%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:12 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 381 expanded)
%              Number of leaves         :   33 ( 142 expanded)
%              Depth                    :   13
%              Number of atoms          :  142 ( 892 expanded)
%              Number of equality atoms :   31 ( 203 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v3_pre_topc > v1_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v3_pre_topc(B,A)
                & v3_tops_1(B,A) )
             => B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_tops_1)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_77,axiom,(
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
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v1_tops_1(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_tops_1)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(A),B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

tff(f_68,axiom,(
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

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_40,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_16,plain,(
    ! [A_12] :
      ( l1_struct_0(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_44,plain,(
    ! [A_27] :
      ( u1_struct_0(A_27) = k2_struct_0(A_27)
      | ~ l1_struct_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_49,plain,(
    ! [A_28] :
      ( u1_struct_0(A_28) = k2_struct_0(A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(resolution,[status(thm)],[c_16,c_44])).

tff(c_53,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_49])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_54,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_38])).

tff(c_59,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(A_29,B_30)
      | ~ m1_subset_1(A_29,k1_zfmisc_1(B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_63,plain,(
    r1_tarski('#skF_2',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_54,c_59])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(k3_subset_1(A_5,B_6),k1_zfmisc_1(A_5))
      | ~ m1_subset_1(B_6,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_184,plain,(
    ! [A_49,B_50] :
      ( k2_pre_topc(A_49,B_50) = k2_struct_0(A_49)
      | ~ v1_tops_1(B_50,A_49)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(u1_struct_0(A_49)))
      | ~ l1_pre_topc(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_195,plain,(
    ! [B_50] :
      ( k2_pre_topc('#skF_1',B_50) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_50,'#skF_1')
      | ~ m1_subset_1(B_50,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_184])).

tff(c_216,plain,(
    ! [B_52] :
      ( k2_pre_topc('#skF_1',B_52) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(B_52,'#skF_1')
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_195])).

tff(c_230,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = k2_struct_0('#skF_1')
    | ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_216])).

tff(c_231,plain,(
    ~ v1_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_230])).

tff(c_107,plain,(
    ! [A_43,B_44] :
      ( k3_subset_1(A_43,k3_subset_1(A_43,B_44)) = B_44
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_116,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_54,c_107])).

tff(c_527,plain,(
    ! [A_79,B_80] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(A_79),B_80),A_79)
      | ~ v3_tops_1(B_80,A_79)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_538,plain,(
    ! [B_80] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_80),'#skF_1')
      | ~ v3_tops_1(B_80,'#skF_1')
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_527])).

tff(c_541,plain,(
    ! [B_81] :
      ( v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_81),'#skF_1')
      | ~ v3_tops_1(B_81,'#skF_1')
      | ~ m1_subset_1(B_81,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_53,c_538])).

tff(c_555,plain,
    ( v1_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_541])).

tff(c_557,plain,
    ( ~ v3_tops_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_231,c_555])).

tff(c_558,plain,(
    ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_557])).

tff(c_561,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_6,c_558])).

tff(c_568,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_561])).

tff(c_570,plain,(
    m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_557])).

tff(c_36,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_660,plain,(
    ! [B_83,A_84] :
      ( v4_pre_topc(B_83,A_84)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(A_84),B_83),A_84)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_84)))
      | ~ l1_pre_topc(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_674,plain,(
    ! [B_83] :
      ( v4_pre_topc(B_83,'#skF_1')
      | ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),B_83),'#skF_1')
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_660])).

tff(c_678,plain,(
    ! [B_85] :
      ( v4_pre_topc(B_85,'#skF_1')
      | ~ v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),B_85),'#skF_1')
      | ~ m1_subset_1(B_85,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_53,c_674])).

tff(c_692,plain,
    ( v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1')
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),k1_zfmisc_1(k2_struct_0('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_678])).

tff(c_695,plain,(
    v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_570,c_36,c_692])).

tff(c_34,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_228,plain,(
    ! [B_6] :
      ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_6)) = k2_struct_0('#skF_1')
      | ~ v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'),B_6),'#skF_1')
      | ~ m1_subset_1(B_6,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_6,c_216])).

tff(c_571,plain,(
    ! [B_82] :
      ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),B_82)) = k2_struct_0('#skF_1')
      | ~ v3_tops_1(B_82,'#skF_1')
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_541,c_228])).

tff(c_582,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_571])).

tff(c_587,plain,(
    k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_582])).

tff(c_168,plain,(
    ! [A_47,B_48] :
      ( k2_pre_topc(A_47,B_48) = B_48
      | ~ v4_pre_topc(B_48,A_47)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(u1_struct_0(A_47)))
      | ~ l1_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_179,plain,(
    ! [B_48] :
      ( k2_pre_topc('#skF_1',B_48) = B_48
      | ~ v4_pre_topc(B_48,'#skF_1')
      | ~ m1_subset_1(B_48,k1_zfmisc_1(k2_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_168])).

tff(c_183,plain,(
    ! [B_48] :
      ( k2_pre_topc('#skF_1',B_48) = B_48
      | ~ v4_pre_topc(B_48,'#skF_1')
      | ~ m1_subset_1(B_48,k1_zfmisc_1(k2_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_179])).

tff(c_621,plain,
    ( k2_pre_topc('#skF_1',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')
    | ~ v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'),'#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_570,c_183])).

tff(c_699,plain,(
    k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') = k2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_695,c_587,c_621])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_70,plain,(
    ! [A_35,B_36] :
      ( k4_xboole_0(A_35,B_36) = k3_subset_1(A_35,B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_78,plain,(
    k4_xboole_0(k2_struct_0('#skF_1'),'#skF_2') = k3_subset_1(k2_struct_0('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_70])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k4_xboole_0(B_2,A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_82,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_2])).

tff(c_85,plain,(
    ~ r1_tarski('#skF_2',k3_subset_1(k2_struct_0('#skF_1'),'#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_82])).

tff(c_709,plain,(
    ~ r1_tarski('#skF_2',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_699,c_85])).

tff(c_713,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_709])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:42:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.37  
% 2.53/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.37  %$ v4_pre_topc > v3_tops_1 > v3_pre_topc > v1_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k4_xboole_0 > k3_subset_1 > k2_pre_topc > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.82/1.37  
% 2.82/1.37  %Foreground sorts:
% 2.82/1.37  
% 2.82/1.37  
% 2.82/1.37  %Background operators:
% 2.82/1.37  
% 2.82/1.37  
% 2.82/1.37  %Foreground operators:
% 2.82/1.37  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.82/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.82/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.82/1.37  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.82/1.37  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 2.82/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.82/1.37  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.82/1.37  tff(v1_tops_1, type, v1_tops_1: ($i * $i) > $o).
% 2.82/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.82/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.82/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.82/1.37  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.82/1.37  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.82/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.37  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.82/1.37  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.82/1.37  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.82/1.37  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.82/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.82/1.37  
% 2.82/1.39  tff(f_109, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tops_1(B, A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_tops_1)).
% 2.82/1.39  tff(f_53, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.82/1.39  tff(f_49, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.82/1.39  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.82/1.39  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.82/1.39  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v1_tops_1(B, A) <=> (k2_pre_topc(A, B) = k2_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tops_1)).
% 2.82/1.39  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.82/1.39  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v1_tops_1(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_tops_1)).
% 2.82/1.39  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> v3_pre_topc(k3_subset_1(u1_struct_0(A), B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_tops_1)).
% 2.82/1.39  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.82/1.39  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.82/1.39  tff(f_29, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 2.82/1.39  tff(c_40, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.82/1.39  tff(c_16, plain, (![A_12]: (l1_struct_0(A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.82/1.39  tff(c_44, plain, (![A_27]: (u1_struct_0(A_27)=k2_struct_0(A_27) | ~l1_struct_0(A_27))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.82/1.39  tff(c_49, plain, (![A_28]: (u1_struct_0(A_28)=k2_struct_0(A_28) | ~l1_pre_topc(A_28))), inference(resolution, [status(thm)], [c_16, c_44])).
% 2.82/1.39  tff(c_53, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_49])).
% 2.82/1.39  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.82/1.39  tff(c_54, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_38])).
% 2.82/1.39  tff(c_59, plain, (![A_29, B_30]: (r1_tarski(A_29, B_30) | ~m1_subset_1(A_29, k1_zfmisc_1(B_30)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.82/1.39  tff(c_63, plain, (r1_tarski('#skF_2', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_54, c_59])).
% 2.82/1.39  tff(c_6, plain, (![A_5, B_6]: (m1_subset_1(k3_subset_1(A_5, B_6), k1_zfmisc_1(A_5)) | ~m1_subset_1(B_6, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.82/1.39  tff(c_184, plain, (![A_49, B_50]: (k2_pre_topc(A_49, B_50)=k2_struct_0(A_49) | ~v1_tops_1(B_50, A_49) | ~m1_subset_1(B_50, k1_zfmisc_1(u1_struct_0(A_49))) | ~l1_pre_topc(A_49))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.82/1.39  tff(c_195, plain, (![B_50]: (k2_pre_topc('#skF_1', B_50)=k2_struct_0('#skF_1') | ~v1_tops_1(B_50, '#skF_1') | ~m1_subset_1(B_50, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_53, c_184])).
% 2.82/1.39  tff(c_216, plain, (![B_52]: (k2_pre_topc('#skF_1', B_52)=k2_struct_0('#skF_1') | ~v1_tops_1(B_52, '#skF_1') | ~m1_subset_1(B_52, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_195])).
% 2.82/1.39  tff(c_230, plain, (k2_pre_topc('#skF_1', '#skF_2')=k2_struct_0('#skF_1') | ~v1_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_54, c_216])).
% 2.82/1.39  tff(c_231, plain, (~v1_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_230])).
% 2.82/1.39  tff(c_107, plain, (![A_43, B_44]: (k3_subset_1(A_43, k3_subset_1(A_43, B_44))=B_44 | ~m1_subset_1(B_44, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.82/1.39  tff(c_116, plain, (k3_subset_1(k2_struct_0('#skF_1'), k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_54, c_107])).
% 2.82/1.39  tff(c_527, plain, (![A_79, B_80]: (v1_tops_1(k3_subset_1(u1_struct_0(A_79), B_80), A_79) | ~v3_tops_1(B_80, A_79) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.82/1.39  tff(c_538, plain, (![B_80]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_80), '#skF_1') | ~v3_tops_1(B_80, '#skF_1') | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_53, c_527])).
% 2.82/1.39  tff(c_541, plain, (![B_81]: (v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_81), '#skF_1') | ~v3_tops_1(B_81, '#skF_1') | ~m1_subset_1(B_81, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_53, c_538])).
% 2.82/1.39  tff(c_555, plain, (v1_tops_1('#skF_2', '#skF_1') | ~v3_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_116, c_541])).
% 2.82/1.39  tff(c_557, plain, (~v3_tops_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_231, c_555])).
% 2.82/1.39  tff(c_558, plain, (~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_557])).
% 2.82/1.39  tff(c_561, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_558])).
% 2.82/1.39  tff(c_568, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_561])).
% 2.82/1.39  tff(c_570, plain, (m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_557])).
% 2.82/1.39  tff(c_36, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.82/1.39  tff(c_660, plain, (![B_83, A_84]: (v4_pre_topc(B_83, A_84) | ~v3_pre_topc(k3_subset_1(u1_struct_0(A_84), B_83), A_84) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_84))) | ~l1_pre_topc(A_84))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.82/1.39  tff(c_674, plain, (![B_83]: (v4_pre_topc(B_83, '#skF_1') | ~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), B_83), '#skF_1') | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_53, c_660])).
% 2.82/1.39  tff(c_678, plain, (![B_85]: (v4_pre_topc(B_85, '#skF_1') | ~v3_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), B_85), '#skF_1') | ~m1_subset_1(B_85, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_53, c_674])).
% 2.82/1.39  tff(c_692, plain, (v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1') | ~v3_pre_topc('#skF_2', '#skF_1') | ~m1_subset_1(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), k1_zfmisc_1(k2_struct_0('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_116, c_678])).
% 2.82/1.39  tff(c_695, plain, (v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_570, c_36, c_692])).
% 2.82/1.39  tff(c_34, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.82/1.39  tff(c_228, plain, (![B_6]: (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_6))=k2_struct_0('#skF_1') | ~v1_tops_1(k3_subset_1(k2_struct_0('#skF_1'), B_6), '#skF_1') | ~m1_subset_1(B_6, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_6, c_216])).
% 2.82/1.39  tff(c_571, plain, (![B_82]: (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), B_82))=k2_struct_0('#skF_1') | ~v3_tops_1(B_82, '#skF_1') | ~m1_subset_1(B_82, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(resolution, [status(thm)], [c_541, c_228])).
% 2.82/1.39  tff(c_582, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1') | ~v3_tops_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_54, c_571])).
% 2.82/1.39  tff(c_587, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_582])).
% 2.82/1.39  tff(c_168, plain, (![A_47, B_48]: (k2_pre_topc(A_47, B_48)=B_48 | ~v4_pre_topc(B_48, A_47) | ~m1_subset_1(B_48, k1_zfmisc_1(u1_struct_0(A_47))) | ~l1_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.82/1.39  tff(c_179, plain, (![B_48]: (k2_pre_topc('#skF_1', B_48)=B_48 | ~v4_pre_topc(B_48, '#skF_1') | ~m1_subset_1(B_48, k1_zfmisc_1(k2_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_53, c_168])).
% 2.82/1.39  tff(c_183, plain, (![B_48]: (k2_pre_topc('#skF_1', B_48)=B_48 | ~v4_pre_topc(B_48, '#skF_1') | ~m1_subset_1(B_48, k1_zfmisc_1(k2_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_179])).
% 2.82/1.39  tff(c_621, plain, (k2_pre_topc('#skF_1', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2') | ~v4_pre_topc(k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_570, c_183])).
% 2.82/1.39  tff(c_699, plain, (k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')=k2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_695, c_587, c_621])).
% 2.82/1.39  tff(c_32, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.82/1.39  tff(c_70, plain, (![A_35, B_36]: (k4_xboole_0(A_35, B_36)=k3_subset_1(A_35, B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.82/1.39  tff(c_78, plain, (k4_xboole_0(k2_struct_0('#skF_1'), '#skF_2')=k3_subset_1(k2_struct_0('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_54, c_70])).
% 2.82/1.39  tff(c_2, plain, (![A_1, B_2]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k4_xboole_0(B_2, A_1)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.82/1.39  tff(c_82, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_2])).
% 2.82/1.39  tff(c_85, plain, (~r1_tarski('#skF_2', k3_subset_1(k2_struct_0('#skF_1'), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_32, c_82])).
% 2.82/1.39  tff(c_709, plain, (~r1_tarski('#skF_2', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_699, c_85])).
% 2.82/1.39  tff(c_713, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_709])).
% 2.82/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.39  
% 2.82/1.39  Inference rules
% 2.82/1.39  ----------------------
% 2.82/1.39  #Ref     : 0
% 2.82/1.39  #Sup     : 144
% 2.82/1.39  #Fact    : 0
% 2.82/1.39  #Define  : 0
% 2.82/1.39  #Split   : 4
% 2.82/1.39  #Chain   : 0
% 2.82/1.39  #Close   : 0
% 2.82/1.39  
% 2.82/1.39  Ordering : KBO
% 2.82/1.39  
% 2.82/1.39  Simplification rules
% 2.82/1.39  ----------------------
% 2.82/1.39  #Subsume      : 13
% 2.82/1.39  #Demod        : 64
% 2.82/1.39  #Tautology    : 49
% 2.82/1.39  #SimpNegUnit  : 8
% 2.82/1.39  #BackRed      : 12
% 2.82/1.39  
% 2.82/1.39  #Partial instantiations: 0
% 2.82/1.39  #Strategies tried      : 1
% 2.82/1.39  
% 2.82/1.39  Timing (in seconds)
% 2.82/1.39  ----------------------
% 2.82/1.39  Preprocessing        : 0.30
% 2.82/1.39  Parsing              : 0.16
% 2.82/1.39  CNF conversion       : 0.02
% 2.82/1.39  Main loop            : 0.32
% 2.82/1.39  Inferencing          : 0.12
% 2.82/1.39  Reduction            : 0.09
% 2.82/1.39  Demodulation         : 0.07
% 2.82/1.39  BG Simplification    : 0.02
% 2.82/1.39  Subsumption          : 0.06
% 2.82/1.39  Abstraction          : 0.02
% 2.82/1.39  MUC search           : 0.00
% 2.82/1.39  Cooper               : 0.00
% 2.82/1.39  Total                : 0.66
% 2.82/1.39  Index Insertion      : 0.00
% 2.82/1.39  Index Deletion       : 0.00
% 2.82/1.39  Index Matching       : 0.00
% 2.82/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
