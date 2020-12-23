%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:02 EST 2020

% Result     : Theorem 3.51s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 152 expanded)
%              Number of leaves         :   32 (  68 expanded)
%              Depth                    :    8
%              Number of atoms          :  131 ( 351 expanded)
%              Number of equality atoms :   35 (  85 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => ( v3_tops_1(B,A)
              <=> B = k2_tops_1(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_tops_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_58,axiom,(
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

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
          <=> v2_tops_1(k2_pre_topc(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_46,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_96,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_40,plain,
    ( k2_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_102,plain,(
    ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_40])).

tff(c_38,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_633,plain,(
    ! [B_68,A_69] :
      ( v2_tops_1(B_68,A_69)
      | ~ r1_tarski(B_68,k2_tops_1(A_69,B_68))
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_69)))
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_635,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_633])).

tff(c_637,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_8,c_635])).

tff(c_34,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_439,plain,(
    ! [A_60,B_61] :
      ( k2_pre_topc(A_60,B_61) = B_61
      | ~ v4_pre_topc(B_61,A_60)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_60)))
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_442,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_439])).

tff(c_445,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_442])).

tff(c_638,plain,(
    ! [B_70,A_71] :
      ( v3_tops_1(B_70,A_71)
      | ~ v2_tops_1(k2_pre_topc(A_71,B_70),A_71)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_640,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_445,c_638])).

tff(c_642,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_637,c_640])).

tff(c_644,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_102,c_642])).

tff(c_646,plain,(
    k2_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_645,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_806,plain,(
    ! [B_87,A_88] :
      ( v2_tops_1(B_87,A_88)
      | ~ v3_tops_1(B_87,A_88)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(u1_struct_0(A_88)))
      | ~ l1_pre_topc(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_809,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_806])).

tff(c_812,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_645,c_809])).

tff(c_1170,plain,(
    ! [B_101,A_102] :
      ( r1_tarski(B_101,k2_tops_1(A_102,B_101))
      | ~ v2_tops_1(B_101,A_102)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(u1_struct_0(A_102)))
      | ~ l1_pre_topc(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1172,plain,
    ( r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_1170])).

tff(c_1175,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_812,c_1172])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1184,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1175,c_10])).

tff(c_671,plain,(
    ! [A_76,B_77,C_78] :
      ( k7_subset_1(A_76,B_77,C_78) = k4_xboole_0(B_77,C_78)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_674,plain,(
    ! [C_78] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_78) = k4_xboole_0('#skF_2',C_78) ),
    inference(resolution,[status(thm)],[c_36,c_671])).

tff(c_1004,plain,(
    ! [A_95,B_96] :
      ( k2_pre_topc(A_95,B_96) = B_96
      | ~ v4_pre_topc(B_96,A_95)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1007,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_1004])).

tff(c_1010,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_1007])).

tff(c_1494,plain,(
    ! [A_115,B_116] :
      ( k7_subset_1(u1_struct_0(A_115),k2_pre_topc(A_115,B_116),k1_tops_1(A_115,B_116)) = k2_tops_1(A_115,B_116)
      | ~ m1_subset_1(B_116,k1_zfmisc_1(u1_struct_0(A_115)))
      | ~ l1_pre_topc(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1503,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1010,c_1494])).

tff(c_1507,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_674,c_1503])).

tff(c_756,plain,(
    ! [A_85,B_86] :
      ( r1_tarski(k1_tops_1(A_85,B_86),B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_758,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_756])).

tff(c_761,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_758])).

tff(c_768,plain,(
    k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_761,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_649,plain,(
    ! [A_72,B_73] : k4_xboole_0(A_72,k4_xboole_0(A_72,B_73)) = k3_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_684,plain,(
    ! [A_80,B_81] : k4_xboole_0(A_80,k3_xboole_0(A_80,B_81)) = k3_xboole_0(A_80,k4_xboole_0(A_80,B_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_649])).

tff(c_699,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k3_xboole_0(A_1,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_684])).

tff(c_772,plain,(
    k3_xboole_0('#skF_2',k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2'))) = k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_768,c_699])).

tff(c_1508,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1507,c_1507,c_772])).

tff(c_1509,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1184,c_1508])).

tff(c_1511,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_646,c_1509])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:32:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.51/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.51/1.62  
% 3.51/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.51/1.62  %$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.51/1.62  
% 3.51/1.62  %Foreground sorts:
% 3.51/1.62  
% 3.51/1.62  
% 3.51/1.62  %Background operators:
% 3.51/1.62  
% 3.51/1.62  
% 3.51/1.62  %Foreground operators:
% 3.51/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.51/1.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.51/1.62  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.51/1.62  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.51/1.62  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.51/1.62  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 3.51/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.51/1.62  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.51/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.51/1.62  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.51/1.62  tff('#skF_1', type, '#skF_1': $i).
% 3.51/1.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.51/1.62  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.51/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.51/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.51/1.62  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.51/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.51/1.62  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.51/1.62  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.51/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.51/1.62  
% 3.85/1.64  tff(f_111, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => (v3_tops_1(B, A) <=> (B = k2_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_tops_1)).
% 3.85/1.64  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.85/1.64  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tops_1)).
% 3.85/1.64  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.85/1.64  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) <=> v2_tops_1(k2_pre_topc(A, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tops_1)).
% 3.85/1.64  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_tops_1)).
% 3.85/1.64  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.85/1.64  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.85/1.64  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 3.85/1.64  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 3.85/1.64  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.85/1.64  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.85/1.64  tff(c_46, plain, (v3_tops_1('#skF_2', '#skF_1') | k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.85/1.64  tff(c_96, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(splitLeft, [status(thm)], [c_46])).
% 3.85/1.64  tff(c_40, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.85/1.64  tff(c_102, plain, (~v3_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_40])).
% 3.85/1.64  tff(c_38, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.85/1.64  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.85/1.64  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.85/1.64  tff(c_633, plain, (![B_68, A_69]: (v2_tops_1(B_68, A_69) | ~r1_tarski(B_68, k2_tops_1(A_69, B_68)) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_69))) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.85/1.64  tff(c_635, plain, (v2_tops_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_2', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_96, c_633])).
% 3.85/1.64  tff(c_637, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_8, c_635])).
% 3.85/1.64  tff(c_34, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.85/1.64  tff(c_439, plain, (![A_60, B_61]: (k2_pre_topc(A_60, B_61)=B_61 | ~v4_pre_topc(B_61, A_60) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_60))) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.85/1.64  tff(c_442, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_439])).
% 3.85/1.64  tff(c_445, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_442])).
% 3.85/1.64  tff(c_638, plain, (![B_70, A_71]: (v3_tops_1(B_70, A_71) | ~v2_tops_1(k2_pre_topc(A_71, B_70), A_71) | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.85/1.64  tff(c_640, plain, (v3_tops_1('#skF_2', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_445, c_638])).
% 3.85/1.64  tff(c_642, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_637, c_640])).
% 3.85/1.64  tff(c_644, plain, $false, inference(negUnitSimplification, [status(thm)], [c_102, c_642])).
% 3.85/1.64  tff(c_646, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(splitRight, [status(thm)], [c_46])).
% 3.85/1.64  tff(c_645, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 3.85/1.64  tff(c_806, plain, (![B_87, A_88]: (v2_tops_1(B_87, A_88) | ~v3_tops_1(B_87, A_88) | ~m1_subset_1(B_87, k1_zfmisc_1(u1_struct_0(A_88))) | ~l1_pre_topc(A_88))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.85/1.64  tff(c_809, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_806])).
% 3.85/1.64  tff(c_812, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_645, c_809])).
% 3.85/1.64  tff(c_1170, plain, (![B_101, A_102]: (r1_tarski(B_101, k2_tops_1(A_102, B_101)) | ~v2_tops_1(B_101, A_102) | ~m1_subset_1(B_101, k1_zfmisc_1(u1_struct_0(A_102))) | ~l1_pre_topc(A_102))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.85/1.64  tff(c_1172, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_1170])).
% 3.85/1.64  tff(c_1175, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_812, c_1172])).
% 3.85/1.64  tff(c_10, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.85/1.64  tff(c_1184, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_1175, c_10])).
% 3.85/1.64  tff(c_671, plain, (![A_76, B_77, C_78]: (k7_subset_1(A_76, B_77, C_78)=k4_xboole_0(B_77, C_78) | ~m1_subset_1(B_77, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.85/1.64  tff(c_674, plain, (![C_78]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_78)=k4_xboole_0('#skF_2', C_78))), inference(resolution, [status(thm)], [c_36, c_671])).
% 3.85/1.64  tff(c_1004, plain, (![A_95, B_96]: (k2_pre_topc(A_95, B_96)=B_96 | ~v4_pre_topc(B_96, A_95) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.85/1.64  tff(c_1007, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_1004])).
% 3.85/1.64  tff(c_1010, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_1007])).
% 3.85/1.64  tff(c_1494, plain, (![A_115, B_116]: (k7_subset_1(u1_struct_0(A_115), k2_pre_topc(A_115, B_116), k1_tops_1(A_115, B_116))=k2_tops_1(A_115, B_116) | ~m1_subset_1(B_116, k1_zfmisc_1(u1_struct_0(A_115))) | ~l1_pre_topc(A_115))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.85/1.64  tff(c_1503, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1010, c_1494])).
% 3.85/1.64  tff(c_1507, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_674, c_1503])).
% 3.85/1.64  tff(c_756, plain, (![A_85, B_86]: (r1_tarski(k1_tops_1(A_85, B_86), B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.85/1.64  tff(c_758, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_756])).
% 3.85/1.64  tff(c_761, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_758])).
% 3.85/1.64  tff(c_768, plain, (k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_761, c_10])).
% 3.85/1.64  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.85/1.64  tff(c_12, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.85/1.64  tff(c_649, plain, (![A_72, B_73]: (k4_xboole_0(A_72, k4_xboole_0(A_72, B_73))=k3_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.85/1.64  tff(c_684, plain, (![A_80, B_81]: (k4_xboole_0(A_80, k3_xboole_0(A_80, B_81))=k3_xboole_0(A_80, k4_xboole_0(A_80, B_81)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_649])).
% 3.85/1.64  tff(c_699, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k3_xboole_0(A_1, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_684])).
% 3.85/1.64  tff(c_772, plain, (k3_xboole_0('#skF_2', k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2')))=k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_768, c_699])).
% 3.85/1.64  tff(c_1508, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1507, c_1507, c_772])).
% 3.85/1.64  tff(c_1509, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1184, c_1508])).
% 3.85/1.64  tff(c_1511, plain, $false, inference(negUnitSimplification, [status(thm)], [c_646, c_1509])).
% 3.85/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/1.64  
% 3.85/1.64  Inference rules
% 3.85/1.64  ----------------------
% 3.85/1.64  #Ref     : 0
% 3.85/1.64  #Sup     : 372
% 3.85/1.64  #Fact    : 0
% 3.85/1.64  #Define  : 0
% 3.85/1.64  #Split   : 3
% 3.85/1.64  #Chain   : 0
% 3.85/1.64  #Close   : 0
% 3.85/1.64  
% 3.85/1.64  Ordering : KBO
% 3.85/1.64  
% 3.85/1.64  Simplification rules
% 3.85/1.64  ----------------------
% 3.85/1.64  #Subsume      : 11
% 3.85/1.64  #Demod        : 450
% 3.85/1.64  #Tautology    : 240
% 3.85/1.64  #SimpNegUnit  : 3
% 3.85/1.64  #BackRed      : 1
% 3.85/1.64  
% 3.85/1.64  #Partial instantiations: 0
% 3.85/1.64  #Strategies tried      : 1
% 3.85/1.64  
% 3.85/1.64  Timing (in seconds)
% 3.85/1.64  ----------------------
% 3.85/1.64  Preprocessing        : 0.32
% 3.85/1.64  Parsing              : 0.17
% 3.85/1.64  CNF conversion       : 0.02
% 3.85/1.64  Main loop            : 0.54
% 3.85/1.64  Inferencing          : 0.17
% 3.85/1.64  Reduction            : 0.25
% 3.85/1.64  Demodulation         : 0.22
% 3.85/1.64  BG Simplification    : 0.02
% 3.85/1.64  Subsumption          : 0.07
% 3.85/1.64  Abstraction          : 0.03
% 3.85/1.64  MUC search           : 0.00
% 3.85/1.64  Cooper               : 0.00
% 3.85/1.64  Total                : 0.89
% 3.85/1.64  Index Insertion      : 0.00
% 3.85/1.64  Index Deletion       : 0.00
% 3.85/1.64  Index Matching       : 0.00
% 3.85/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
