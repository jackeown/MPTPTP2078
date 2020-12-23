%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:05 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 178 expanded)
%              Number of leaves         :   32 (  77 expanded)
%              Depth                    :   10
%              Number of atoms          :  149 ( 426 expanded)
%              Number of equality atoms :   29 (  84 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_121,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => ( v3_tops_1(B,A)
              <=> B = k2_tops_1(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_tops_1)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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

tff(f_77,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
          <=> v2_tops_1(k2_pre_topc(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_84,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_888,plain,(
    ! [A_142,B_143] :
      ( r1_tarski(k1_tops_1(A_142,B_143),B_143)
      | ~ m1_subset_1(B_143,k1_zfmisc_1(u1_struct_0(A_142)))
      | ~ l1_pre_topc(A_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_896,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_888])).

tff(c_901,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_896])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_44,plain,
    ( k2_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_53,plain,(
    ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_38,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_444,plain,(
    ! [A_82,B_83] :
      ( k2_pre_topc(A_82,B_83) = B_83
      | ~ v4_pre_topc(B_83,A_82)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_455,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_444])).

tff(c_460,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_455])).

tff(c_580,plain,(
    ! [B_92,A_93] :
      ( v3_tops_1(B_92,A_93)
      | ~ v2_tops_1(k2_pre_topc(A_93,B_92),A_93)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_582,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_460,c_580])).

tff(c_584,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_582])).

tff(c_585,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_584])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_55,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_50])).

tff(c_660,plain,(
    ! [B_106,A_107] :
      ( v2_tops_1(B_106,A_107)
      | ~ r1_tarski(B_106,k2_tops_1(A_107,B_106))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0(A_107)))
      | ~ l1_pre_topc(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_662,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_660])).

tff(c_664,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_6,c_662])).

tff(c_666,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_585,c_664])).

tff(c_667,plain,(
    k2_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_668,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_949,plain,(
    ! [B_145,A_146] :
      ( v2_tops_1(B_145,A_146)
      | ~ v3_tops_1(B_145,A_146)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ l1_pre_topc(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_960,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_949])).

tff(c_965,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_668,c_960])).

tff(c_1373,plain,(
    ! [B_187,A_188] :
      ( r1_tarski(B_187,k2_tops_1(A_188,B_187))
      | ~ v2_tops_1(B_187,A_188)
      | ~ m1_subset_1(B_187,k1_zfmisc_1(u1_struct_0(A_188)))
      | ~ l1_pre_topc(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1381,plain,
    ( r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1373])).

tff(c_1386,plain,(
    r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_965,c_1381])).

tff(c_706,plain,(
    ! [A_118,B_119] :
      ( k4_xboole_0(A_118,B_119) = k3_subset_1(A_118,B_119)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(A_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_713,plain,(
    ! [B_14,A_13] :
      ( k4_xboole_0(B_14,A_13) = k3_subset_1(B_14,A_13)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(resolution,[status(thm)],[c_18,c_706])).

tff(c_917,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_901,c_713])).

tff(c_787,plain,(
    ! [A_130,B_131,C_132] :
      ( k7_subset_1(A_130,B_131,C_132) = k4_xboole_0(B_131,C_132)
      | ~ m1_subset_1(B_131,k1_zfmisc_1(A_130)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_796,plain,(
    ! [C_132] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_132) = k4_xboole_0('#skF_2',C_132) ),
    inference(resolution,[status(thm)],[c_40,c_787])).

tff(c_1020,plain,(
    ! [A_151,B_152] :
      ( k2_pre_topc(A_151,B_152) = B_152
      | ~ v4_pre_topc(B_152,A_151)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ l1_pre_topc(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1031,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1020])).

tff(c_1036,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_1031])).

tff(c_1827,plain,(
    ! [A_209,B_210] :
      ( k7_subset_1(u1_struct_0(A_209),k2_pre_topc(A_209,B_210),k1_tops_1(A_209,B_210)) = k2_tops_1(A_209,B_210)
      | ~ m1_subset_1(B_210,k1_zfmisc_1(u1_struct_0(A_209)))
      | ~ l1_pre_topc(A_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1840,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1036,c_1827])).

tff(c_1850,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_917,c_796,c_1840])).

tff(c_753,plain,(
    ! [A_124,B_125] :
      ( m1_subset_1(k3_subset_1(A_124,B_125),k1_zfmisc_1(A_124))
      | ~ m1_subset_1(B_125,k1_zfmisc_1(A_124)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_762,plain,(
    ! [A_126,B_127] :
      ( r1_tarski(k3_subset_1(A_126,B_127),A_126)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(A_126)) ) ),
    inference(resolution,[status(thm)],[c_753,c_16])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_772,plain,(
    ! [A_126,B_127] :
      ( k3_subset_1(A_126,B_127) = A_126
      | ~ r1_tarski(A_126,k3_subset_1(A_126,B_127))
      | ~ m1_subset_1(B_127,k1_zfmisc_1(A_126)) ) ),
    inference(resolution,[status(thm)],[c_762,c_2])).

tff(c_1863,plain,
    ( k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1850,c_772])).

tff(c_1883,plain,
    ( k2_tops_1('#skF_1','#skF_2') = '#skF_2'
    | ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1386,c_1850,c_1863])).

tff(c_1884,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_667,c_1883])).

tff(c_1891,plain,(
    ~ r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_1884])).

tff(c_1895,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_901,c_1891])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:46:40 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.61  
% 3.53/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.53/1.61  %$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_subset_1 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.53/1.61  
% 3.53/1.61  %Foreground sorts:
% 3.53/1.61  
% 3.53/1.61  
% 3.53/1.61  %Background operators:
% 3.53/1.61  
% 3.53/1.61  
% 3.53/1.61  %Foreground operators:
% 3.53/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.53/1.61  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.53/1.61  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 3.53/1.61  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.53/1.61  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 3.53/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.53/1.61  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.53/1.61  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.53/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.53/1.61  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.53/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.53/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.53/1.61  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.53/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.61  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.53/1.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.53/1.61  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.53/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.53/1.61  
% 3.87/1.63  tff(f_121, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => (v3_tops_1(B, A) <=> (B = k2_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_tops_1)).
% 3.87/1.63  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_tops_1)).
% 3.87/1.63  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.87/1.63  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 3.87/1.63  tff(f_77, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) <=> v2_tops_1(k2_pre_topc(A, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tops_1)).
% 3.87/1.63  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.87/1.63  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tops_1)).
% 3.87/1.63  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_tops_1)).
% 3.87/1.63  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.87/1.63  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.87/1.63  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 3.87/1.63  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.87/1.63  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.87/1.63  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.87/1.63  tff(c_888, plain, (![A_142, B_143]: (r1_tarski(k1_tops_1(A_142, B_143), B_143) | ~m1_subset_1(B_143, k1_zfmisc_1(u1_struct_0(A_142))) | ~l1_pre_topc(A_142))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.87/1.63  tff(c_896, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_888])).
% 3.87/1.63  tff(c_901, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_896])).
% 3.87/1.63  tff(c_18, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.87/1.63  tff(c_44, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.87/1.63  tff(c_53, plain, (~v3_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_44])).
% 3.87/1.63  tff(c_38, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.87/1.63  tff(c_444, plain, (![A_82, B_83]: (k2_pre_topc(A_82, B_83)=B_83 | ~v4_pre_topc(B_83, A_82) | ~m1_subset_1(B_83, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.87/1.63  tff(c_455, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_444])).
% 3.87/1.63  tff(c_460, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_455])).
% 3.87/1.63  tff(c_580, plain, (![B_92, A_93]: (v3_tops_1(B_92, A_93) | ~v2_tops_1(k2_pre_topc(A_93, B_92), A_93) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.87/1.63  tff(c_582, plain, (v3_tops_1('#skF_2', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_460, c_580])).
% 3.87/1.63  tff(c_584, plain, (v3_tops_1('#skF_2', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_582])).
% 3.87/1.63  tff(c_585, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_53, c_584])).
% 3.87/1.63  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.87/1.63  tff(c_50, plain, (v3_tops_1('#skF_2', '#skF_1') | k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.87/1.63  tff(c_55, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_53, c_50])).
% 3.87/1.63  tff(c_660, plain, (![B_106, A_107]: (v2_tops_1(B_106, A_107) | ~r1_tarski(B_106, k2_tops_1(A_107, B_106)) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0(A_107))) | ~l1_pre_topc(A_107))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.87/1.63  tff(c_662, plain, (v2_tops_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_2', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_55, c_660])).
% 3.87/1.63  tff(c_664, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_6, c_662])).
% 3.87/1.63  tff(c_666, plain, $false, inference(negUnitSimplification, [status(thm)], [c_585, c_664])).
% 3.87/1.63  tff(c_667, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(splitRight, [status(thm)], [c_44])).
% 3.87/1.63  tff(c_668, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_44])).
% 3.87/1.63  tff(c_949, plain, (![B_145, A_146]: (v2_tops_1(B_145, A_146) | ~v3_tops_1(B_145, A_146) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_146))) | ~l1_pre_topc(A_146))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.87/1.63  tff(c_960, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_949])).
% 3.87/1.63  tff(c_965, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_668, c_960])).
% 3.87/1.63  tff(c_1373, plain, (![B_187, A_188]: (r1_tarski(B_187, k2_tops_1(A_188, B_187)) | ~v2_tops_1(B_187, A_188) | ~m1_subset_1(B_187, k1_zfmisc_1(u1_struct_0(A_188))) | ~l1_pre_topc(A_188))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.87/1.63  tff(c_1381, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1373])).
% 3.87/1.63  tff(c_1386, plain, (r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_965, c_1381])).
% 3.87/1.63  tff(c_706, plain, (![A_118, B_119]: (k4_xboole_0(A_118, B_119)=k3_subset_1(A_118, B_119) | ~m1_subset_1(B_119, k1_zfmisc_1(A_118)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.87/1.63  tff(c_713, plain, (![B_14, A_13]: (k4_xboole_0(B_14, A_13)=k3_subset_1(B_14, A_13) | ~r1_tarski(A_13, B_14))), inference(resolution, [status(thm)], [c_18, c_706])).
% 3.87/1.63  tff(c_917, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_901, c_713])).
% 3.87/1.63  tff(c_787, plain, (![A_130, B_131, C_132]: (k7_subset_1(A_130, B_131, C_132)=k4_xboole_0(B_131, C_132) | ~m1_subset_1(B_131, k1_zfmisc_1(A_130)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.87/1.63  tff(c_796, plain, (![C_132]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_132)=k4_xboole_0('#skF_2', C_132))), inference(resolution, [status(thm)], [c_40, c_787])).
% 3.87/1.63  tff(c_1020, plain, (![A_151, B_152]: (k2_pre_topc(A_151, B_152)=B_152 | ~v4_pre_topc(B_152, A_151) | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0(A_151))) | ~l1_pre_topc(A_151))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.87/1.63  tff(c_1031, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1020])).
% 3.87/1.63  tff(c_1036, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_1031])).
% 3.87/1.63  tff(c_1827, plain, (![A_209, B_210]: (k7_subset_1(u1_struct_0(A_209), k2_pre_topc(A_209, B_210), k1_tops_1(A_209, B_210))=k2_tops_1(A_209, B_210) | ~m1_subset_1(B_210, k1_zfmisc_1(u1_struct_0(A_209))) | ~l1_pre_topc(A_209))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.87/1.63  tff(c_1840, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1036, c_1827])).
% 3.87/1.63  tff(c_1850, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_917, c_796, c_1840])).
% 3.87/1.63  tff(c_753, plain, (![A_124, B_125]: (m1_subset_1(k3_subset_1(A_124, B_125), k1_zfmisc_1(A_124)) | ~m1_subset_1(B_125, k1_zfmisc_1(A_124)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.87/1.63  tff(c_16, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.87/1.63  tff(c_762, plain, (![A_126, B_127]: (r1_tarski(k3_subset_1(A_126, B_127), A_126) | ~m1_subset_1(B_127, k1_zfmisc_1(A_126)))), inference(resolution, [status(thm)], [c_753, c_16])).
% 3.87/1.63  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.87/1.63  tff(c_772, plain, (![A_126, B_127]: (k3_subset_1(A_126, B_127)=A_126 | ~r1_tarski(A_126, k3_subset_1(A_126, B_127)) | ~m1_subset_1(B_127, k1_zfmisc_1(A_126)))), inference(resolution, [status(thm)], [c_762, c_2])).
% 3.87/1.63  tff(c_1863, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))='#skF_2' | ~r1_tarski('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1850, c_772])).
% 3.87/1.63  tff(c_1883, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2' | ~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1386, c_1850, c_1863])).
% 3.87/1.63  tff(c_1884, plain, (~m1_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_667, c_1883])).
% 3.87/1.63  tff(c_1891, plain, (~r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_18, c_1884])).
% 3.87/1.63  tff(c_1895, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_901, c_1891])).
% 3.87/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/1.63  
% 3.87/1.63  Inference rules
% 3.87/1.63  ----------------------
% 3.87/1.63  #Ref     : 0
% 3.87/1.63  #Sup     : 423
% 3.87/1.63  #Fact    : 0
% 3.87/1.63  #Define  : 0
% 3.87/1.63  #Split   : 12
% 3.87/1.63  #Chain   : 0
% 3.87/1.63  #Close   : 0
% 3.87/1.63  
% 3.87/1.63  Ordering : KBO
% 3.87/1.63  
% 3.87/1.63  Simplification rules
% 3.87/1.63  ----------------------
% 3.87/1.63  #Subsume      : 74
% 3.87/1.63  #Demod        : 146
% 3.87/1.63  #Tautology    : 132
% 3.87/1.63  #SimpNegUnit  : 7
% 3.87/1.63  #BackRed      : 1
% 3.87/1.63  
% 3.87/1.63  #Partial instantiations: 0
% 3.87/1.63  #Strategies tried      : 1
% 3.87/1.63  
% 3.87/1.63  Timing (in seconds)
% 3.87/1.63  ----------------------
% 3.87/1.63  Preprocessing        : 0.32
% 3.87/1.63  Parsing              : 0.17
% 3.87/1.63  CNF conversion       : 0.02
% 3.87/1.63  Main loop            : 0.54
% 3.87/1.63  Inferencing          : 0.19
% 3.87/1.63  Reduction            : 0.16
% 3.87/1.63  Demodulation         : 0.11
% 3.87/1.63  BG Simplification    : 0.03
% 3.87/1.63  Subsumption          : 0.12
% 3.87/1.63  Abstraction          : 0.03
% 3.87/1.63  MUC search           : 0.00
% 3.87/1.63  Cooper               : 0.00
% 3.87/1.63  Total                : 0.90
% 3.87/1.63  Index Insertion      : 0.00
% 3.87/1.63  Index Deletion       : 0.00
% 3.87/1.63  Index Matching       : 0.00
% 3.87/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
