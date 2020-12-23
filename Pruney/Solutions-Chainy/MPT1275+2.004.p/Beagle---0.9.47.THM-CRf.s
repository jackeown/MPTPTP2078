%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:02 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 139 expanded)
%              Number of leaves         :   39 (  65 expanded)
%              Depth                    :    8
%              Number of atoms          :  137 ( 293 expanded)
%              Number of equality atoms :   42 (  75 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_121,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => ( v3_tops_1(B,A)
              <=> B = k2_tops_1(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).

tff(f_80,axiom,(
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

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v2_tops_1(B,A)
              & v4_pre_topc(B,A) )
           => v3_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_tops_1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_49,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_39,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_98,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_52,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_121,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_46,plain,
    ( k2_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_127,plain,(
    ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_46])).

tff(c_44,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_499,plain,(
    ! [A_75,B_76] :
      ( k1_tops_1(A_75,B_76) = k1_xboole_0
      | ~ v2_tops_1(B_76,A_75)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_502,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_499])).

tff(c_505,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_502])).

tff(c_506,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_505])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_522,plain,(
    ! [B_81,A_82] :
      ( v2_tops_1(B_81,A_82)
      | ~ r1_tarski(B_81,k2_tops_1(A_82,B_81))
      | ~ m1_subset_1(B_81,k1_zfmisc_1(u1_struct_0(A_82)))
      | ~ l1_pre_topc(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_527,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_522])).

tff(c_530,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_6,c_527])).

tff(c_532,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_506,c_530])).

tff(c_534,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_505])).

tff(c_40,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_580,plain,(
    ! [B_94,A_95] :
      ( v3_tops_1(B_94,A_95)
      | ~ v4_pre_topc(B_94,A_95)
      | ~ v2_tops_1(B_94,A_95)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_pre_topc(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_583,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_580])).

tff(c_586,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_534,c_40,c_583])).

tff(c_588,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_586])).

tff(c_590,plain,(
    k2_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_14,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [B_10,A_9] : k2_tarski(B_10,A_9) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_593,plain,(
    ! [A_96,B_97] : k1_setfam_1(k2_tarski(A_96,B_97)) = k3_xboole_0(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_608,plain,(
    ! [B_98,A_99] : k1_setfam_1(k2_tarski(B_98,A_99)) = k3_xboole_0(A_99,B_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_593])).

tff(c_20,plain,(
    ! [A_14,B_15] : k1_setfam_1(k2_tarski(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_631,plain,(
    ! [B_100,A_101] : k3_xboole_0(B_100,A_101) = k3_xboole_0(A_101,B_100) ),
    inference(superposition,[status(thm),theory(equality)],[c_608,c_20])).

tff(c_71,plain,(
    ! [A_38,B_39] : r1_tarski(k3_xboole_0(A_38,B_39),A_38) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_76,plain,(
    ! [B_39] : k3_xboole_0(k1_xboole_0,B_39) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_71,c_12])).

tff(c_647,plain,(
    ! [B_100] : k3_xboole_0(B_100,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_631,c_76])).

tff(c_769,plain,(
    ! [A_108,B_109] : k5_xboole_0(A_108,k3_xboole_0(A_108,B_109)) = k4_xboole_0(A_108,B_109) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_778,plain,(
    ! [B_100] : k5_xboole_0(B_100,k1_xboole_0) = k4_xboole_0(B_100,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_647,c_769])).

tff(c_790,plain,(
    ! [B_100] : k4_xboole_0(B_100,k1_xboole_0) = B_100 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_778])).

tff(c_589,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_869,plain,(
    ! [B_118,A_119] :
      ( v2_tops_1(B_118,A_119)
      | ~ v3_tops_1(B_118,A_119)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(u1_struct_0(A_119)))
      | ~ l1_pre_topc(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_872,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_869])).

tff(c_875,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_589,c_872])).

tff(c_942,plain,(
    ! [A_126,B_127] :
      ( k1_tops_1(A_126,B_127) = k1_xboole_0
      | ~ v2_tops_1(B_127,A_126)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_945,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_942])).

tff(c_948,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_875,c_945])).

tff(c_820,plain,(
    ! [A_112,B_113,C_114] :
      ( k7_subset_1(A_112,B_113,C_114) = k4_xboole_0(B_113,C_114)
      | ~ m1_subset_1(B_113,k1_zfmisc_1(A_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_823,plain,(
    ! [C_114] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_114) = k4_xboole_0('#skF_2',C_114) ),
    inference(resolution,[status(thm)],[c_42,c_820])).

tff(c_982,plain,(
    ! [A_132,B_133] :
      ( k2_pre_topc(A_132,B_133) = B_133
      | ~ v4_pre_topc(B_133,A_132)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0(A_132)))
      | ~ l1_pre_topc(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_985,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_982])).

tff(c_988,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_985])).

tff(c_1029,plain,(
    ! [A_143,B_144] :
      ( k7_subset_1(u1_struct_0(A_143),k2_pre_topc(A_143,B_144),k1_tops_1(A_143,B_144)) = k2_tops_1(A_143,B_144)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(u1_struct_0(A_143)))
      | ~ l1_pre_topc(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1038,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_988,c_1029])).

tff(c_1045,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_790,c_948,c_823,c_1038])).

tff(c_1047,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_590,c_1045])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:25:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.34  
% 2.80/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.35  %$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.80/1.35  
% 2.80/1.35  %Foreground sorts:
% 2.80/1.35  
% 2.80/1.35  
% 2.80/1.35  %Background operators:
% 2.80/1.35  
% 2.80/1.35  
% 2.80/1.35  %Foreground operators:
% 2.80/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.80/1.35  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.80/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.80/1.35  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 2.80/1.35  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.80/1.35  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 2.80/1.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.80/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.80/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.80/1.35  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.80/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.80/1.35  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.80/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.80/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.80/1.35  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.80/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.35  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.80/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.80/1.35  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.80/1.35  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.80/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.80/1.35  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.80/1.35  
% 2.80/1.36  tff(f_121, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => (v3_tops_1(B, A) <=> (B = k2_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_tops_1)).
% 2.80/1.36  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 2.80/1.36  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.80/1.36  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tops_1)).
% 2.80/1.36  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tops_1(B, A) & v4_pre_topc(B, A)) => v3_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_tops_1)).
% 2.80/1.36  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.80/1.36  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.80/1.36  tff(f_49, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.80/1.36  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.80/1.36  tff(f_39, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.80/1.36  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.80/1.36  tff(f_98, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_tops_1)).
% 2.80/1.36  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.80/1.36  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.80/1.36  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 2.80/1.36  tff(c_52, plain, (v3_tops_1('#skF_2', '#skF_1') | k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.80/1.36  tff(c_121, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(splitLeft, [status(thm)], [c_52])).
% 2.80/1.36  tff(c_46, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.80/1.36  tff(c_127, plain, (~v3_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_46])).
% 2.80/1.36  tff(c_44, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.80/1.36  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.80/1.36  tff(c_499, plain, (![A_75, B_76]: (k1_tops_1(A_75, B_76)=k1_xboole_0 | ~v2_tops_1(B_76, A_75) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.80/1.36  tff(c_502, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_499])).
% 2.80/1.36  tff(c_505, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_502])).
% 2.80/1.36  tff(c_506, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_505])).
% 2.80/1.36  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.80/1.36  tff(c_522, plain, (![B_81, A_82]: (v2_tops_1(B_81, A_82) | ~r1_tarski(B_81, k2_tops_1(A_82, B_81)) | ~m1_subset_1(B_81, k1_zfmisc_1(u1_struct_0(A_82))) | ~l1_pre_topc(A_82))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.80/1.36  tff(c_527, plain, (v2_tops_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_2', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_121, c_522])).
% 2.80/1.36  tff(c_530, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_6, c_527])).
% 2.80/1.36  tff(c_532, plain, $false, inference(negUnitSimplification, [status(thm)], [c_506, c_530])).
% 2.80/1.36  tff(c_534, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_505])).
% 2.80/1.36  tff(c_40, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 2.80/1.36  tff(c_580, plain, (![B_94, A_95]: (v3_tops_1(B_94, A_95) | ~v4_pre_topc(B_94, A_95) | ~v2_tops_1(B_94, A_95) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_pre_topc(A_95))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.80/1.36  tff(c_583, plain, (v3_tops_1('#skF_2', '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_580])).
% 2.80/1.36  tff(c_586, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_534, c_40, c_583])).
% 2.80/1.36  tff(c_588, plain, $false, inference(negUnitSimplification, [status(thm)], [c_127, c_586])).
% 2.80/1.36  tff(c_590, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(splitRight, [status(thm)], [c_52])).
% 2.80/1.36  tff(c_14, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.80/1.36  tff(c_16, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.80/1.36  tff(c_593, plain, (![A_96, B_97]: (k1_setfam_1(k2_tarski(A_96, B_97))=k3_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.80/1.36  tff(c_608, plain, (![B_98, A_99]: (k1_setfam_1(k2_tarski(B_98, A_99))=k3_xboole_0(A_99, B_98))), inference(superposition, [status(thm), theory('equality')], [c_16, c_593])).
% 2.80/1.36  tff(c_20, plain, (![A_14, B_15]: (k1_setfam_1(k2_tarski(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.80/1.36  tff(c_631, plain, (![B_100, A_101]: (k3_xboole_0(B_100, A_101)=k3_xboole_0(A_101, B_100))), inference(superposition, [status(thm), theory('equality')], [c_608, c_20])).
% 2.80/1.36  tff(c_71, plain, (![A_38, B_39]: (r1_tarski(k3_xboole_0(A_38, B_39), A_38))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.80/1.36  tff(c_12, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.80/1.36  tff(c_76, plain, (![B_39]: (k3_xboole_0(k1_xboole_0, B_39)=k1_xboole_0)), inference(resolution, [status(thm)], [c_71, c_12])).
% 2.80/1.36  tff(c_647, plain, (![B_100]: (k3_xboole_0(B_100, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_631, c_76])).
% 2.80/1.36  tff(c_769, plain, (![A_108, B_109]: (k5_xboole_0(A_108, k3_xboole_0(A_108, B_109))=k4_xboole_0(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.80/1.36  tff(c_778, plain, (![B_100]: (k5_xboole_0(B_100, k1_xboole_0)=k4_xboole_0(B_100, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_647, c_769])).
% 2.80/1.36  tff(c_790, plain, (![B_100]: (k4_xboole_0(B_100, k1_xboole_0)=B_100)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_778])).
% 2.80/1.36  tff(c_589, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_52])).
% 2.80/1.36  tff(c_869, plain, (![B_118, A_119]: (v2_tops_1(B_118, A_119) | ~v3_tops_1(B_118, A_119) | ~m1_subset_1(B_118, k1_zfmisc_1(u1_struct_0(A_119))) | ~l1_pre_topc(A_119))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.80/1.36  tff(c_872, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_869])).
% 2.80/1.36  tff(c_875, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_589, c_872])).
% 2.80/1.36  tff(c_942, plain, (![A_126, B_127]: (k1_tops_1(A_126, B_127)=k1_xboole_0 | ~v2_tops_1(B_127, A_126) | ~m1_subset_1(B_127, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_pre_topc(A_126))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.80/1.36  tff(c_945, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_942])).
% 2.80/1.36  tff(c_948, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_875, c_945])).
% 2.80/1.36  tff(c_820, plain, (![A_112, B_113, C_114]: (k7_subset_1(A_112, B_113, C_114)=k4_xboole_0(B_113, C_114) | ~m1_subset_1(B_113, k1_zfmisc_1(A_112)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.80/1.36  tff(c_823, plain, (![C_114]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_114)=k4_xboole_0('#skF_2', C_114))), inference(resolution, [status(thm)], [c_42, c_820])).
% 2.80/1.36  tff(c_982, plain, (![A_132, B_133]: (k2_pre_topc(A_132, B_133)=B_133 | ~v4_pre_topc(B_133, A_132) | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0(A_132))) | ~l1_pre_topc(A_132))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.80/1.36  tff(c_985, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_42, c_982])).
% 2.80/1.36  tff(c_988, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_985])).
% 2.80/1.36  tff(c_1029, plain, (![A_143, B_144]: (k7_subset_1(u1_struct_0(A_143), k2_pre_topc(A_143, B_144), k1_tops_1(A_143, B_144))=k2_tops_1(A_143, B_144) | ~m1_subset_1(B_144, k1_zfmisc_1(u1_struct_0(A_143))) | ~l1_pre_topc(A_143))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.80/1.36  tff(c_1038, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_988, c_1029])).
% 2.80/1.36  tff(c_1045, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_790, c_948, c_823, c_1038])).
% 2.80/1.36  tff(c_1047, plain, $false, inference(negUnitSimplification, [status(thm)], [c_590, c_1045])).
% 2.80/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.36  
% 2.80/1.36  Inference rules
% 2.80/1.36  ----------------------
% 2.80/1.36  #Ref     : 0
% 2.80/1.36  #Sup     : 224
% 2.80/1.36  #Fact    : 0
% 2.80/1.36  #Define  : 0
% 2.80/1.36  #Split   : 2
% 2.80/1.36  #Chain   : 0
% 2.80/1.36  #Close   : 0
% 2.80/1.36  
% 2.80/1.36  Ordering : KBO
% 2.80/1.36  
% 2.80/1.36  Simplification rules
% 2.80/1.36  ----------------------
% 2.80/1.36  #Subsume      : 26
% 2.80/1.36  #Demod        : 141
% 2.80/1.36  #Tautology    : 159
% 2.80/1.36  #SimpNegUnit  : 5
% 2.80/1.36  #BackRed      : 0
% 2.80/1.36  
% 2.80/1.36  #Partial instantiations: 0
% 2.80/1.36  #Strategies tried      : 1
% 2.80/1.36  
% 2.80/1.36  Timing (in seconds)
% 2.80/1.36  ----------------------
% 2.80/1.37  Preprocessing        : 0.33
% 2.80/1.37  Parsing              : 0.18
% 2.80/1.37  CNF conversion       : 0.02
% 2.80/1.37  Main loop            : 0.32
% 2.80/1.37  Inferencing          : 0.12
% 2.80/1.37  Reduction            : 0.11
% 2.80/1.37  Demodulation         : 0.09
% 2.80/1.37  BG Simplification    : 0.02
% 2.80/1.37  Subsumption          : 0.05
% 2.80/1.37  Abstraction          : 0.02
% 2.80/1.37  MUC search           : 0.00
% 2.80/1.37  Cooper               : 0.00
% 2.80/1.37  Total                : 0.69
% 2.80/1.37  Index Insertion      : 0.00
% 2.80/1.37  Index Deletion       : 0.00
% 2.80/1.37  Index Matching       : 0.00
% 2.80/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
