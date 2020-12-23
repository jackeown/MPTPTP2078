%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:03 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 147 expanded)
%              Number of leaves         :   43 (  71 expanded)
%              Depth                    :    7
%              Number of atoms          :  142 ( 313 expanded)
%              Number of equality atoms :   41 (  75 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_131,negated_conjecture,(
    ~ ! [A] :
        ( l1_pre_topc(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
             => ( v3_tops_1(B,A)
              <=> B = k2_tops_1(A,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).

tff(f_90,axiom,(
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

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> r1_tarski(B,k2_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

tff(f_119,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( ( v2_tops_1(B,A)
              & v4_pre_topc(B,A) )
           => v3_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_tops_1)).

tff(f_37,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_39,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_49,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_51,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_52,plain,
    ( k2_tops_1('#skF_1','#skF_2') != '#skF_2'
    | ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_98,plain,(
    ~ v3_tops_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_48,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_198,plain,(
    ! [B_70,A_71] :
      ( v2_tops_1(B_70,A_71)
      | k1_tops_1(A_71,B_70) != k1_xboole_0
      | ~ m1_subset_1(B_70,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_pre_topc(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_201,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_198])).

tff(c_208,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_201])).

tff(c_210,plain,(
    k1_tops_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_208])).

tff(c_230,plain,(
    ! [A_77,B_78] :
      ( k1_tops_1(A_77,B_78) = k1_xboole_0
      | ~ v2_tops_1(B_78,A_77)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(u1_struct_0(A_77)))
      | ~ l1_pre_topc(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_233,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_230])).

tff(c_240,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_233])).

tff(c_241,plain,(
    ~ v2_tops_1('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_210,c_240])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_99,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_58])).

tff(c_263,plain,(
    ! [B_84,A_85] :
      ( v2_tops_1(B_84,A_85)
      | ~ r1_tarski(B_84,k2_tops_1(A_85,B_84))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_85)))
      | ~ l1_pre_topc(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_267,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_263])).

tff(c_272,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_6,c_267])).

tff(c_274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_241,c_272])).

tff(c_275,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_208])).

tff(c_46,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_359,plain,(
    ! [B_103,A_104] :
      ( v3_tops_1(B_103,A_104)
      | ~ v4_pre_topc(B_103,A_104)
      | ~ v2_tops_1(B_103,A_104)
      | ~ m1_subset_1(B_103,k1_zfmisc_1(u1_struct_0(A_104)))
      | ~ l1_pre_topc(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_362,plain,
    ( v3_tops_1('#skF_2','#skF_1')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_359])).

tff(c_369,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_275,c_46,c_362])).

tff(c_371,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_369])).

tff(c_372,plain,(
    k2_tops_1('#skF_1','#skF_2') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_12,plain,(
    ! [A_7] : k1_subset_1(A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [A_14] : k3_subset_1(A_14,k1_subset_1(A_14)) = k2_subset_1(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_59,plain,(
    ! [A_14] : k3_subset_1(A_14,k1_subset_1(A_14)) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_20])).

tff(c_60,plain,(
    ! [A_14] : k3_subset_1(A_14,k1_xboole_0) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_59])).

tff(c_22,plain,(
    ! [A_15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_401,plain,(
    ! [A_111,B_112] :
      ( k4_xboole_0(A_111,B_112) = k3_subset_1(A_111,B_112)
      | ~ m1_subset_1(B_112,k1_zfmisc_1(A_111)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_407,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = k3_subset_1(A_15,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_22,c_401])).

tff(c_410,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_407])).

tff(c_433,plain,(
    ! [A_120,B_121,C_122] :
      ( k7_subset_1(A_120,B_121,C_122) = k4_xboole_0(B_121,C_122)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(A_120)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_438,plain,(
    ! [C_122] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_122) = k4_xboole_0('#skF_2',C_122) ),
    inference(resolution,[status(thm)],[c_48,c_433])).

tff(c_471,plain,(
    ! [A_129,B_130] :
      ( k2_pre_topc(A_129,B_130) = B_130
      | ~ v4_pre_topc(B_130,A_129)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(u1_struct_0(A_129)))
      | ~ l1_pre_topc(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_474,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_471])).

tff(c_481,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_474])).

tff(c_373,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_458,plain,(
    ! [B_126,A_127] :
      ( v2_tops_1(B_126,A_127)
      | ~ v3_tops_1(B_126,A_127)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(u1_struct_0(A_127)))
      | ~ l1_pre_topc(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_461,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_458])).

tff(c_468,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_373,c_461])).

tff(c_501,plain,(
    ! [A_135,B_136] :
      ( k1_tops_1(A_135,B_136) = k1_xboole_0
      | ~ v2_tops_1(B_136,A_135)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_504,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_501])).

tff(c_511,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_468,c_504])).

tff(c_592,plain,(
    ! [A_151,B_152] :
      ( k7_subset_1(u1_struct_0(A_151),k2_pre_topc(A_151,B_152),k1_tops_1(A_151,B_152)) = k2_tops_1(A_151,B_152)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(u1_struct_0(A_151)))
      | ~ l1_pre_topc(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_601,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k1_xboole_0) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_511,c_592])).

tff(c_608,plain,(
    k2_tops_1('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_410,c_438,c_481,c_601])).

tff(c_610,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_372,c_608])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:05:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.40  
% 2.86/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.40  %$ v4_pre_topc > v3_tops_1 > v2_tops_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.86/1.40  
% 2.86/1.40  %Foreground sorts:
% 2.86/1.40  
% 2.86/1.40  
% 2.86/1.40  %Background operators:
% 2.86/1.40  
% 2.86/1.40  
% 2.86/1.40  %Foreground operators:
% 2.86/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.86/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.86/1.40  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 2.86/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.86/1.40  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 2.86/1.40  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.86/1.40  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 2.86/1.40  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.86/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.86/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.86/1.40  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.86/1.40  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 2.86/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.86/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.86/1.40  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 2.86/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.86/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.86/1.40  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 2.86/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.40  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.86/1.40  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.86/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.86/1.40  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.86/1.40  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.86/1.40  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 2.86/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.86/1.40  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.86/1.40  
% 2.86/1.42  tff(f_131, negated_conjecture, ~(![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => (v3_tops_1(B, A) <=> (B = k2_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_tops_1)).
% 2.86/1.42  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 2.86/1.42  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.86/1.42  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> r1_tarski(B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tops_1)).
% 2.86/1.42  tff(f_119, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tops_1(B, A) & v4_pre_topc(B, A)) => v3_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_tops_1)).
% 2.86/1.42  tff(f_37, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.86/1.42  tff(f_39, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.86/1.42  tff(f_49, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 2.86/1.42  tff(f_51, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.86/1.42  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.86/1.42  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 2.86/1.42  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 2.86/1.42  tff(f_108, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_tops_1)).
% 2.86/1.42  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 2.86/1.42  tff(c_52, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2' | ~v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.86/1.42  tff(c_98, plain, (~v3_tops_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_52])).
% 2.86/1.42  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.86/1.42  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.86/1.42  tff(c_198, plain, (![B_70, A_71]: (v2_tops_1(B_70, A_71) | k1_tops_1(A_71, B_70)!=k1_xboole_0 | ~m1_subset_1(B_70, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_pre_topc(A_71))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.86/1.42  tff(c_201, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0 | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_198])).
% 2.86/1.42  tff(c_208, plain, (v2_tops_1('#skF_2', '#skF_1') | k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_201])).
% 2.86/1.42  tff(c_210, plain, (k1_tops_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_208])).
% 2.86/1.42  tff(c_230, plain, (![A_77, B_78]: (k1_tops_1(A_77, B_78)=k1_xboole_0 | ~v2_tops_1(B_78, A_77) | ~m1_subset_1(B_78, k1_zfmisc_1(u1_struct_0(A_77))) | ~l1_pre_topc(A_77))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.86/1.42  tff(c_233, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_230])).
% 2.86/1.42  tff(c_240, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_233])).
% 2.86/1.42  tff(c_241, plain, (~v2_tops_1('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_210, c_240])).
% 2.86/1.42  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.86/1.42  tff(c_58, plain, (v3_tops_1('#skF_2', '#skF_1') | k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.86/1.42  tff(c_99, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_98, c_58])).
% 2.86/1.42  tff(c_263, plain, (![B_84, A_85]: (v2_tops_1(B_84, A_85) | ~r1_tarski(B_84, k2_tops_1(A_85, B_84)) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_85))) | ~l1_pre_topc(A_85))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.86/1.42  tff(c_267, plain, (v2_tops_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_2', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_99, c_263])).
% 2.86/1.42  tff(c_272, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_6, c_267])).
% 2.86/1.42  tff(c_274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_241, c_272])).
% 2.86/1.42  tff(c_275, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_208])).
% 2.86/1.42  tff(c_46, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 2.86/1.42  tff(c_359, plain, (![B_103, A_104]: (v3_tops_1(B_103, A_104) | ~v4_pre_topc(B_103, A_104) | ~v2_tops_1(B_103, A_104) | ~m1_subset_1(B_103, k1_zfmisc_1(u1_struct_0(A_104))) | ~l1_pre_topc(A_104))), inference(cnfTransformation, [status(thm)], [f_119])).
% 2.86/1.42  tff(c_362, plain, (v3_tops_1('#skF_2', '#skF_1') | ~v4_pre_topc('#skF_2', '#skF_1') | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_359])).
% 2.86/1.42  tff(c_369, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_275, c_46, c_362])).
% 2.86/1.42  tff(c_371, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_369])).
% 2.86/1.42  tff(c_372, plain, (k2_tops_1('#skF_1', '#skF_2')!='#skF_2'), inference(splitRight, [status(thm)], [c_52])).
% 2.86/1.42  tff(c_12, plain, (![A_7]: (k1_subset_1(A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.86/1.42  tff(c_14, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.86/1.42  tff(c_20, plain, (![A_14]: (k3_subset_1(A_14, k1_subset_1(A_14))=k2_subset_1(A_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.86/1.42  tff(c_59, plain, (![A_14]: (k3_subset_1(A_14, k1_subset_1(A_14))=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_20])).
% 2.86/1.42  tff(c_60, plain, (![A_14]: (k3_subset_1(A_14, k1_xboole_0)=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_59])).
% 2.86/1.42  tff(c_22, plain, (![A_15]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.86/1.42  tff(c_401, plain, (![A_111, B_112]: (k4_xboole_0(A_111, B_112)=k3_subset_1(A_111, B_112) | ~m1_subset_1(B_112, k1_zfmisc_1(A_111)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.86/1.42  tff(c_407, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=k3_subset_1(A_15, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_401])).
% 2.86/1.42  tff(c_410, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_407])).
% 2.86/1.42  tff(c_433, plain, (![A_120, B_121, C_122]: (k7_subset_1(A_120, B_121, C_122)=k4_xboole_0(B_121, C_122) | ~m1_subset_1(B_121, k1_zfmisc_1(A_120)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.86/1.42  tff(c_438, plain, (![C_122]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_122)=k4_xboole_0('#skF_2', C_122))), inference(resolution, [status(thm)], [c_48, c_433])).
% 2.86/1.42  tff(c_471, plain, (![A_129, B_130]: (k2_pre_topc(A_129, B_130)=B_130 | ~v4_pre_topc(B_130, A_129) | ~m1_subset_1(B_130, k1_zfmisc_1(u1_struct_0(A_129))) | ~l1_pre_topc(A_129))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.86/1.42  tff(c_474, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_471])).
% 2.86/1.42  tff(c_481, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_474])).
% 2.86/1.42  tff(c_373, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_52])).
% 2.86/1.42  tff(c_458, plain, (![B_126, A_127]: (v2_tops_1(B_126, A_127) | ~v3_tops_1(B_126, A_127) | ~m1_subset_1(B_126, k1_zfmisc_1(u1_struct_0(A_127))) | ~l1_pre_topc(A_127))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.86/1.42  tff(c_461, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_458])).
% 2.86/1.42  tff(c_468, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_373, c_461])).
% 2.86/1.42  tff(c_501, plain, (![A_135, B_136]: (k1_tops_1(A_135, B_136)=k1_xboole_0 | ~v2_tops_1(B_136, A_135) | ~m1_subset_1(B_136, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.86/1.42  tff(c_504, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_48, c_501])).
% 2.86/1.42  tff(c_511, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_468, c_504])).
% 2.86/1.42  tff(c_592, plain, (![A_151, B_152]: (k7_subset_1(u1_struct_0(A_151), k2_pre_topc(A_151, B_152), k1_tops_1(A_151, B_152))=k2_tops_1(A_151, B_152) | ~m1_subset_1(B_152, k1_zfmisc_1(u1_struct_0(A_151))) | ~l1_pre_topc(A_151))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.86/1.42  tff(c_601, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_511, c_592])).
% 2.86/1.42  tff(c_608, plain, (k2_tops_1('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_410, c_438, c_481, c_601])).
% 2.86/1.42  tff(c_610, plain, $false, inference(negUnitSimplification, [status(thm)], [c_372, c_608])).
% 2.86/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.42  
% 2.86/1.42  Inference rules
% 2.86/1.42  ----------------------
% 2.86/1.42  #Ref     : 0
% 2.86/1.42  #Sup     : 113
% 2.86/1.42  #Fact    : 0
% 2.86/1.42  #Define  : 0
% 2.86/1.42  #Split   : 2
% 2.86/1.42  #Chain   : 0
% 2.86/1.42  #Close   : 0
% 2.86/1.42  
% 2.86/1.42  Ordering : KBO
% 2.86/1.42  
% 2.86/1.42  Simplification rules
% 2.86/1.42  ----------------------
% 2.86/1.42  #Subsume      : 2
% 2.86/1.42  #Demod        : 66
% 2.86/1.42  #Tautology    : 69
% 2.86/1.42  #SimpNegUnit  : 7
% 2.86/1.42  #BackRed      : 0
% 2.86/1.42  
% 2.86/1.42  #Partial instantiations: 0
% 2.86/1.42  #Strategies tried      : 1
% 2.86/1.42  
% 2.86/1.42  Timing (in seconds)
% 2.86/1.42  ----------------------
% 2.86/1.42  Preprocessing        : 0.35
% 2.86/1.42  Parsing              : 0.18
% 2.86/1.42  CNF conversion       : 0.02
% 2.86/1.42  Main loop            : 0.31
% 2.86/1.42  Inferencing          : 0.13
% 2.86/1.42  Reduction            : 0.10
% 2.86/1.42  Demodulation         : 0.07
% 2.86/1.42  BG Simplification    : 0.02
% 2.86/1.42  Subsumption          : 0.05
% 2.86/1.42  Abstraction          : 0.02
% 2.86/1.43  MUC search           : 0.00
% 2.86/1.43  Cooper               : 0.00
% 2.86/1.43  Total                : 0.71
% 2.86/1.43  Index Insertion      : 0.00
% 2.86/1.43  Index Deletion       : 0.00
% 2.86/1.43  Index Matching       : 0.00
% 2.86/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
