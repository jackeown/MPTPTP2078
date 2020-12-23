%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:36 EST 2020

% Result     : Theorem 5.70s
% Output     : CNFRefutation 5.70s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 150 expanded)
%              Number of leaves         :   34 (  66 expanded)
%              Depth                    :   10
%              Number of atoms          :  135 ( 303 expanded)
%              Number of equality atoms :   51 (  88 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_pre_topc,type,(
    k2_pre_topc: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_81,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_3793,plain,(
    ! [A_232,B_233,C_234] :
      ( k7_subset_1(A_232,B_233,C_234) = k4_xboole_0(B_233,C_234)
      | ~ m1_subset_1(B_233,k1_zfmisc_1(A_232)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3796,plain,(
    ! [C_234] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_234) = k4_xboole_0('#skF_2',C_234) ),
    inference(resolution,[status(thm)],[c_30,c_3793])).

tff(c_36,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_88,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1370,plain,(
    ! [A_124,B_125] :
      ( k4_subset_1(u1_struct_0(A_124),B_125,k2_tops_1(A_124,B_125)) = k2_pre_topc(A_124,B_125)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_124)))
      | ~ l1_pre_topc(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1374,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1370])).

tff(c_1378,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1374])).

tff(c_42,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_215,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_42])).

tff(c_275,plain,(
    ! [A_60,B_61,C_62] :
      ( k7_subset_1(A_60,B_61,C_62) = k4_xboole_0(B_61,C_62)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_352,plain,(
    ! [C_69] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_69) = k4_xboole_0('#skF_2',C_69) ),
    inference(resolution,[status(thm)],[c_30,c_275])).

tff(c_364,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_352])).

tff(c_6,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_63,plain,(
    ! [A_40,B_41] :
      ( k4_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_71,plain,(
    ! [A_7,B_8] : k4_xboole_0(k4_xboole_0(A_7,B_8),A_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_63])).

tff(c_145,plain,(
    ! [A_48,B_49] : k2_xboole_0(A_48,k4_xboole_0(B_49,A_48)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_160,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k2_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_145])).

tff(c_165,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_160])).

tff(c_393,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_165])).

tff(c_20,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k2_tops_1(A_19,B_20),k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_19)))
      | ~ l1_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_958,plain,(
    ! [A_107,B_108,C_109] :
      ( k4_subset_1(A_107,B_108,C_109) = k2_xboole_0(B_108,C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(A_107))
      | ~ m1_subset_1(B_108,k1_zfmisc_1(A_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3462,plain,(
    ! [A_205,B_206,B_207] :
      ( k4_subset_1(u1_struct_0(A_205),B_206,k2_tops_1(A_205,B_207)) = k2_xboole_0(B_206,k2_tops_1(A_205,B_207))
      | ~ m1_subset_1(B_206,k1_zfmisc_1(u1_struct_0(A_205)))
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0(A_205)))
      | ~ l1_pre_topc(A_205) ) ),
    inference(resolution,[status(thm)],[c_20,c_958])).

tff(c_3466,plain,(
    ! [B_207] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_207)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_207))
      | ~ m1_subset_1(B_207,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_3462])).

tff(c_3549,plain,(
    ! [B_212] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_212)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_212))
      | ~ m1_subset_1(B_212,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3466])).

tff(c_3556,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_3549])).

tff(c_3561,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1378,c_393,c_3556])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_657,plain,(
    ! [A_83,B_84] :
      ( v4_pre_topc(k2_pre_topc(A_83,B_84),A_83)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0(A_83)))
      | ~ l1_pre_topc(A_83)
      | ~ v2_pre_topc(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_661,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_657])).

tff(c_665,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_661])).

tff(c_3563,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3561,c_665])).

tff(c_3565,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_3563])).

tff(c_3566,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_3844,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3796,c_3566])).

tff(c_4546,plain,(
    ! [A_284,B_285] :
      ( k4_subset_1(u1_struct_0(A_284),B_285,k2_tops_1(A_284,B_285)) = k2_pre_topc(A_284,B_285)
      | ~ m1_subset_1(B_285,k1_zfmisc_1(u1_struct_0(A_284)))
      | ~ l1_pre_topc(A_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4550,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_4546])).

tff(c_4554,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_4550])).

tff(c_3567,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_4058,plain,(
    ! [A_260,B_261] :
      ( r1_tarski(k2_tops_1(A_260,B_261),B_261)
      | ~ v4_pre_topc(B_261,A_260)
      | ~ m1_subset_1(B_261,k1_zfmisc_1(u1_struct_0(A_260)))
      | ~ l1_pre_topc(A_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_4062,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_4058])).

tff(c_4066,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3567,c_4062])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4073,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4066,c_4])).

tff(c_12,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4098,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4073,c_12])).

tff(c_4112,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4098])).

tff(c_4284,plain,(
    ! [A_269,B_270,C_271] :
      ( k4_subset_1(A_269,B_270,C_271) = k2_xboole_0(B_270,C_271)
      | ~ m1_subset_1(C_271,k1_zfmisc_1(A_269))
      | ~ m1_subset_1(B_270,k1_zfmisc_1(A_269)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_7382,plain,(
    ! [A_387,B_388,B_389] :
      ( k4_subset_1(u1_struct_0(A_387),B_388,k2_tops_1(A_387,B_389)) = k2_xboole_0(B_388,k2_tops_1(A_387,B_389))
      | ~ m1_subset_1(B_388,k1_zfmisc_1(u1_struct_0(A_387)))
      | ~ m1_subset_1(B_389,k1_zfmisc_1(u1_struct_0(A_387)))
      | ~ l1_pre_topc(A_387) ) ),
    inference(resolution,[status(thm)],[c_20,c_4284])).

tff(c_7386,plain,(
    ! [B_389] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_389)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_389))
      | ~ m1_subset_1(B_389,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_7382])).

tff(c_8019,plain,(
    ! [B_400] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_400)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_400))
      | ~ m1_subset_1(B_400,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_7386])).

tff(c_8026,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_8019])).

tff(c_8031,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4554,c_4112,c_8026])).

tff(c_24,plain,(
    ! [A_23,B_25] :
      ( k7_subset_1(u1_struct_0(A_23),k2_pre_topc(A_23,B_25),k1_tops_1(A_23,B_25)) = k2_tops_1(A_23,B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_8038,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_8031,c_24])).

tff(c_8042,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_3796,c_8038])).

tff(c_8044,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3844,c_8042])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:17:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.70/2.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.70/2.10  
% 5.70/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.70/2.10  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.70/2.10  
% 5.70/2.10  %Foreground sorts:
% 5.70/2.10  
% 5.70/2.10  
% 5.70/2.10  %Background operators:
% 5.70/2.10  
% 5.70/2.10  
% 5.70/2.10  %Foreground operators:
% 5.70/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.70/2.10  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.70/2.10  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 5.70/2.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.70/2.10  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.70/2.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.70/2.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.70/2.10  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.70/2.10  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 5.70/2.10  tff('#skF_2', type, '#skF_2': $i).
% 5.70/2.10  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.70/2.10  tff('#skF_1', type, '#skF_1': $i).
% 5.70/2.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.70/2.10  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.70/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.70/2.10  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.70/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.70/2.10  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.70/2.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.70/2.10  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.70/2.10  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 5.70/2.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.70/2.10  
% 5.70/2.12  tff(f_102, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 5.70/2.12  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.70/2.12  tff(f_81, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 5.70/2.12  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 5.70/2.12  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.70/2.12  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.70/2.12  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.70/2.12  tff(f_59, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 5.70/2.12  tff(f_49, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.70/2.12  tff(f_67, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 5.70/2.12  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 5.70/2.12  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 5.70/2.12  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.70/2.12  tff(c_3793, plain, (![A_232, B_233, C_234]: (k7_subset_1(A_232, B_233, C_234)=k4_xboole_0(B_233, C_234) | ~m1_subset_1(B_233, k1_zfmisc_1(A_232)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.70/2.12  tff(c_3796, plain, (![C_234]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_234)=k4_xboole_0('#skF_2', C_234))), inference(resolution, [status(thm)], [c_30, c_3793])).
% 5.70/2.12  tff(c_36, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.70/2.12  tff(c_88, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_36])).
% 5.70/2.12  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.70/2.12  tff(c_1370, plain, (![A_124, B_125]: (k4_subset_1(u1_struct_0(A_124), B_125, k2_tops_1(A_124, B_125))=k2_pre_topc(A_124, B_125) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_124))) | ~l1_pre_topc(A_124))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.70/2.12  tff(c_1374, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1370])).
% 5.70/2.12  tff(c_1378, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1374])).
% 5.70/2.12  tff(c_42, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.70/2.12  tff(c_215, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_88, c_42])).
% 5.70/2.12  tff(c_275, plain, (![A_60, B_61, C_62]: (k7_subset_1(A_60, B_61, C_62)=k4_xboole_0(B_61, C_62) | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.70/2.12  tff(c_352, plain, (![C_69]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_69)=k4_xboole_0('#skF_2', C_69))), inference(resolution, [status(thm)], [c_30, c_275])).
% 5.70/2.12  tff(c_364, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_215, c_352])).
% 5.70/2.12  tff(c_6, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.70/2.12  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.70/2.12  tff(c_63, plain, (![A_40, B_41]: (k4_xboole_0(A_40, B_41)=k1_xboole_0 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.70/2.12  tff(c_71, plain, (![A_7, B_8]: (k4_xboole_0(k4_xboole_0(A_7, B_8), A_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_63])).
% 5.70/2.12  tff(c_145, plain, (![A_48, B_49]: (k2_xboole_0(A_48, k4_xboole_0(B_49, A_48))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.70/2.12  tff(c_160, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k2_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_71, c_145])).
% 5.70/2.12  tff(c_165, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(A_7, B_8))=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_160])).
% 5.70/2.12  tff(c_393, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_364, c_165])).
% 5.70/2.12  tff(c_20, plain, (![A_19, B_20]: (m1_subset_1(k2_tops_1(A_19, B_20), k1_zfmisc_1(u1_struct_0(A_19))) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_19))) | ~l1_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.70/2.12  tff(c_958, plain, (![A_107, B_108, C_109]: (k4_subset_1(A_107, B_108, C_109)=k2_xboole_0(B_108, C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(A_107)) | ~m1_subset_1(B_108, k1_zfmisc_1(A_107)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.70/2.12  tff(c_3462, plain, (![A_205, B_206, B_207]: (k4_subset_1(u1_struct_0(A_205), B_206, k2_tops_1(A_205, B_207))=k2_xboole_0(B_206, k2_tops_1(A_205, B_207)) | ~m1_subset_1(B_206, k1_zfmisc_1(u1_struct_0(A_205))) | ~m1_subset_1(B_207, k1_zfmisc_1(u1_struct_0(A_205))) | ~l1_pre_topc(A_205))), inference(resolution, [status(thm)], [c_20, c_958])).
% 5.70/2.12  tff(c_3466, plain, (![B_207]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_207))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_207)) | ~m1_subset_1(B_207, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_3462])).
% 5.70/2.12  tff(c_3549, plain, (![B_212]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_212))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_212)) | ~m1_subset_1(B_212, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3466])).
% 5.70/2.12  tff(c_3556, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_3549])).
% 5.70/2.12  tff(c_3561, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1378, c_393, c_3556])).
% 5.70/2.12  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.70/2.12  tff(c_657, plain, (![A_83, B_84]: (v4_pre_topc(k2_pre_topc(A_83, B_84), A_83) | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0(A_83))) | ~l1_pre_topc(A_83) | ~v2_pre_topc(A_83))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.70/2.12  tff(c_661, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_657])).
% 5.70/2.12  tff(c_665, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_661])).
% 5.70/2.12  tff(c_3563, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3561, c_665])).
% 5.70/2.12  tff(c_3565, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_3563])).
% 5.70/2.12  tff(c_3566, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_36])).
% 5.70/2.12  tff(c_3844, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3796, c_3566])).
% 5.70/2.12  tff(c_4546, plain, (![A_284, B_285]: (k4_subset_1(u1_struct_0(A_284), B_285, k2_tops_1(A_284, B_285))=k2_pre_topc(A_284, B_285) | ~m1_subset_1(B_285, k1_zfmisc_1(u1_struct_0(A_284))) | ~l1_pre_topc(A_284))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.70/2.12  tff(c_4550, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_4546])).
% 5.70/2.12  tff(c_4554, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_4550])).
% 5.70/2.12  tff(c_3567, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_36])).
% 5.70/2.12  tff(c_4058, plain, (![A_260, B_261]: (r1_tarski(k2_tops_1(A_260, B_261), B_261) | ~v4_pre_topc(B_261, A_260) | ~m1_subset_1(B_261, k1_zfmisc_1(u1_struct_0(A_260))) | ~l1_pre_topc(A_260))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.70/2.12  tff(c_4062, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_4058])).
% 5.70/2.12  tff(c_4066, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3567, c_4062])).
% 5.70/2.12  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.70/2.12  tff(c_4073, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_4066, c_4])).
% 5.70/2.12  tff(c_12, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.70/2.12  tff(c_4098, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4073, c_12])).
% 5.70/2.12  tff(c_4112, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_4098])).
% 5.70/2.12  tff(c_4284, plain, (![A_269, B_270, C_271]: (k4_subset_1(A_269, B_270, C_271)=k2_xboole_0(B_270, C_271) | ~m1_subset_1(C_271, k1_zfmisc_1(A_269)) | ~m1_subset_1(B_270, k1_zfmisc_1(A_269)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.70/2.12  tff(c_7382, plain, (![A_387, B_388, B_389]: (k4_subset_1(u1_struct_0(A_387), B_388, k2_tops_1(A_387, B_389))=k2_xboole_0(B_388, k2_tops_1(A_387, B_389)) | ~m1_subset_1(B_388, k1_zfmisc_1(u1_struct_0(A_387))) | ~m1_subset_1(B_389, k1_zfmisc_1(u1_struct_0(A_387))) | ~l1_pre_topc(A_387))), inference(resolution, [status(thm)], [c_20, c_4284])).
% 5.70/2.12  tff(c_7386, plain, (![B_389]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_389))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_389)) | ~m1_subset_1(B_389, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_7382])).
% 5.70/2.12  tff(c_8019, plain, (![B_400]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_400))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_400)) | ~m1_subset_1(B_400, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_7386])).
% 5.70/2.12  tff(c_8026, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_8019])).
% 5.70/2.12  tff(c_8031, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4554, c_4112, c_8026])).
% 5.70/2.12  tff(c_24, plain, (![A_23, B_25]: (k7_subset_1(u1_struct_0(A_23), k2_pre_topc(A_23, B_25), k1_tops_1(A_23, B_25))=k2_tops_1(A_23, B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(u1_struct_0(A_23))) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.70/2.12  tff(c_8038, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_8031, c_24])).
% 5.70/2.12  tff(c_8042, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_3796, c_8038])).
% 5.70/2.12  tff(c_8044, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3844, c_8042])).
% 5.70/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.70/2.12  
% 5.70/2.12  Inference rules
% 5.70/2.12  ----------------------
% 5.70/2.12  #Ref     : 0
% 5.70/2.12  #Sup     : 1951
% 5.70/2.12  #Fact    : 0
% 5.70/2.12  #Define  : 0
% 5.70/2.12  #Split   : 4
% 5.70/2.12  #Chain   : 0
% 5.70/2.12  #Close   : 0
% 5.70/2.12  
% 5.70/2.12  Ordering : KBO
% 5.70/2.12  
% 5.70/2.12  Simplification rules
% 5.70/2.12  ----------------------
% 5.70/2.12  #Subsume      : 383
% 5.70/2.12  #Demod        : 1658
% 5.70/2.12  #Tautology    : 1231
% 5.70/2.12  #SimpNegUnit  : 3
% 5.70/2.12  #BackRed      : 5
% 5.70/2.12  
% 5.70/2.12  #Partial instantiations: 0
% 5.70/2.12  #Strategies tried      : 1
% 5.70/2.12  
% 5.70/2.12  Timing (in seconds)
% 5.70/2.12  ----------------------
% 5.70/2.12  Preprocessing        : 0.31
% 5.70/2.12  Parsing              : 0.17
% 5.70/2.12  CNF conversion       : 0.02
% 5.70/2.12  Main loop            : 1.05
% 5.70/2.12  Inferencing          : 0.33
% 5.70/2.12  Reduction            : 0.41
% 5.70/2.12  Demodulation         : 0.32
% 5.70/2.12  BG Simplification    : 0.03
% 5.70/2.12  Subsumption          : 0.21
% 5.70/2.12  Abstraction          : 0.05
% 5.70/2.12  MUC search           : 0.00
% 5.70/2.12  Cooper               : 0.00
% 5.70/2.12  Total                : 1.40
% 5.70/2.12  Index Insertion      : 0.00
% 5.70/2.12  Index Deletion       : 0.00
% 5.70/2.12  Index Matching       : 0.00
% 5.70/2.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
