%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:20 EST 2020

% Result     : Theorem 7.23s
% Output     : CNFRefutation 7.52s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 270 expanded)
%              Number of leaves         :   42 ( 108 expanded)
%              Depth                    :   14
%              Number of atoms          :  167 ( 465 expanded)
%              Number of equality atoms :   97 ( 215 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

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
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

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

tff(f_102,axiom,(
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
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_59,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_47,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_46,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_9299,plain,(
    ! [A_246,B_247,C_248] :
      ( k7_subset_1(A_246,B_247,C_248) = k4_xboole_0(B_247,C_248)
      | ~ m1_subset_1(B_247,k1_zfmisc_1(A_246)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_9302,plain,(
    ! [C_248] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_248) = k4_xboole_0('#skF_2',C_248) ),
    inference(resolution,[status(thm)],[c_44,c_9299])).

tff(c_10499,plain,(
    ! [A_284,B_285] :
      ( k7_subset_1(u1_struct_0(A_284),B_285,k2_tops_1(A_284,B_285)) = k1_tops_1(A_284,B_285)
      | ~ m1_subset_1(B_285,k1_zfmisc_1(u1_struct_0(A_284)))
      | ~ l1_pre_topc(A_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_10503,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_10499])).

tff(c_10507,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_9302,c_10503])).

tff(c_16,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10514,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10507,c_16])).

tff(c_56,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_128,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_50,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_377,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_48,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2428,plain,(
    ! [B_125,A_126] :
      ( v4_pre_topc(B_125,A_126)
      | k2_pre_topc(A_126,B_125) != B_125
      | ~ v2_pre_topc(A_126)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(u1_struct_0(A_126)))
      | ~ l1_pre_topc(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2434,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_2428])).

tff(c_2438,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48,c_2434])).

tff(c_2439,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_377,c_2438])).

tff(c_3057,plain,(
    ! [A_136,B_137] :
      ( k4_subset_1(u1_struct_0(A_136),B_137,k2_tops_1(A_136,B_137)) = k2_pre_topc(A_136,B_137)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(u1_struct_0(A_136)))
      | ~ l1_pre_topc(A_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_3061,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_3057])).

tff(c_3065,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_3061])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_101,plain,(
    ! [A_49,B_50] : k4_xboole_0(A_49,k2_xboole_0(A_49,B_50)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_108,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_101])).

tff(c_268,plain,(
    ! [A_62,B_63] : k2_xboole_0(A_62,k4_xboole_0(B_63,A_62)) = k2_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_280,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = k2_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_268])).

tff(c_290,plain,(
    ! [A_5] : k2_xboole_0(A_5,A_5) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_280])).

tff(c_417,plain,(
    ! [A_67,B_68] : k5_xboole_0(A_67,k4_xboole_0(B_68,A_67)) = k2_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_429,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = k2_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_417])).

tff(c_439,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_429])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_610,plain,(
    ! [A_77,B_78] : k5_xboole_0(A_77,k3_xboole_0(A_77,B_78)) = k4_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_633,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_610])).

tff(c_641,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_633])).

tff(c_820,plain,(
    ! [A_85,B_86,C_87] :
      ( k7_subset_1(A_85,B_86,C_87) = k4_xboole_0(B_86,C_87)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_881,plain,(
    ! [C_90] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_90) = k4_xboole_0('#skF_2',C_90) ),
    inference(resolution,[status(thm)],[c_44,c_820])).

tff(c_893,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_881])).

tff(c_1062,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_893,c_16])).

tff(c_823,plain,(
    ! [C_87] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_87) = k4_xboole_0('#skF_2',C_87) ),
    inference(resolution,[status(thm)],[c_44,c_820])).

tff(c_2746,plain,(
    ! [A_134,B_135] :
      ( k7_subset_1(u1_struct_0(A_134),B_135,k2_tops_1(A_134,B_135)) = k1_tops_1(A_134,B_135)
      | ~ m1_subset_1(B_135,k1_zfmisc_1(u1_struct_0(A_134)))
      | ~ l1_pre_topc(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2750,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_2746])).

tff(c_2754,plain,(
    k3_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1062,c_823,c_2750])).

tff(c_20,plain,(
    ! [B_17,A_16] : k2_tarski(B_17,A_16) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_177,plain,(
    ! [A_56,B_57] : k1_setfam_1(k2_tarski(A_56,B_57)) = k3_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_540,plain,(
    ! [A_73,B_74] : k1_setfam_1(k2_tarski(A_73,B_74)) = k3_xboole_0(B_74,A_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_177])).

tff(c_28,plain,(
    ! [A_26,B_27] : k1_setfam_1(k2_tarski(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_546,plain,(
    ! [B_74,A_73] : k3_xboole_0(B_74,A_73) = k3_xboole_0(A_73,B_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_540,c_28])).

tff(c_623,plain,(
    ! [A_73,B_74] : k5_xboole_0(A_73,k3_xboole_0(B_74,A_73)) = k4_xboole_0(A_73,B_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_546,c_610])).

tff(c_2765,plain,(
    k5_xboole_0(k1_tops_1('#skF_1','#skF_2'),k1_tops_1('#skF_1','#skF_2')) = k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2754,c_623])).

tff(c_2773,plain,(
    k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_641,c_2765])).

tff(c_18,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2791,plain,(
    k2_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k5_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2773,c_18])).

tff(c_2801,plain,(
    k2_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_439,c_2791])).

tff(c_162,plain,(
    ! [A_54,B_55] : k3_tarski(k2_tarski(A_54,B_55)) = k2_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_192,plain,(
    ! [B_58,A_59] : k3_tarski(k2_tarski(B_58,A_59)) = k2_xboole_0(A_59,B_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_162])).

tff(c_22,plain,(
    ! [A_18,B_19] : k3_tarski(k2_tarski(A_18,B_19)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_198,plain,(
    ! [B_58,A_59] : k2_xboole_0(B_58,A_59) = k2_xboole_0(A_59,B_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_22])).

tff(c_10,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_215,plain,(
    ! [B_60,A_61] : k2_xboole_0(B_60,A_61) = k2_xboole_0(A_61,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_22])).

tff(c_14,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k2_xboole_0(A_10,B_11)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_484,plain,(
    ! [B_71,A_72] : k4_xboole_0(B_71,k2_xboole_0(A_72,B_71)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_14])).

tff(c_1666,plain,(
    ! [B_111,A_112] : k4_xboole_0(k4_xboole_0(B_111,A_112),k2_xboole_0(A_112,B_111)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_484])).

tff(c_1706,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),k2_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_893,c_1666])).

tff(c_1760,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),k2_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_1706])).

tff(c_2804,plain,(
    k4_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2801,c_1760])).

tff(c_2892,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k5_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2804,c_18])).

tff(c_2902,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_439,c_2892])).

tff(c_34,plain,(
    ! [A_31,B_32] :
      ( m1_subset_1(k2_tops_1(A_31,B_32),k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2059,plain,(
    ! [A_117,B_118,C_119] :
      ( k4_subset_1(A_117,B_118,C_119) = k2_xboole_0(B_118,C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(A_117))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(A_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8023,plain,(
    ! [A_192,B_193,B_194] :
      ( k4_subset_1(u1_struct_0(A_192),B_193,k2_tops_1(A_192,B_194)) = k2_xboole_0(B_193,k2_tops_1(A_192,B_194))
      | ~ m1_subset_1(B_193,k1_zfmisc_1(u1_struct_0(A_192)))
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0(A_192)))
      | ~ l1_pre_topc(A_192) ) ),
    inference(resolution,[status(thm)],[c_34,c_2059])).

tff(c_8027,plain,(
    ! [B_194] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_194)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_194))
      | ~ m1_subset_1(B_194,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_8023])).

tff(c_8241,plain,(
    ! [B_197] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_197)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_197))
      | ~ m1_subset_1(B_197,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8027])).

tff(c_8248,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_8241])).

tff(c_8253,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3065,c_2902,c_8248])).

tff(c_8255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2439,c_8253])).

tff(c_8256,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_8591,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_8256])).

tff(c_8592,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_8812,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8592,c_50])).

tff(c_9360,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9302,c_8812])).

tff(c_10529,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10514,c_9360])).

tff(c_9688,plain,(
    ! [A_264,B_265] :
      ( k2_pre_topc(A_264,B_265) = B_265
      | ~ v4_pre_topc(B_265,A_264)
      | ~ m1_subset_1(B_265,k1_zfmisc_1(u1_struct_0(A_264)))
      | ~ l1_pre_topc(A_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_9694,plain,
    ( k2_pre_topc('#skF_1','#skF_2') = '#skF_2'
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_9688])).

tff(c_9698,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8592,c_9694])).

tff(c_11092,plain,(
    ! [A_296,B_297] :
      ( k7_subset_1(u1_struct_0(A_296),k2_pre_topc(A_296,B_297),k1_tops_1(A_296,B_297)) = k2_tops_1(A_296,B_297)
      | ~ m1_subset_1(B_297,k1_zfmisc_1(u1_struct_0(A_296)))
      | ~ l1_pre_topc(A_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_11101,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_9698,c_11092])).

tff(c_11105,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_10514,c_9302,c_11101])).

tff(c_11107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10529,c_11105])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n013.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 10:37:54 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.23/2.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.23/2.58  
% 7.23/2.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.23/2.58  %$ v4_pre_topc > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 7.23/2.58  
% 7.23/2.58  %Foreground sorts:
% 7.23/2.58  
% 7.23/2.58  
% 7.23/2.58  %Background operators:
% 7.23/2.58  
% 7.23/2.58  
% 7.23/2.58  %Foreground operators:
% 7.23/2.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.23/2.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.23/2.58  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 7.23/2.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.23/2.58  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.23/2.58  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.23/2.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.23/2.58  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 7.23/2.58  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 7.23/2.58  tff('#skF_2', type, '#skF_2': $i).
% 7.23/2.58  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 7.23/2.58  tff('#skF_1', type, '#skF_1': $i).
% 7.23/2.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.23/2.58  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 7.23/2.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.23/2.58  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.23/2.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.23/2.58  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.23/2.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.23/2.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.23/2.58  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.23/2.58  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 7.23/2.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.23/2.58  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.23/2.58  
% 7.52/2.60  tff(f_121, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 7.52/2.60  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 7.52/2.60  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_tops_1)).
% 7.52/2.60  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.52/2.60  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_pre_topc)).
% 7.52/2.60  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 7.52/2.60  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 7.52/2.60  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 7.52/2.60  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 7.52/2.60  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.52/2.60  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 7.52/2.60  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.52/2.60  tff(f_45, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 7.52/2.60  tff(f_59, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 7.52/2.60  tff(f_47, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 7.52/2.60  tff(f_80, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 7.52/2.60  tff(f_53, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 7.52/2.60  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 7.52/2.60  tff(c_46, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.52/2.60  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.52/2.60  tff(c_9299, plain, (![A_246, B_247, C_248]: (k7_subset_1(A_246, B_247, C_248)=k4_xboole_0(B_247, C_248) | ~m1_subset_1(B_247, k1_zfmisc_1(A_246)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.52/2.60  tff(c_9302, plain, (![C_248]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_248)=k4_xboole_0('#skF_2', C_248))), inference(resolution, [status(thm)], [c_44, c_9299])).
% 7.52/2.60  tff(c_10499, plain, (![A_284, B_285]: (k7_subset_1(u1_struct_0(A_284), B_285, k2_tops_1(A_284, B_285))=k1_tops_1(A_284, B_285) | ~m1_subset_1(B_285, k1_zfmisc_1(u1_struct_0(A_284))) | ~l1_pre_topc(A_284))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.52/2.60  tff(c_10503, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_10499])).
% 7.52/2.60  tff(c_10507, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_9302, c_10503])).
% 7.52/2.60  tff(c_16, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.52/2.60  tff(c_10514, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_10507, c_16])).
% 7.52/2.60  tff(c_56, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.52/2.60  tff(c_128, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_56])).
% 7.52/2.60  tff(c_50, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.52/2.60  tff(c_377, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_50])).
% 7.52/2.60  tff(c_48, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.52/2.60  tff(c_2428, plain, (![B_125, A_126]: (v4_pre_topc(B_125, A_126) | k2_pre_topc(A_126, B_125)!=B_125 | ~v2_pre_topc(A_126) | ~m1_subset_1(B_125, k1_zfmisc_1(u1_struct_0(A_126))) | ~l1_pre_topc(A_126))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.52/2.60  tff(c_2434, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_2428])).
% 7.52/2.60  tff(c_2438, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48, c_2434])).
% 7.52/2.60  tff(c_2439, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_377, c_2438])).
% 7.52/2.60  tff(c_3057, plain, (![A_136, B_137]: (k4_subset_1(u1_struct_0(A_136), B_137, k2_tops_1(A_136, B_137))=k2_pre_topc(A_136, B_137) | ~m1_subset_1(B_137, k1_zfmisc_1(u1_struct_0(A_136))) | ~l1_pre_topc(A_136))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.52/2.60  tff(c_3061, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_3057])).
% 7.52/2.60  tff(c_3065, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_3061])).
% 7.52/2.60  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.52/2.60  tff(c_101, plain, (![A_49, B_50]: (k4_xboole_0(A_49, k2_xboole_0(A_49, B_50))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.52/2.60  tff(c_108, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_101])).
% 7.52/2.60  tff(c_268, plain, (![A_62, B_63]: (k2_xboole_0(A_62, k4_xboole_0(B_63, A_62))=k2_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.52/2.60  tff(c_280, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=k2_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_108, c_268])).
% 7.52/2.60  tff(c_290, plain, (![A_5]: (k2_xboole_0(A_5, A_5)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_280])).
% 7.52/2.60  tff(c_417, plain, (![A_67, B_68]: (k5_xboole_0(A_67, k4_xboole_0(B_68, A_67))=k2_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.52/2.60  tff(c_429, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=k2_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_108, c_417])).
% 7.52/2.60  tff(c_439, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_290, c_429])).
% 7.52/2.60  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.52/2.60  tff(c_610, plain, (![A_77, B_78]: (k5_xboole_0(A_77, k3_xboole_0(A_77, B_78))=k4_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.52/2.60  tff(c_633, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_610])).
% 7.52/2.60  tff(c_641, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_108, c_633])).
% 7.52/2.60  tff(c_820, plain, (![A_85, B_86, C_87]: (k7_subset_1(A_85, B_86, C_87)=k4_xboole_0(B_86, C_87) | ~m1_subset_1(B_86, k1_zfmisc_1(A_85)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.52/2.60  tff(c_881, plain, (![C_90]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_90)=k4_xboole_0('#skF_2', C_90))), inference(resolution, [status(thm)], [c_44, c_820])).
% 7.52/2.60  tff(c_893, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_128, c_881])).
% 7.52/2.60  tff(c_1062, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_893, c_16])).
% 7.52/2.60  tff(c_823, plain, (![C_87]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_87)=k4_xboole_0('#skF_2', C_87))), inference(resolution, [status(thm)], [c_44, c_820])).
% 7.52/2.60  tff(c_2746, plain, (![A_134, B_135]: (k7_subset_1(u1_struct_0(A_134), B_135, k2_tops_1(A_134, B_135))=k1_tops_1(A_134, B_135) | ~m1_subset_1(B_135, k1_zfmisc_1(u1_struct_0(A_134))) | ~l1_pre_topc(A_134))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.52/2.60  tff(c_2750, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_2746])).
% 7.52/2.60  tff(c_2754, plain, (k3_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1062, c_823, c_2750])).
% 7.52/2.60  tff(c_20, plain, (![B_17, A_16]: (k2_tarski(B_17, A_16)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.52/2.60  tff(c_177, plain, (![A_56, B_57]: (k1_setfam_1(k2_tarski(A_56, B_57))=k3_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.52/2.60  tff(c_540, plain, (![A_73, B_74]: (k1_setfam_1(k2_tarski(A_73, B_74))=k3_xboole_0(B_74, A_73))), inference(superposition, [status(thm), theory('equality')], [c_20, c_177])).
% 7.52/2.60  tff(c_28, plain, (![A_26, B_27]: (k1_setfam_1(k2_tarski(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.52/2.60  tff(c_546, plain, (![B_74, A_73]: (k3_xboole_0(B_74, A_73)=k3_xboole_0(A_73, B_74))), inference(superposition, [status(thm), theory('equality')], [c_540, c_28])).
% 7.52/2.60  tff(c_623, plain, (![A_73, B_74]: (k5_xboole_0(A_73, k3_xboole_0(B_74, A_73))=k4_xboole_0(A_73, B_74))), inference(superposition, [status(thm), theory('equality')], [c_546, c_610])).
% 7.52/2.60  tff(c_2765, plain, (k5_xboole_0(k1_tops_1('#skF_1', '#skF_2'), k1_tops_1('#skF_1', '#skF_2'))=k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2754, c_623])).
% 7.52/2.60  tff(c_2773, plain, (k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_641, c_2765])).
% 7.52/2.60  tff(c_18, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.52/2.60  tff(c_2791, plain, (k2_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k5_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2773, c_18])).
% 7.52/2.60  tff(c_2801, plain, (k2_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_439, c_2791])).
% 7.52/2.60  tff(c_162, plain, (![A_54, B_55]: (k3_tarski(k2_tarski(A_54, B_55))=k2_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.52/2.60  tff(c_192, plain, (![B_58, A_59]: (k3_tarski(k2_tarski(B_58, A_59))=k2_xboole_0(A_59, B_58))), inference(superposition, [status(thm), theory('equality')], [c_20, c_162])).
% 7.52/2.60  tff(c_22, plain, (![A_18, B_19]: (k3_tarski(k2_tarski(A_18, B_19))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.52/2.60  tff(c_198, plain, (![B_58, A_59]: (k2_xboole_0(B_58, A_59)=k2_xboole_0(A_59, B_58))), inference(superposition, [status(thm), theory('equality')], [c_192, c_22])).
% 7.52/2.60  tff(c_10, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.52/2.60  tff(c_215, plain, (![B_60, A_61]: (k2_xboole_0(B_60, A_61)=k2_xboole_0(A_61, B_60))), inference(superposition, [status(thm), theory('equality')], [c_192, c_22])).
% 7.52/2.60  tff(c_14, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k2_xboole_0(A_10, B_11))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.52/2.60  tff(c_484, plain, (![B_71, A_72]: (k4_xboole_0(B_71, k2_xboole_0(A_72, B_71))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_215, c_14])).
% 7.52/2.60  tff(c_1666, plain, (![B_111, A_112]: (k4_xboole_0(k4_xboole_0(B_111, A_112), k2_xboole_0(A_112, B_111))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_484])).
% 7.52/2.60  tff(c_1706, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k2_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_893, c_1666])).
% 7.52/2.60  tff(c_1760, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), k2_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_198, c_1706])).
% 7.52/2.60  tff(c_2804, plain, (k4_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2801, c_1760])).
% 7.52/2.60  tff(c_2892, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k5_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2804, c_18])).
% 7.52/2.60  tff(c_2902, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_439, c_2892])).
% 7.52/2.60  tff(c_34, plain, (![A_31, B_32]: (m1_subset_1(k2_tops_1(A_31, B_32), k1_zfmisc_1(u1_struct_0(A_31))) | ~m1_subset_1(B_32, k1_zfmisc_1(u1_struct_0(A_31))) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.52/2.60  tff(c_2059, plain, (![A_117, B_118, C_119]: (k4_subset_1(A_117, B_118, C_119)=k2_xboole_0(B_118, C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(A_117)) | ~m1_subset_1(B_118, k1_zfmisc_1(A_117)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.52/2.60  tff(c_8023, plain, (![A_192, B_193, B_194]: (k4_subset_1(u1_struct_0(A_192), B_193, k2_tops_1(A_192, B_194))=k2_xboole_0(B_193, k2_tops_1(A_192, B_194)) | ~m1_subset_1(B_193, k1_zfmisc_1(u1_struct_0(A_192))) | ~m1_subset_1(B_194, k1_zfmisc_1(u1_struct_0(A_192))) | ~l1_pre_topc(A_192))), inference(resolution, [status(thm)], [c_34, c_2059])).
% 7.52/2.60  tff(c_8027, plain, (![B_194]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_194))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_194)) | ~m1_subset_1(B_194, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_8023])).
% 7.52/2.60  tff(c_8241, plain, (![B_197]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_197))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_197)) | ~m1_subset_1(B_197, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8027])).
% 7.52/2.60  tff(c_8248, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_44, c_8241])).
% 7.52/2.60  tff(c_8253, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3065, c_2902, c_8248])).
% 7.52/2.60  tff(c_8255, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2439, c_8253])).
% 7.52/2.60  tff(c_8256, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 7.52/2.60  tff(c_8591, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_128, c_8256])).
% 7.52/2.60  tff(c_8592, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_56])).
% 7.52/2.60  tff(c_8812, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8592, c_50])).
% 7.52/2.60  tff(c_9360, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9302, c_8812])).
% 7.52/2.60  tff(c_10529, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10514, c_9360])).
% 7.52/2.60  tff(c_9688, plain, (![A_264, B_265]: (k2_pre_topc(A_264, B_265)=B_265 | ~v4_pre_topc(B_265, A_264) | ~m1_subset_1(B_265, k1_zfmisc_1(u1_struct_0(A_264))) | ~l1_pre_topc(A_264))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.52/2.60  tff(c_9694, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2' | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_44, c_9688])).
% 7.52/2.60  tff(c_9698, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8592, c_9694])).
% 7.52/2.60  tff(c_11092, plain, (![A_296, B_297]: (k7_subset_1(u1_struct_0(A_296), k2_pre_topc(A_296, B_297), k1_tops_1(A_296, B_297))=k2_tops_1(A_296, B_297) | ~m1_subset_1(B_297, k1_zfmisc_1(u1_struct_0(A_296))) | ~l1_pre_topc(A_296))), inference(cnfTransformation, [status(thm)], [f_95])).
% 7.52/2.60  tff(c_11101, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_9698, c_11092])).
% 7.52/2.60  tff(c_11105, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_10514, c_9302, c_11101])).
% 7.52/2.60  tff(c_11107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10529, c_11105])).
% 7.52/2.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.52/2.60  
% 7.52/2.60  Inference rules
% 7.52/2.60  ----------------------
% 7.52/2.60  #Ref     : 0
% 7.52/2.60  #Sup     : 2748
% 7.52/2.60  #Fact    : 0
% 7.52/2.60  #Define  : 0
% 7.52/2.60  #Split   : 3
% 7.52/2.60  #Chain   : 0
% 7.52/2.60  #Close   : 0
% 7.52/2.60  
% 7.52/2.60  Ordering : KBO
% 7.52/2.60  
% 7.52/2.60  Simplification rules
% 7.52/2.60  ----------------------
% 7.52/2.60  #Subsume      : 119
% 7.52/2.60  #Demod        : 4410
% 7.52/2.60  #Tautology    : 2110
% 7.52/2.60  #SimpNegUnit  : 3
% 7.52/2.60  #BackRed      : 8
% 7.52/2.60  
% 7.52/2.60  #Partial instantiations: 0
% 7.52/2.60  #Strategies tried      : 1
% 7.52/2.60  
% 7.52/2.60  Timing (in seconds)
% 7.52/2.60  ----------------------
% 7.52/2.61  Preprocessing        : 0.34
% 7.52/2.61  Parsing              : 0.18
% 7.52/2.61  CNF conversion       : 0.02
% 7.52/2.61  Main loop            : 1.51
% 7.52/2.61  Inferencing          : 0.38
% 7.52/2.61  Reduction            : 0.83
% 7.52/2.61  Demodulation         : 0.73
% 7.52/2.61  BG Simplification    : 0.04
% 7.52/2.61  Subsumption          : 0.18
% 7.52/2.61  Abstraction          : 0.07
% 7.52/2.61  MUC search           : 0.00
% 7.52/2.61  Cooper               : 0.00
% 7.52/2.61  Total                : 1.89
% 7.52/2.61  Index Insertion      : 0.00
% 7.52/2.61  Index Deletion       : 0.00
% 7.52/2.61  Index Matching       : 0.00
% 7.52/2.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
