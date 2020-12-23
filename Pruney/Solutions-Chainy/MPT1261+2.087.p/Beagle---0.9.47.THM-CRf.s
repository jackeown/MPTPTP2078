%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:21:24 EST 2020

% Result     : Theorem 18.58s
% Output     : CNFRefutation 18.58s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 244 expanded)
%              Number of leaves         :   50 (  99 expanded)
%              Depth                    :   10
%              Number of atoms          :  199 ( 445 expanded)
%              Number of equality atoms :   83 ( 147 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(f_169,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_120,axiom,(
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

tff(f_99,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_141,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_150,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_157,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_47,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_93,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_127,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_55,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_70,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_47638,plain,(
    ! [A_736,B_737,C_738] :
      ( k7_subset_1(A_736,B_737,C_738) = k4_xboole_0(B_737,C_738)
      | ~ m1_subset_1(B_737,k1_zfmisc_1(A_736)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_47652,plain,(
    ! [C_738] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_738) = k4_xboole_0('#skF_2',C_738) ),
    inference(resolution,[status(thm)],[c_70,c_47638])).

tff(c_82,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_102,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_76,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_260,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_72,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_74,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_4478,plain,(
    ! [B_231,A_232] :
      ( v4_pre_topc(B_231,A_232)
      | k2_pre_topc(A_232,B_231) != B_231
      | ~ v2_pre_topc(A_232)
      | ~ m1_subset_1(B_231,k1_zfmisc_1(u1_struct_0(A_232)))
      | ~ l1_pre_topc(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_4493,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2'
    | ~ v2_pre_topc('#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_4478])).

tff(c_4503,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_74,c_4493])).

tff(c_4504,plain,(
    k2_pre_topc('#skF_1','#skF_2') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_260,c_4503])).

tff(c_374,plain,(
    ! [A_94,B_95] :
      ( r1_tarski(A_94,B_95)
      | ~ m1_subset_1(A_94,k1_zfmisc_1(B_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_381,plain,(
    r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_70,c_374])).

tff(c_4807,plain,(
    ! [A_242,B_243] :
      ( k4_subset_1(u1_struct_0(A_242),B_243,k2_tops_1(A_242,B_243)) = k2_pre_topc(A_242,B_243)
      | ~ m1_subset_1(B_243,k1_zfmisc_1(u1_struct_0(A_242)))
      | ~ l1_pre_topc(A_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_4818,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_4807])).

tff(c_4827,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4818])).

tff(c_3015,plain,(
    ! [A_189,B_190,C_191] :
      ( k7_subset_1(A_189,B_190,C_191) = k4_xboole_0(B_190,C_191)
      | ~ m1_subset_1(B_190,k1_zfmisc_1(A_189)) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3269,plain,(
    ! [C_200] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_200) = k4_xboole_0('#skF_2',C_200) ),
    inference(resolution,[status(thm)],[c_70,c_3015])).

tff(c_3275,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3269,c_102])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [A_19,B_20] : r1_tarski(k4_xboole_0(A_19,B_20),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_261,plain,(
    ! [A_88,B_89] :
      ( k2_xboole_0(A_88,B_89) = B_89
      | ~ r1_tarski(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_320,plain,(
    ! [A_91,B_92] : k2_xboole_0(k4_xboole_0(A_91,B_92),A_91) = A_91 ),
    inference(resolution,[status(thm)],[c_24,c_261])).

tff(c_350,plain,(
    ! [A_1,B_92] : k2_xboole_0(A_1,k4_xboole_0(A_1,B_92)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_320])).

tff(c_3739,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_3275,c_350])).

tff(c_14,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_tarski(A_9,k2_xboole_0(C_11,B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_30,plain,(
    ! [A_26,B_27] : k4_xboole_0(A_26,k3_xboole_0(A_26,B_27)) = k4_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1272,plain,(
    ! [A_139,B_140,C_141] :
      ( r1_tarski(k4_xboole_0(A_139,B_140),C_141)
      | ~ r1_tarski(A_139,k2_xboole_0(B_140,C_141)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_36607,plain,(
    ! [A_534,B_535,C_536] :
      ( r1_tarski(k4_xboole_0(A_534,B_535),C_536)
      | ~ r1_tarski(A_534,k2_xboole_0(k3_xboole_0(A_534,B_535),C_536)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_1272])).

tff(c_36946,plain,(
    ! [A_537,B_538,B_539] :
      ( r1_tarski(k4_xboole_0(A_537,B_538),B_539)
      | ~ r1_tarski(A_537,B_539) ) ),
    inference(resolution,[status(thm)],[c_14,c_36607])).

tff(c_37122,plain,(
    ! [B_539] :
      ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),B_539)
      | ~ r1_tarski('#skF_2',B_539) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3275,c_36946])).

tff(c_52,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1(A_47,k1_zfmisc_1(B_48))
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_4188,plain,(
    ! [A_220,B_221,C_222] :
      ( k4_subset_1(A_220,B_221,C_222) = k2_xboole_0(B_221,C_222)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(A_220))
      | ~ m1_subset_1(B_221,k1_zfmisc_1(A_220)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_43731,plain,(
    ! [B_598,B_599,A_600] :
      ( k4_subset_1(B_598,B_599,A_600) = k2_xboole_0(B_599,A_600)
      | ~ m1_subset_1(B_599,k1_zfmisc_1(B_598))
      | ~ r1_tarski(A_600,B_598) ) ),
    inference(resolution,[status(thm)],[c_52,c_4188])).

tff(c_44390,plain,(
    ! [A_606] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',A_606) = k2_xboole_0('#skF_2',A_606)
      | ~ r1_tarski(A_606,u1_struct_0('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_70,c_43731])).

tff(c_44402,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2',u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_37122,c_44390])).

tff(c_44548,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_4827,c_3739,c_44402])).

tff(c_44550,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4504,c_44548])).

tff(c_44551,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_44794,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_44551])).

tff(c_44795,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_44946,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44795,c_76])).

tff(c_47797,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47652,c_44946])).

tff(c_48451,plain,(
    ! [A_763,B_764] :
      ( r1_tarski(k2_tops_1(A_763,B_764),B_764)
      | ~ v4_pre_topc(B_764,A_763)
      | ~ m1_subset_1(B_764,k1_zfmisc_1(u1_struct_0(A_763)))
      | ~ l1_pre_topc(A_763) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_48462,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_48451])).

tff(c_48471,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_44795,c_48462])).

tff(c_50136,plain,(
    ! [A_808,B_809] :
      ( k7_subset_1(u1_struct_0(A_808),B_809,k2_tops_1(A_808,B_809)) = k1_tops_1(A_808,B_809)
      | ~ m1_subset_1(B_809,k1_zfmisc_1(u1_struct_0(A_808)))
      | ~ l1_pre_topc(A_808) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_50147,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_50136])).

tff(c_50157,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_47652,c_50147])).

tff(c_46724,plain,(
    ! [A_714,B_715] :
      ( k4_xboole_0(A_714,B_715) = k3_subset_1(A_714,B_715)
      | ~ m1_subset_1(B_715,k1_zfmisc_1(A_714)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_53340,plain,(
    ! [B_871,A_872] :
      ( k4_xboole_0(B_871,A_872) = k3_subset_1(B_871,A_872)
      | ~ r1_tarski(A_872,B_871) ) ),
    inference(resolution,[status(thm)],[c_52,c_46724])).

tff(c_53469,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_48471,c_53340])).

tff(c_53558,plain,(
    k3_subset_1('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50157,c_53469])).

tff(c_46103,plain,(
    ! [A_694,B_695] :
      ( k3_subset_1(A_694,k3_subset_1(A_694,B_695)) = B_695
      | ~ m1_subset_1(B_695,k1_zfmisc_1(A_694)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_46110,plain,(
    ! [B_48,A_47] :
      ( k3_subset_1(B_48,k3_subset_1(B_48,A_47)) = A_47
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(resolution,[status(thm)],[c_52,c_46103])).

tff(c_56074,plain,
    ( k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_53558,c_46110])).

tff(c_56082,plain,(
    k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48471,c_56074])).

tff(c_44797,plain,(
    ! [B_624,A_625] : k2_xboole_0(B_624,A_625) = k2_xboole_0(A_625,B_624) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_44819,plain,(
    ! [A_625] : k2_xboole_0(k1_xboole_0,A_625) = A_625 ),
    inference(superposition,[status(thm),theory(equality)],[c_44797,c_18])).

tff(c_45176,plain,(
    ! [A_650,B_651] : k2_xboole_0(A_650,k4_xboole_0(B_651,A_650)) = k2_xboole_0(A_650,B_651) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_45186,plain,(
    ! [B_651] : k4_xboole_0(B_651,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_651) ),
    inference(superposition,[status(thm),theory(equality)],[c_45176,c_44819])).

tff(c_45204,plain,(
    ! [B_651] : k4_xboole_0(B_651,k1_xboole_0) = B_651 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44819,c_45186])).

tff(c_46,plain,(
    ! [A_44] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_46736,plain,(
    ! [A_44] : k4_xboole_0(A_44,k1_xboole_0) = k3_subset_1(A_44,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_46,c_46724])).

tff(c_46741,plain,(
    ! [A_44] : k3_subset_1(A_44,k1_xboole_0) = A_44 ),
    inference(demodulation,[status(thm),theory(equality)],[c_45204,c_46736])).

tff(c_47884,plain,(
    ! [A_746,B_747] :
      ( r1_tarski(k1_tops_1(A_746,B_747),B_747)
      | ~ m1_subset_1(B_747,k1_zfmisc_1(u1_struct_0(A_746)))
      | ~ l1_pre_topc(A_746) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_47895,plain,
    ( r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_47884])).

tff(c_47904,plain,(
    r1_tarski(k1_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_47895])).

tff(c_46926,plain,(
    ! [A_723,B_724,C_725] :
      ( r1_tarski(k4_xboole_0(A_723,B_724),C_725)
      | ~ r1_tarski(A_723,k2_xboole_0(B_724,C_725)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_22,plain,(
    ! [A_18] : r1_tarski(k1_xboole_0,A_18) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_45500,plain,(
    ! [B_663,A_664] :
      ( B_663 = A_664
      | ~ r1_tarski(B_663,A_664)
      | ~ r1_tarski(A_664,B_663) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_45523,plain,(
    ! [A_18] :
      ( k1_xboole_0 = A_18
      | ~ r1_tarski(A_18,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_45500])).

tff(c_46935,plain,(
    ! [A_723,B_724] :
      ( k4_xboole_0(A_723,B_724) = k1_xboole_0
      | ~ r1_tarski(A_723,k2_xboole_0(B_724,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_46926,c_45523])).

tff(c_46972,plain,(
    ! [A_723,B_724] :
      ( k4_xboole_0(A_723,B_724) = k1_xboole_0
      | ~ r1_tarski(A_723,B_724) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_46935])).

tff(c_47916,plain,(
    k4_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_47904,c_46972])).

tff(c_32,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k4_xboole_0(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_53508,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k4_xboole_0(A_19,B_20)) = k3_subset_1(A_19,k4_xboole_0(A_19,B_20)) ),
    inference(resolution,[status(thm)],[c_24,c_53340])).

tff(c_55952,plain,(
    ! [A_903,B_904] : k3_subset_1(A_903,k4_xboole_0(A_903,B_904)) = k3_xboole_0(A_903,B_904) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_53508])).

tff(c_56000,plain,(
    k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = k3_subset_1(k1_tops_1('#skF_1','#skF_2'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_47916,c_55952])).

tff(c_56054,plain,(
    k3_xboole_0(k1_tops_1('#skF_1','#skF_2'),'#skF_2') = k1_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46741,c_56000])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_45303,plain,(
    ! [A_654,B_655] : k4_xboole_0(A_654,k3_xboole_0(A_654,B_655)) = k4_xboole_0(A_654,B_655) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_45341,plain,(
    ! [B_4,A_3] : k4_xboole_0(B_4,k3_xboole_0(A_3,B_4)) = k4_xboole_0(B_4,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_45303])).

tff(c_44997,plain,(
    ! [A_639,B_640] : k4_xboole_0(A_639,k4_xboole_0(A_639,B_640)) = k3_xboole_0(A_639,B_640) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_45052,plain,(
    ! [A_642,B_643] : r1_tarski(k3_xboole_0(A_642,B_643),A_642) ),
    inference(superposition,[status(thm),theory(equality)],[c_44997,c_24])).

tff(c_45058,plain,(
    ! [B_4,A_3] : r1_tarski(k3_xboole_0(B_4,A_3),A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_45052])).

tff(c_53493,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k3_xboole_0(B_4,A_3)) = k3_subset_1(A_3,k3_xboole_0(B_4,A_3)) ),
    inference(resolution,[status(thm)],[c_45058,c_53340])).

tff(c_53568,plain,(
    ! [A_3,B_4] : k3_subset_1(A_3,k3_xboole_0(B_4,A_3)) = k4_xboole_0(A_3,B_4) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45341,c_53493])).

tff(c_89389,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k3_subset_1('#skF_2',k1_tops_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_56054,c_53568])).

tff(c_89509,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56082,c_89389])).

tff(c_89511,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47797,c_89509])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:53:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.58/11.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.58/11.22  
% 18.58/11.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.58/11.22  %$ v4_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 18.58/11.22  
% 18.58/11.22  %Foreground sorts:
% 18.58/11.22  
% 18.58/11.22  
% 18.58/11.22  %Background operators:
% 18.58/11.22  
% 18.58/11.22  
% 18.58/11.22  %Foreground operators:
% 18.58/11.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.58/11.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 18.58/11.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 18.58/11.22  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 18.58/11.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 18.58/11.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 18.58/11.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 18.58/11.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.58/11.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 18.58/11.22  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 18.58/11.22  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 18.58/11.22  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 18.58/11.22  tff('#skF_2', type, '#skF_2': $i).
% 18.58/11.22  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 18.58/11.22  tff('#skF_1', type, '#skF_1': $i).
% 18.58/11.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 18.58/11.22  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 18.58/11.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.58/11.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.58/11.22  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 18.58/11.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 18.58/11.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 18.58/11.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 18.58/11.22  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 18.58/11.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 18.58/11.22  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 18.58/11.22  
% 18.58/11.24  tff(f_169, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tops_1)).
% 18.58/11.24  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 18.58/11.24  tff(f_120, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v4_pre_topc(B, A) => (k2_pre_topc(A, B) = B)) & ((v2_pre_topc(A) & (k2_pre_topc(A, B) = B)) => v4_pre_topc(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_pre_topc)).
% 18.58/11.24  tff(f_99, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 18.58/11.24  tff(f_141, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_tops_1)).
% 18.58/11.24  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 18.58/11.24  tff(f_57, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 18.58/11.24  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 18.58/11.24  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 18.58/11.24  tff(f_65, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 18.58/11.24  tff(f_63, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 18.58/11.24  tff(f_87, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 18.58/11.24  tff(f_150, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_tops_1)).
% 18.58/11.24  tff(f_157, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 18.58/11.24  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 18.58/11.24  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 18.58/11.24  tff(f_47, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 18.58/11.24  tff(f_59, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 18.58/11.24  tff(f_93, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 18.58/11.24  tff(f_127, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 18.58/11.24  tff(f_55, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 18.58/11.24  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 18.58/11.24  tff(f_67, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 18.58/11.24  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 18.58/11.24  tff(c_70, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_169])).
% 18.58/11.24  tff(c_47638, plain, (![A_736, B_737, C_738]: (k7_subset_1(A_736, B_737, C_738)=k4_xboole_0(B_737, C_738) | ~m1_subset_1(B_737, k1_zfmisc_1(A_736)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 18.58/11.24  tff(c_47652, plain, (![C_738]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_738)=k4_xboole_0('#skF_2', C_738))), inference(resolution, [status(thm)], [c_70, c_47638])).
% 18.58/11.24  tff(c_82, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_169])).
% 18.58/11.24  tff(c_102, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_82])).
% 18.58/11.24  tff(c_76, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_169])).
% 18.58/11.24  tff(c_260, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_76])).
% 18.58/11.24  tff(c_72, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_169])).
% 18.58/11.24  tff(c_74, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_169])).
% 18.58/11.24  tff(c_4478, plain, (![B_231, A_232]: (v4_pre_topc(B_231, A_232) | k2_pre_topc(A_232, B_231)!=B_231 | ~v2_pre_topc(A_232) | ~m1_subset_1(B_231, k1_zfmisc_1(u1_struct_0(A_232))) | ~l1_pre_topc(A_232))), inference(cnfTransformation, [status(thm)], [f_120])).
% 18.58/11.24  tff(c_4493, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2' | ~v2_pre_topc('#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_70, c_4478])).
% 18.58/11.24  tff(c_4503, plain, (v4_pre_topc('#skF_2', '#skF_1') | k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_74, c_4493])).
% 18.58/11.24  tff(c_4504, plain, (k2_pre_topc('#skF_1', '#skF_2')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_260, c_4503])).
% 18.58/11.24  tff(c_374, plain, (![A_94, B_95]: (r1_tarski(A_94, B_95) | ~m1_subset_1(A_94, k1_zfmisc_1(B_95)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 18.58/11.24  tff(c_381, plain, (r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_374])).
% 18.58/11.24  tff(c_4807, plain, (![A_242, B_243]: (k4_subset_1(u1_struct_0(A_242), B_243, k2_tops_1(A_242, B_243))=k2_pre_topc(A_242, B_243) | ~m1_subset_1(B_243, k1_zfmisc_1(u1_struct_0(A_242))) | ~l1_pre_topc(A_242))), inference(cnfTransformation, [status(thm)], [f_141])).
% 18.58/11.24  tff(c_4818, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_70, c_4807])).
% 18.58/11.24  tff(c_4827, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4818])).
% 18.58/11.24  tff(c_3015, plain, (![A_189, B_190, C_191]: (k7_subset_1(A_189, B_190, C_191)=k4_xboole_0(B_190, C_191) | ~m1_subset_1(B_190, k1_zfmisc_1(A_189)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 18.58/11.24  tff(c_3269, plain, (![C_200]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_200)=k4_xboole_0('#skF_2', C_200))), inference(resolution, [status(thm)], [c_70, c_3015])).
% 18.58/11.24  tff(c_3275, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3269, c_102])).
% 18.58/11.24  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 18.58/11.24  tff(c_24, plain, (![A_19, B_20]: (r1_tarski(k4_xboole_0(A_19, B_20), A_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 18.58/11.24  tff(c_261, plain, (![A_88, B_89]: (k2_xboole_0(A_88, B_89)=B_89 | ~r1_tarski(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_45])).
% 18.58/11.24  tff(c_320, plain, (![A_91, B_92]: (k2_xboole_0(k4_xboole_0(A_91, B_92), A_91)=A_91)), inference(resolution, [status(thm)], [c_24, c_261])).
% 18.58/11.24  tff(c_350, plain, (![A_1, B_92]: (k2_xboole_0(A_1, k4_xboole_0(A_1, B_92))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_320])).
% 18.58/11.24  tff(c_3739, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_3275, c_350])).
% 18.58/11.24  tff(c_14, plain, (![A_9, C_11, B_10]: (r1_tarski(A_9, k2_xboole_0(C_11, B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 18.58/11.24  tff(c_30, plain, (![A_26, B_27]: (k4_xboole_0(A_26, k3_xboole_0(A_26, B_27))=k4_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_65])).
% 18.58/11.24  tff(c_1272, plain, (![A_139, B_140, C_141]: (r1_tarski(k4_xboole_0(A_139, B_140), C_141) | ~r1_tarski(A_139, k2_xboole_0(B_140, C_141)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 18.58/11.24  tff(c_36607, plain, (![A_534, B_535, C_536]: (r1_tarski(k4_xboole_0(A_534, B_535), C_536) | ~r1_tarski(A_534, k2_xboole_0(k3_xboole_0(A_534, B_535), C_536)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_1272])).
% 18.58/11.24  tff(c_36946, plain, (![A_537, B_538, B_539]: (r1_tarski(k4_xboole_0(A_537, B_538), B_539) | ~r1_tarski(A_537, B_539))), inference(resolution, [status(thm)], [c_14, c_36607])).
% 18.58/11.24  tff(c_37122, plain, (![B_539]: (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), B_539) | ~r1_tarski('#skF_2', B_539))), inference(superposition, [status(thm), theory('equality')], [c_3275, c_36946])).
% 18.58/11.24  tff(c_52, plain, (![A_47, B_48]: (m1_subset_1(A_47, k1_zfmisc_1(B_48)) | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_99])).
% 18.58/11.24  tff(c_4188, plain, (![A_220, B_221, C_222]: (k4_subset_1(A_220, B_221, C_222)=k2_xboole_0(B_221, C_222) | ~m1_subset_1(C_222, k1_zfmisc_1(A_220)) | ~m1_subset_1(B_221, k1_zfmisc_1(A_220)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 18.58/11.24  tff(c_43731, plain, (![B_598, B_599, A_600]: (k4_subset_1(B_598, B_599, A_600)=k2_xboole_0(B_599, A_600) | ~m1_subset_1(B_599, k1_zfmisc_1(B_598)) | ~r1_tarski(A_600, B_598))), inference(resolution, [status(thm)], [c_52, c_4188])).
% 18.58/11.24  tff(c_44390, plain, (![A_606]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', A_606)=k2_xboole_0('#skF_2', A_606) | ~r1_tarski(A_606, u1_struct_0('#skF_1')))), inference(resolution, [status(thm)], [c_70, c_43731])).
% 18.58/11.24  tff(c_44402, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_37122, c_44390])).
% 18.58/11.24  tff(c_44548, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_381, c_4827, c_3739, c_44402])).
% 18.58/11.24  tff(c_44550, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4504, c_44548])).
% 18.58/11.24  tff(c_44551, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_76])).
% 18.58/11.24  tff(c_44794, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_44551])).
% 18.58/11.24  tff(c_44795, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_82])).
% 18.58/11.24  tff(c_44946, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44795, c_76])).
% 18.58/11.24  tff(c_47797, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_47652, c_44946])).
% 18.58/11.24  tff(c_48451, plain, (![A_763, B_764]: (r1_tarski(k2_tops_1(A_763, B_764), B_764) | ~v4_pre_topc(B_764, A_763) | ~m1_subset_1(B_764, k1_zfmisc_1(u1_struct_0(A_763))) | ~l1_pre_topc(A_763))), inference(cnfTransformation, [status(thm)], [f_150])).
% 18.58/11.24  tff(c_48462, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_70, c_48451])).
% 18.58/11.24  tff(c_48471, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_44795, c_48462])).
% 18.58/11.24  tff(c_50136, plain, (![A_808, B_809]: (k7_subset_1(u1_struct_0(A_808), B_809, k2_tops_1(A_808, B_809))=k1_tops_1(A_808, B_809) | ~m1_subset_1(B_809, k1_zfmisc_1(u1_struct_0(A_808))) | ~l1_pre_topc(A_808))), inference(cnfTransformation, [status(thm)], [f_157])).
% 18.58/11.24  tff(c_50147, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_70, c_50136])).
% 18.58/11.24  tff(c_50157, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_47652, c_50147])).
% 18.58/11.24  tff(c_46724, plain, (![A_714, B_715]: (k4_xboole_0(A_714, B_715)=k3_subset_1(A_714, B_715) | ~m1_subset_1(B_715, k1_zfmisc_1(A_714)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 18.58/11.24  tff(c_53340, plain, (![B_871, A_872]: (k4_xboole_0(B_871, A_872)=k3_subset_1(B_871, A_872) | ~r1_tarski(A_872, B_871))), inference(resolution, [status(thm)], [c_52, c_46724])).
% 18.58/11.24  tff(c_53469, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_48471, c_53340])).
% 18.58/11.24  tff(c_53558, plain, (k3_subset_1('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50157, c_53469])).
% 18.58/11.24  tff(c_46103, plain, (![A_694, B_695]: (k3_subset_1(A_694, k3_subset_1(A_694, B_695))=B_695 | ~m1_subset_1(B_695, k1_zfmisc_1(A_694)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 18.58/11.24  tff(c_46110, plain, (![B_48, A_47]: (k3_subset_1(B_48, k3_subset_1(B_48, A_47))=A_47 | ~r1_tarski(A_47, B_48))), inference(resolution, [status(thm)], [c_52, c_46103])).
% 18.58/11.24  tff(c_56074, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_53558, c_46110])).
% 18.58/11.24  tff(c_56082, plain, (k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48471, c_56074])).
% 18.58/11.24  tff(c_44797, plain, (![B_624, A_625]: (k2_xboole_0(B_624, A_625)=k2_xboole_0(A_625, B_624))), inference(cnfTransformation, [status(thm)], [f_27])).
% 18.58/11.24  tff(c_18, plain, (![A_14]: (k2_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_47])).
% 18.58/11.24  tff(c_44819, plain, (![A_625]: (k2_xboole_0(k1_xboole_0, A_625)=A_625)), inference(superposition, [status(thm), theory('equality')], [c_44797, c_18])).
% 18.58/11.24  tff(c_45176, plain, (![A_650, B_651]: (k2_xboole_0(A_650, k4_xboole_0(B_651, A_650))=k2_xboole_0(A_650, B_651))), inference(cnfTransformation, [status(thm)], [f_59])).
% 18.58/11.24  tff(c_45186, plain, (![B_651]: (k4_xboole_0(B_651, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_651))), inference(superposition, [status(thm), theory('equality')], [c_45176, c_44819])).
% 18.58/11.24  tff(c_45204, plain, (![B_651]: (k4_xboole_0(B_651, k1_xboole_0)=B_651)), inference(demodulation, [status(thm), theory('equality')], [c_44819, c_45186])).
% 18.58/11.24  tff(c_46, plain, (![A_44]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 18.58/11.24  tff(c_46736, plain, (![A_44]: (k4_xboole_0(A_44, k1_xboole_0)=k3_subset_1(A_44, k1_xboole_0))), inference(resolution, [status(thm)], [c_46, c_46724])).
% 18.58/11.24  tff(c_46741, plain, (![A_44]: (k3_subset_1(A_44, k1_xboole_0)=A_44)), inference(demodulation, [status(thm), theory('equality')], [c_45204, c_46736])).
% 18.58/11.24  tff(c_47884, plain, (![A_746, B_747]: (r1_tarski(k1_tops_1(A_746, B_747), B_747) | ~m1_subset_1(B_747, k1_zfmisc_1(u1_struct_0(A_746))) | ~l1_pre_topc(A_746))), inference(cnfTransformation, [status(thm)], [f_127])).
% 18.58/11.24  tff(c_47895, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_70, c_47884])).
% 18.58/11.24  tff(c_47904, plain, (r1_tarski(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_47895])).
% 18.58/11.24  tff(c_46926, plain, (![A_723, B_724, C_725]: (r1_tarski(k4_xboole_0(A_723, B_724), C_725) | ~r1_tarski(A_723, k2_xboole_0(B_724, C_725)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 18.58/11.24  tff(c_22, plain, (![A_18]: (r1_tarski(k1_xboole_0, A_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 18.58/11.24  tff(c_45500, plain, (![B_663, A_664]: (B_663=A_664 | ~r1_tarski(B_663, A_664) | ~r1_tarski(A_664, B_663))), inference(cnfTransformation, [status(thm)], [f_35])).
% 18.58/11.24  tff(c_45523, plain, (![A_18]: (k1_xboole_0=A_18 | ~r1_tarski(A_18, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_45500])).
% 18.58/11.24  tff(c_46935, plain, (![A_723, B_724]: (k4_xboole_0(A_723, B_724)=k1_xboole_0 | ~r1_tarski(A_723, k2_xboole_0(B_724, k1_xboole_0)))), inference(resolution, [status(thm)], [c_46926, c_45523])).
% 18.58/11.24  tff(c_46972, plain, (![A_723, B_724]: (k4_xboole_0(A_723, B_724)=k1_xboole_0 | ~r1_tarski(A_723, B_724))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_46935])).
% 18.58/11.24  tff(c_47916, plain, (k4_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_47904, c_46972])).
% 18.58/11.24  tff(c_32, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k4_xboole_0(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_67])).
% 18.58/11.24  tff(c_53508, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k4_xboole_0(A_19, B_20))=k3_subset_1(A_19, k4_xboole_0(A_19, B_20)))), inference(resolution, [status(thm)], [c_24, c_53340])).
% 18.58/11.24  tff(c_55952, plain, (![A_903, B_904]: (k3_subset_1(A_903, k4_xboole_0(A_903, B_904))=k3_xboole_0(A_903, B_904))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_53508])).
% 18.58/11.24  tff(c_56000, plain, (k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')=k3_subset_1(k1_tops_1('#skF_1', '#skF_2'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_47916, c_55952])).
% 18.58/11.24  tff(c_56054, plain, (k3_xboole_0(k1_tops_1('#skF_1', '#skF_2'), '#skF_2')=k1_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46741, c_56000])).
% 18.58/11.24  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 18.58/11.24  tff(c_45303, plain, (![A_654, B_655]: (k4_xboole_0(A_654, k3_xboole_0(A_654, B_655))=k4_xboole_0(A_654, B_655))), inference(cnfTransformation, [status(thm)], [f_65])).
% 18.58/11.24  tff(c_45341, plain, (![B_4, A_3]: (k4_xboole_0(B_4, k3_xboole_0(A_3, B_4))=k4_xboole_0(B_4, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_45303])).
% 18.58/11.24  tff(c_44997, plain, (![A_639, B_640]: (k4_xboole_0(A_639, k4_xboole_0(A_639, B_640))=k3_xboole_0(A_639, B_640))), inference(cnfTransformation, [status(thm)], [f_67])).
% 18.58/11.24  tff(c_45052, plain, (![A_642, B_643]: (r1_tarski(k3_xboole_0(A_642, B_643), A_642))), inference(superposition, [status(thm), theory('equality')], [c_44997, c_24])).
% 18.58/11.24  tff(c_45058, plain, (![B_4, A_3]: (r1_tarski(k3_xboole_0(B_4, A_3), A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_45052])).
% 18.58/11.24  tff(c_53493, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k3_xboole_0(B_4, A_3))=k3_subset_1(A_3, k3_xboole_0(B_4, A_3)))), inference(resolution, [status(thm)], [c_45058, c_53340])).
% 18.58/11.24  tff(c_53568, plain, (![A_3, B_4]: (k3_subset_1(A_3, k3_xboole_0(B_4, A_3))=k4_xboole_0(A_3, B_4))), inference(demodulation, [status(thm), theory('equality')], [c_45341, c_53493])).
% 18.58/11.24  tff(c_89389, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_2', k1_tops_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_56054, c_53568])).
% 18.58/11.24  tff(c_89509, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_56082, c_89389])).
% 18.58/11.24  tff(c_89511, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47797, c_89509])).
% 18.58/11.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.58/11.24  
% 18.58/11.24  Inference rules
% 18.58/11.24  ----------------------
% 18.58/11.24  #Ref     : 0
% 18.58/11.24  #Sup     : 22029
% 18.58/11.24  #Fact    : 0
% 18.58/11.24  #Define  : 0
% 18.58/11.24  #Split   : 9
% 18.58/11.24  #Chain   : 0
% 18.58/11.24  #Close   : 0
% 18.58/11.24  
% 18.58/11.24  Ordering : KBO
% 18.58/11.24  
% 18.58/11.24  Simplification rules
% 18.58/11.24  ----------------------
% 18.58/11.24  #Subsume      : 1399
% 18.58/11.24  #Demod        : 20433
% 18.58/11.24  #Tautology    : 14269
% 18.58/11.24  #SimpNegUnit  : 6
% 18.58/11.24  #BackRed      : 6
% 18.58/11.24  
% 18.58/11.24  #Partial instantiations: 0
% 18.58/11.24  #Strategies tried      : 1
% 18.58/11.24  
% 18.58/11.24  Timing (in seconds)
% 18.58/11.24  ----------------------
% 18.58/11.25  Preprocessing        : 0.37
% 18.58/11.25  Parsing              : 0.20
% 18.58/11.25  CNF conversion       : 0.03
% 18.58/11.25  Main loop            : 10.11
% 18.58/11.25  Inferencing          : 1.46
% 18.58/11.25  Reduction            : 5.82
% 18.58/11.25  Demodulation         : 5.12
% 18.58/11.25  BG Simplification    : 0.15
% 18.58/11.25  Subsumption          : 2.20
% 18.58/11.25  Abstraction          : 0.28
% 18.58/11.25  MUC search           : 0.00
% 18.58/11.25  Cooper               : 0.00
% 18.58/11.25  Total                : 10.52
% 18.58/11.25  Index Insertion      : 0.00
% 18.58/11.25  Index Deletion       : 0.00
% 18.58/11.25  Index Matching       : 0.00
% 18.58/11.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
