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
% DateTime   : Thu Dec  3 10:21:21 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 164 expanded)
%              Number of leaves         :   37 (  72 expanded)
%              Depth                    :    9
%              Number of atoms          :  141 ( 315 expanded)
%              Number of equality atoms :   57 ( 100 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tops_1,type,(
    k2_tops_1: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v4_pre_topc(B,A)
            <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k1_tops_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_pre_topc(A,B) = k4_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_51,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_tops_1(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => v4_pre_topc(k2_pre_topc(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v4_pre_topc(B,A)
           => r1_tarski(k2_tops_1(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_942,plain,(
    ! [A_125,B_126,C_127] :
      ( k7_subset_1(A_125,B_126,C_127) = k4_xboole_0(B_126,C_127)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(A_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_945,plain,(
    ! [C_127] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_127) = k4_xboole_0('#skF_2',C_127) ),
    inference(resolution,[status(thm)],[c_30,c_942])).

tff(c_36,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_121,plain,(
    ~ v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_32,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_598,plain,(
    ! [A_89,B_90] :
      ( k4_subset_1(u1_struct_0(A_89),B_90,k2_tops_1(A_89,B_90)) = k2_pre_topc(A_89,B_90)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_602,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_598])).

tff(c_606,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_602])).

tff(c_331,plain,(
    ! [A_63,B_64,C_65] :
      ( k7_subset_1(A_63,B_64,C_65) = k4_xboole_0(B_64,C_65)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_335,plain,(
    ! [C_66] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_66) = k4_xboole_0('#skF_2',C_66) ),
    inference(resolution,[status(thm)],[c_30,c_331])).

tff(c_42,plain,
    ( v4_pre_topc('#skF_2','#skF_1')
    | k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_282,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_42])).

tff(c_341,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_335,c_282])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_116,plain,(
    ! [A_45,B_46] :
      ( k3_xboole_0(A_45,B_46) = A_45
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_290,plain,(
    ! [A_59,B_60] : k3_xboole_0(k4_xboole_0(A_59,B_60),A_59) = k4_xboole_0(A_59,B_60) ),
    inference(resolution,[status(thm)],[c_8,c_116])).

tff(c_10,plain,(
    ! [B_10,A_9] : k2_tarski(B_10,A_9) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_101,plain,(
    ! [A_43,B_44] : k1_setfam_1(k2_tarski(A_43,B_44)) = k3_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_178,plain,(
    ! [B_51,A_52] : k1_setfam_1(k2_tarski(B_51,A_52)) = k3_xboole_0(A_52,B_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_101])).

tff(c_18,plain,(
    ! [A_19,B_20] : k1_setfam_1(k2_tarski(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_210,plain,(
    ! [B_55,A_56] : k3_xboole_0(B_55,A_56) = k3_xboole_0(A_56,B_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_18])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_234,plain,(
    ! [B_55,A_56] : k2_xboole_0(B_55,k3_xboole_0(A_56,B_55)) = B_55 ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_4])).

tff(c_296,plain,(
    ! [A_59,B_60] : k2_xboole_0(A_59,k4_xboole_0(A_59,B_60)) = A_59 ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_234])).

tff(c_353,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_296])).

tff(c_20,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(k2_tops_1(A_21,B_22),k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(u1_struct_0(A_21)))
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_576,plain,(
    ! [A_83,B_84,C_85] :
      ( k4_subset_1(A_83,B_84,C_85) = k2_xboole_0(B_84,C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(A_83))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_679,plain,(
    ! [A_103,B_104,B_105] :
      ( k4_subset_1(u1_struct_0(A_103),B_104,k2_tops_1(A_103,B_105)) = k2_xboole_0(B_104,k2_tops_1(A_103,B_105))
      | ~ m1_subset_1(B_104,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0(A_103)))
      | ~ l1_pre_topc(A_103) ) ),
    inference(resolution,[status(thm)],[c_20,c_576])).

tff(c_683,plain,(
    ! [B_105] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_105)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_105))
      | ~ m1_subset_1(B_105,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_679])).

tff(c_688,plain,(
    ! [B_106] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_106)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_106))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_683])).

tff(c_695,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_688])).

tff(c_700,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_606,c_353,c_695])).

tff(c_34,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_511,plain,(
    ! [A_75,B_76] :
      ( v4_pre_topc(k2_pre_topc(A_75,B_76),A_75)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(u1_struct_0(A_75)))
      | ~ l1_pre_topc(A_75)
      | ~ v2_pre_topc(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_515,plain,
    ( v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_511])).

tff(c_519,plain,(
    v4_pre_topc(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_515])).

tff(c_702,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_700,c_519])).

tff(c_704,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_702])).

tff(c_705,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_946,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) != k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_945,c_705])).

tff(c_1128,plain,(
    ! [A_148,B_149] :
      ( k4_subset_1(u1_struct_0(A_148),B_149,k2_tops_1(A_148,B_149)) = k2_pre_topc(A_148,B_149)
      | ~ m1_subset_1(B_149,k1_zfmisc_1(u1_struct_0(A_148)))
      | ~ l1_pre_topc(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1132,plain,
    ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1128])).

tff(c_1136,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1132])).

tff(c_706,plain,(
    v4_pre_topc('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1046,plain,(
    ! [A_145,B_146] :
      ( r1_tarski(k2_tops_1(A_145,B_146),B_146)
      | ~ v4_pre_topc(B_146,A_145)
      | ~ m1_subset_1(B_146,k1_zfmisc_1(u1_struct_0(A_145)))
      | ~ l1_pre_topc(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1050,plain,
    ( r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2')
    | ~ v4_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_1046])).

tff(c_1054,plain,(
    r1_tarski(k2_tops_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_706,c_1050])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1058,plain,(
    k3_xboole_0(k2_tops_1('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_1054,c_6])).

tff(c_708,plain,(
    ! [A_107,B_108] : k1_setfam_1(k2_tarski(A_107,B_108)) = k3_xboole_0(B_108,A_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_101])).

tff(c_731,plain,(
    ! [B_109,A_110] : k3_xboole_0(B_109,A_110) = k3_xboole_0(A_110,B_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_708,c_18])).

tff(c_749,plain,(
    ! [B_109,A_110] : k2_xboole_0(B_109,k3_xboole_0(A_110,B_109)) = B_109 ),
    inference(superposition,[status(thm),theory(equality)],[c_731,c_4])).

tff(c_1068,plain,(
    k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1058,c_749])).

tff(c_1014,plain,(
    ! [A_139,B_140,C_141] :
      ( k4_subset_1(A_139,B_140,C_141) = k2_xboole_0(B_140,C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(A_139))
      | ~ m1_subset_1(B_140,k1_zfmisc_1(A_139)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1217,plain,(
    ! [A_166,B_167,B_168] :
      ( k4_subset_1(u1_struct_0(A_166),B_167,k2_tops_1(A_166,B_168)) = k2_xboole_0(B_167,k2_tops_1(A_166,B_168))
      | ~ m1_subset_1(B_167,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ m1_subset_1(B_168,k1_zfmisc_1(u1_struct_0(A_166)))
      | ~ l1_pre_topc(A_166) ) ),
    inference(resolution,[status(thm)],[c_20,c_1014])).

tff(c_1221,plain,(
    ! [B_168] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_168)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_168))
      | ~ m1_subset_1(B_168,k1_zfmisc_1(u1_struct_0('#skF_1')))
      | ~ l1_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_30,c_1217])).

tff(c_1226,plain,(
    ! [B_169] :
      ( k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1',B_169)) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1',B_169))
      | ~ m1_subset_1(B_169,k1_zfmisc_1(u1_struct_0('#skF_1'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1221])).

tff(c_1233,plain,(
    k4_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_1226])).

tff(c_1238,plain,(
    k2_pre_topc('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1136,c_1068,c_1233])).

tff(c_24,plain,(
    ! [A_25,B_27] :
      ( k7_subset_1(u1_struct_0(A_25),k2_pre_topc(A_25,B_27),k1_tops_1(A_25,B_27)) = k2_tops_1(A_25,B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(u1_struct_0(A_25)))
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1245,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1238,c_24])).

tff(c_1249,plain,(
    k4_xboole_0('#skF_2',k1_tops_1('#skF_1','#skF_2')) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_945,c_1245])).

tff(c_1251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_946,c_1249])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:11:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.21/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.48  
% 3.21/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.48  %$ v4_pre_topc > r1_tarski > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tops_1 > k2_tarski > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > #skF_2 > #skF_1
% 3.21/1.48  
% 3.21/1.48  %Foreground sorts:
% 3.21/1.48  
% 3.21/1.48  
% 3.21/1.48  %Background operators:
% 3.21/1.48  
% 3.21/1.48  
% 3.21/1.48  %Foreground operators:
% 3.21/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.21/1.48  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 3.21/1.48  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.21/1.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.21/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.21/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.21/1.48  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.21/1.48  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 3.21/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.21/1.48  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.21/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.21/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.21/1.48  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 3.21/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.48  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.21/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.48  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.21/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.21/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.21/1.48  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.21/1.48  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 3.21/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.21/1.48  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.21/1.48  
% 3.21/1.49  tff(f_100, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k1_tops_1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tops_1)).
% 3.21/1.49  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.21/1.49  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_pre_topc(A, B) = k4_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tops_1)).
% 3.21/1.49  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.21/1.49  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.21/1.49  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.21/1.49  tff(f_51, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.21/1.49  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 3.21/1.49  tff(f_57, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_tops_1(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tops_1)).
% 3.21/1.49  tff(f_45, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.21/1.49  tff(f_65, axiom, (![A, B]: (((v2_pre_topc(A) & l1_pre_topc(A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => v4_pre_topc(k2_pre_topc(A, B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_tops_1)).
% 3.21/1.49  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v4_pre_topc(B, A) => r1_tarski(k2_tops_1(A, B), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_tops_1)).
% 3.21/1.49  tff(f_72, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l78_tops_1)).
% 3.21/1.49  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.21/1.49  tff(c_942, plain, (![A_125, B_126, C_127]: (k7_subset_1(A_125, B_126, C_127)=k4_xboole_0(B_126, C_127) | ~m1_subset_1(B_126, k1_zfmisc_1(A_125)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.21/1.49  tff(c_945, plain, (![C_127]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_127)=k4_xboole_0('#skF_2', C_127))), inference(resolution, [status(thm)], [c_30, c_942])).
% 3.21/1.49  tff(c_36, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.21/1.49  tff(c_121, plain, (~v4_pre_topc('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_36])).
% 3.21/1.49  tff(c_32, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.21/1.49  tff(c_598, plain, (![A_89, B_90]: (k4_subset_1(u1_struct_0(A_89), B_90, k2_tops_1(A_89, B_90))=k2_pre_topc(A_89, B_90) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.21/1.49  tff(c_602, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_598])).
% 3.21/1.49  tff(c_606, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_602])).
% 3.21/1.49  tff(c_331, plain, (![A_63, B_64, C_65]: (k7_subset_1(A_63, B_64, C_65)=k4_xboole_0(B_64, C_65) | ~m1_subset_1(B_64, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.21/1.49  tff(c_335, plain, (![C_66]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_66)=k4_xboole_0('#skF_2', C_66))), inference(resolution, [status(thm)], [c_30, c_331])).
% 3.21/1.49  tff(c_42, plain, (v4_pre_topc('#skF_2', '#skF_1') | k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.21/1.49  tff(c_282, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_121, c_42])).
% 3.21/1.49  tff(c_341, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_335, c_282])).
% 3.21/1.49  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.21/1.49  tff(c_116, plain, (![A_45, B_46]: (k3_xboole_0(A_45, B_46)=A_45 | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.21/1.49  tff(c_290, plain, (![A_59, B_60]: (k3_xboole_0(k4_xboole_0(A_59, B_60), A_59)=k4_xboole_0(A_59, B_60))), inference(resolution, [status(thm)], [c_8, c_116])).
% 3.21/1.49  tff(c_10, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.21/1.49  tff(c_101, plain, (![A_43, B_44]: (k1_setfam_1(k2_tarski(A_43, B_44))=k3_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.21/1.49  tff(c_178, plain, (![B_51, A_52]: (k1_setfam_1(k2_tarski(B_51, A_52))=k3_xboole_0(A_52, B_51))), inference(superposition, [status(thm), theory('equality')], [c_10, c_101])).
% 3.21/1.49  tff(c_18, plain, (![A_19, B_20]: (k1_setfam_1(k2_tarski(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.21/1.49  tff(c_210, plain, (![B_55, A_56]: (k3_xboole_0(B_55, A_56)=k3_xboole_0(A_56, B_55))), inference(superposition, [status(thm), theory('equality')], [c_178, c_18])).
% 3.21/1.49  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k3_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.21/1.49  tff(c_234, plain, (![B_55, A_56]: (k2_xboole_0(B_55, k3_xboole_0(A_56, B_55))=B_55)), inference(superposition, [status(thm), theory('equality')], [c_210, c_4])).
% 3.21/1.49  tff(c_296, plain, (![A_59, B_60]: (k2_xboole_0(A_59, k4_xboole_0(A_59, B_60))=A_59)), inference(superposition, [status(thm), theory('equality')], [c_290, c_234])).
% 3.21/1.49  tff(c_353, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_341, c_296])).
% 3.21/1.49  tff(c_20, plain, (![A_21, B_22]: (m1_subset_1(k2_tops_1(A_21, B_22), k1_zfmisc_1(u1_struct_0(A_21))) | ~m1_subset_1(B_22, k1_zfmisc_1(u1_struct_0(A_21))) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.21/1.49  tff(c_576, plain, (![A_83, B_84, C_85]: (k4_subset_1(A_83, B_84, C_85)=k2_xboole_0(B_84, C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(A_83)) | ~m1_subset_1(B_84, k1_zfmisc_1(A_83)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.21/1.49  tff(c_679, plain, (![A_103, B_104, B_105]: (k4_subset_1(u1_struct_0(A_103), B_104, k2_tops_1(A_103, B_105))=k2_xboole_0(B_104, k2_tops_1(A_103, B_105)) | ~m1_subset_1(B_104, k1_zfmisc_1(u1_struct_0(A_103))) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0(A_103))) | ~l1_pre_topc(A_103))), inference(resolution, [status(thm)], [c_20, c_576])).
% 3.21/1.49  tff(c_683, plain, (![B_105]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_105))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_105)) | ~m1_subset_1(B_105, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_679])).
% 3.21/1.49  tff(c_688, plain, (![B_106]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_106))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_106)) | ~m1_subset_1(B_106, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_683])).
% 3.21/1.49  tff(c_695, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_688])).
% 3.21/1.49  tff(c_700, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_606, c_353, c_695])).
% 3.21/1.49  tff(c_34, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.21/1.49  tff(c_511, plain, (![A_75, B_76]: (v4_pre_topc(k2_pre_topc(A_75, B_76), A_75) | ~m1_subset_1(B_76, k1_zfmisc_1(u1_struct_0(A_75))) | ~l1_pre_topc(A_75) | ~v2_pre_topc(A_75))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.21/1.49  tff(c_515, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_511])).
% 3.21/1.49  tff(c_519, plain, (v4_pre_topc(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_515])).
% 3.21/1.49  tff(c_702, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_700, c_519])).
% 3.21/1.49  tff(c_704, plain, $false, inference(negUnitSimplification, [status(thm)], [c_121, c_702])).
% 3.21/1.49  tff(c_705, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_36])).
% 3.21/1.49  tff(c_946, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))!=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_945, c_705])).
% 3.21/1.49  tff(c_1128, plain, (![A_148, B_149]: (k4_subset_1(u1_struct_0(A_148), B_149, k2_tops_1(A_148, B_149))=k2_pre_topc(A_148, B_149) | ~m1_subset_1(B_149, k1_zfmisc_1(u1_struct_0(A_148))) | ~l1_pre_topc(A_148))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.21/1.49  tff(c_1132, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1128])).
% 3.21/1.49  tff(c_1136, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1132])).
% 3.21/1.49  tff(c_706, plain, (v4_pre_topc('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_36])).
% 3.21/1.49  tff(c_1046, plain, (![A_145, B_146]: (r1_tarski(k2_tops_1(A_145, B_146), B_146) | ~v4_pre_topc(B_146, A_145) | ~m1_subset_1(B_146, k1_zfmisc_1(u1_struct_0(A_145))) | ~l1_pre_topc(A_145))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.21/1.49  tff(c_1050, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2') | ~v4_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_1046])).
% 3.21/1.49  tff(c_1054, plain, (r1_tarski(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_706, c_1050])).
% 3.21/1.49  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.21/1.49  tff(c_1058, plain, (k3_xboole_0(k2_tops_1('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_1054, c_6])).
% 3.21/1.49  tff(c_708, plain, (![A_107, B_108]: (k1_setfam_1(k2_tarski(A_107, B_108))=k3_xboole_0(B_108, A_107))), inference(superposition, [status(thm), theory('equality')], [c_10, c_101])).
% 3.21/1.49  tff(c_731, plain, (![B_109, A_110]: (k3_xboole_0(B_109, A_110)=k3_xboole_0(A_110, B_109))), inference(superposition, [status(thm), theory('equality')], [c_708, c_18])).
% 3.21/1.49  tff(c_749, plain, (![B_109, A_110]: (k2_xboole_0(B_109, k3_xboole_0(A_110, B_109))=B_109)), inference(superposition, [status(thm), theory('equality')], [c_731, c_4])).
% 3.21/1.49  tff(c_1068, plain, (k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1058, c_749])).
% 3.21/1.49  tff(c_1014, plain, (![A_139, B_140, C_141]: (k4_subset_1(A_139, B_140, C_141)=k2_xboole_0(B_140, C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(A_139)) | ~m1_subset_1(B_140, k1_zfmisc_1(A_139)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.21/1.49  tff(c_1217, plain, (![A_166, B_167, B_168]: (k4_subset_1(u1_struct_0(A_166), B_167, k2_tops_1(A_166, B_168))=k2_xboole_0(B_167, k2_tops_1(A_166, B_168)) | ~m1_subset_1(B_167, k1_zfmisc_1(u1_struct_0(A_166))) | ~m1_subset_1(B_168, k1_zfmisc_1(u1_struct_0(A_166))) | ~l1_pre_topc(A_166))), inference(resolution, [status(thm)], [c_20, c_1014])).
% 3.21/1.49  tff(c_1221, plain, (![B_168]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_168))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_168)) | ~m1_subset_1(B_168, k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_1217])).
% 3.21/1.49  tff(c_1226, plain, (![B_169]: (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', B_169))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', B_169)) | ~m1_subset_1(B_169, k1_zfmisc_1(u1_struct_0('#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1221])).
% 3.21/1.49  tff(c_1233, plain, (k4_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_1226])).
% 3.21/1.49  tff(c_1238, plain, (k2_pre_topc('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1136, c_1068, c_1233])).
% 3.21/1.49  tff(c_24, plain, (![A_25, B_27]: (k7_subset_1(u1_struct_0(A_25), k2_pre_topc(A_25, B_27), k1_tops_1(A_25, B_27))=k2_tops_1(A_25, B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(u1_struct_0(A_25))) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.21/1.49  tff(c_1245, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1238, c_24])).
% 3.21/1.49  tff(c_1249, plain, (k4_xboole_0('#skF_2', k1_tops_1('#skF_1', '#skF_2'))=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_945, c_1245])).
% 3.21/1.49  tff(c_1251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_946, c_1249])).
% 3.21/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.49  
% 3.21/1.49  Inference rules
% 3.21/1.49  ----------------------
% 3.21/1.49  #Ref     : 0
% 3.21/1.49  #Sup     : 303
% 3.21/1.49  #Fact    : 0
% 3.21/1.49  #Define  : 0
% 3.21/1.49  #Split   : 1
% 3.21/1.49  #Chain   : 0
% 3.21/1.49  #Close   : 0
% 3.21/1.49  
% 3.21/1.49  Ordering : KBO
% 3.21/1.50  
% 3.21/1.50  Simplification rules
% 3.21/1.50  ----------------------
% 3.21/1.50  #Subsume      : 9
% 3.21/1.50  #Demod        : 113
% 3.21/1.50  #Tautology    : 222
% 3.21/1.50  #SimpNegUnit  : 3
% 3.21/1.50  #BackRed      : 5
% 3.21/1.50  
% 3.21/1.50  #Partial instantiations: 0
% 3.21/1.50  #Strategies tried      : 1
% 3.21/1.50  
% 3.21/1.50  Timing (in seconds)
% 3.21/1.50  ----------------------
% 3.21/1.50  Preprocessing        : 0.32
% 3.21/1.50  Parsing              : 0.17
% 3.21/1.50  CNF conversion       : 0.02
% 3.21/1.50  Main loop            : 0.41
% 3.21/1.50  Inferencing          : 0.16
% 3.21/1.50  Reduction            : 0.14
% 3.21/1.50  Demodulation         : 0.11
% 3.21/1.50  BG Simplification    : 0.02
% 3.21/1.50  Subsumption          : 0.06
% 3.21/1.50  Abstraction          : 0.02
% 3.21/1.50  MUC search           : 0.00
% 3.21/1.50  Cooper               : 0.00
% 3.21/1.50  Total                : 0.76
% 3.21/1.50  Index Insertion      : 0.00
% 3.21/1.50  Index Deletion       : 0.00
% 3.21/1.50  Index Matching       : 0.00
% 3.21/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
