%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:10 EST 2020

% Result     : Theorem 4.20s
% Output     : CNFRefutation 4.20s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 569 expanded)
%              Number of leaves         :   33 ( 218 expanded)
%              Depth                    :   15
%              Number of atoms          :  163 (1387 expanded)
%              Number of equality atoms :   68 ( 380 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tops_1 > v3_pre_topc > v2_tops_1 > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

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

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ( v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( ( v3_pre_topc(B,A)
                & v3_tops_1(B,A) )
             => B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_tops_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => m1_subset_1(k2_pre_topc(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
          <=> v2_tops_1(k2_pre_topc(A,B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_1)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v2_tops_1(B,A)
          <=> k1_tops_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),k1_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tops_1(B,A)
           => v2_tops_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => k1_tops_1(A,B) = k7_subset_1(u1_struct_0(A),B,k2_tops_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_pre_topc(B,A)
          <=> k2_tops_1(A,B) = k7_subset_1(u1_struct_0(A),k2_pre_topc(A,B),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_6,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_40,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(k2_pre_topc(A_10,B_11),k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ m1_subset_1(B_11,k1_zfmisc_1(u1_struct_0(A_10)))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_36,plain,(
    v3_tops_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_602,plain,(
    ! [A_67,B_68] :
      ( v2_tops_1(k2_pre_topc(A_67,B_68),A_67)
      | ~ v3_tops_1(B_68,A_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(u1_struct_0(A_67)))
      | ~ l1_pre_topc(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_606,plain,
    ( v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_602])).

tff(c_610,plain,(
    v2_tops_1(k2_pre_topc('#skF_1','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36,c_606])).

tff(c_517,plain,(
    ! [A_61,B_62] :
      ( m1_subset_1(k2_pre_topc(A_61,B_62),k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ m1_subset_1(B_62,k1_zfmisc_1(u1_struct_0(A_61)))
      | ~ l1_pre_topc(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_30,plain,(
    ! [A_27,B_29] :
      ( k1_tops_1(A_27,B_29) = k1_xboole_0
      | ~ v2_tops_1(B_29,A_27)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(u1_struct_0(A_27)))
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1197,plain,(
    ! [A_89,B_90] :
      ( k1_tops_1(A_89,k2_pre_topc(A_89,B_90)) = k1_xboole_0
      | ~ v2_tops_1(k2_pre_topc(A_89,B_90),A_89)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ l1_pre_topc(A_89) ) ),
    inference(resolution,[status(thm)],[c_517,c_30])).

tff(c_1201,plain,
    ( k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_xboole_0
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_610,c_1197])).

tff(c_1206,plain,(
    k1_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1201])).

tff(c_18,plain,(
    ! [A_15,B_17] :
      ( k7_subset_1(u1_struct_0(A_15),k2_pre_topc(A_15,B_17),k1_tops_1(A_15,B_17)) = k2_tops_1(A_15,B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(u1_struct_0(A_15)))
      | ~ l1_pre_topc(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1212,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_xboole_0) = k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1206,c_18])).

tff(c_1216,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1',k2_pre_topc('#skF_1','#skF_2')),k1_xboole_0) = k2_tops_1('#skF_1',k2_pre_topc('#skF_1','#skF_2'))
    | ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1212])).

tff(c_1504,plain,(
    ~ m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1216])).

tff(c_1507,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_1504])).

tff(c_1511,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1507])).

tff(c_1513,plain,(
    m1_subset_1(k2_pre_topc('#skF_1','#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_1216])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9] :
      ( k7_subset_1(A_7,B_8,C_9) = k4_xboole_0(B_8,C_9)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1577,plain,(
    ! [C_101] : k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),C_101) = k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),C_101) ),
    inference(resolution,[status(thm)],[c_1513,c_10])).

tff(c_256,plain,(
    ! [B_49,A_50] :
      ( v2_tops_1(B_49,A_50)
      | ~ v3_tops_1(B_49,A_50)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(u1_struct_0(A_50)))
      | ~ l1_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_259,plain,
    ( v2_tops_1('#skF_2','#skF_1')
    | ~ v3_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_256])).

tff(c_262,plain,(
    v2_tops_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36,c_259])).

tff(c_356,plain,(
    ! [A_55,B_56] :
      ( k1_tops_1(A_55,B_56) = k1_xboole_0
      | ~ v2_tops_1(B_56,A_55)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_pre_topc(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_359,plain,
    ( k1_tops_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v2_tops_1('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_356])).

tff(c_362,plain,(
    k1_tops_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_262,c_359])).

tff(c_993,plain,(
    ! [A_79,B_80] :
      ( k7_subset_1(u1_struct_0(A_79),k2_pre_topc(A_79,B_80),k1_tops_1(A_79,B_80)) = k2_tops_1(A_79,B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0(A_79)))
      | ~ l1_pre_topc(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1002,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k1_xboole_0) = k2_tops_1('#skF_1','#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ l1_pre_topc('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_993])).

tff(c_1006,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),k1_xboole_0) = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_1002])).

tff(c_1592,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k1_xboole_0) = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1577,c_1006])).

tff(c_1616,plain,(
    k2_tops_1('#skF_1','#skF_2') = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1592])).

tff(c_184,plain,(
    ! [A_42,B_43,C_44] :
      ( k7_subset_1(A_42,B_43,C_44) = k4_xboole_0(B_43,C_44)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_187,plain,(
    ! [C_44] : k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',C_44) = k4_xboole_0('#skF_2',C_44) ),
    inference(resolution,[status(thm)],[c_40,c_184])).

tff(c_696,plain,(
    ! [A_73,B_74] :
      ( k7_subset_1(u1_struct_0(A_73),B_74,k2_tops_1(A_73,B_74)) = k1_tops_1(A_73,B_74)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0(A_73)))
      | ~ l1_pre_topc(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_700,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),'#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_tops_1('#skF_1','#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_696])).

tff(c_704,plain,(
    k4_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_362,c_187,c_700])).

tff(c_8,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k4_xboole_0(A_5,B_6)) = k3_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_714,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = k4_xboole_0('#skF_2',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_704,c_8])).

tff(c_719,plain,(
    k3_xboole_0('#skF_2',k2_tops_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_714])).

tff(c_1627,plain,(
    k3_xboole_0('#skF_2',k2_pre_topc('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1616,c_719])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_108,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k4_xboole_0(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_226,plain,(
    ! [A_47,B_48] : k4_xboole_0(A_47,k3_xboole_0(A_47,B_48)) = k3_xboole_0(A_47,k4_xboole_0(A_47,B_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_8])).

tff(c_264,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k3_xboole_0(B_52,A_51)) = k3_xboole_0(A_51,k4_xboole_0(A_51,B_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_226])).

tff(c_367,plain,(
    ! [A_57,B_58] : k4_xboole_0(A_57,k3_xboole_0(A_57,k4_xboole_0(A_57,B_58))) = k3_xboole_0(A_57,k3_xboole_0(B_58,A_57)) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_8])).

tff(c_232,plain,(
    ! [A_47,B_48] : k4_xboole_0(A_47,k3_xboole_0(A_47,k4_xboole_0(A_47,B_48))) = k3_xboole_0(A_47,k3_xboole_0(A_47,B_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_8])).

tff(c_379,plain,(
    ! [A_57,B_58] : k3_xboole_0(A_57,k3_xboole_0(B_58,A_57)) = k3_xboole_0(A_57,k3_xboole_0(A_57,B_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_232])).

tff(c_61,plain,(
    ! [B_36,A_37] : k3_xboole_0(B_36,A_37) = k3_xboole_0(A_37,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_77,plain,(
    ! [A_37] : k3_xboole_0(k1_xboole_0,A_37) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_4])).

tff(c_123,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k3_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_108])).

tff(c_126,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_123])).

tff(c_244,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k3_xboole_0(A_1,k4_xboole_0(A_1,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_226])).

tff(c_161,plain,(
    ! [A_41] : k4_xboole_0(A_41,A_41) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_123])).

tff(c_166,plain,(
    ! [A_41] : k4_xboole_0(A_41,k1_xboole_0) = k3_xboole_0(A_41,A_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_8])).

tff(c_178,plain,(
    ! [A_41] : k3_xboole_0(A_41,A_41) = A_41 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_166])).

tff(c_307,plain,(
    ! [A_53,B_54] : k4_xboole_0(A_53,k3_xboole_0(A_53,k4_xboole_0(A_53,B_54))) = k3_xboole_0(A_53,k3_xboole_0(A_53,B_54)) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_8])).

tff(c_771,plain,(
    ! [A_75,B_76] : k4_xboole_0(A_75,k3_xboole_0(A_75,k3_xboole_0(A_75,k4_xboole_0(A_75,B_76)))) = k3_xboole_0(A_75,k3_xboole_0(A_75,k3_xboole_0(B_76,A_75))) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_307])).

tff(c_345,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k3_xboole_0(A_5,k3_xboole_0(A_5,B_6))) = k3_xboole_0(A_5,k3_xboole_0(A_5,k4_xboole_0(A_5,B_6))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_307])).

tff(c_780,plain,(
    ! [A_75,B_76] : k3_xboole_0(A_75,k3_xboole_0(A_75,k4_xboole_0(A_75,k4_xboole_0(A_75,B_76)))) = k3_xboole_0(A_75,k3_xboole_0(A_75,k3_xboole_0(B_76,A_75))) ),
    inference(superposition,[status(thm),theory(equality)],[c_771,c_345])).

tff(c_850,plain,(
    ! [A_75,B_76] : k3_xboole_0(A_75,k3_xboole_0(A_75,k3_xboole_0(B_76,A_75))) = k3_xboole_0(A_75,k3_xboole_0(A_75,k3_xboole_0(A_75,B_76))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_780])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_38,plain,(
    v3_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1218,plain,(
    ! [A_91,B_92] :
      ( k7_subset_1(u1_struct_0(A_91),k2_pre_topc(A_91,B_92),B_92) = k2_tops_1(A_91,B_92)
      | ~ v3_pre_topc(B_92,A_91)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(u1_struct_0(A_91)))
      | ~ l1_pre_topc(A_91)
      | ~ v2_pre_topc(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1222,plain,
    ( k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2')
    | ~ v3_pre_topc('#skF_2','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_1218])).

tff(c_1226,plain,(
    k7_subset_1(u1_struct_0('#skF_1'),k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_38,c_1222])).

tff(c_1589,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_tops_1('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1577,c_1226])).

tff(c_1688,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2') = k2_pre_topc('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1616,c_1589])).

tff(c_111,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k3_xboole_0(A_38,B_39)) = k3_xboole_0(A_38,k4_xboole_0(A_38,B_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_8])).

tff(c_331,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k3_xboole_0(A_38,k3_xboole_0(A_38,k4_xboole_0(A_38,B_39)))) = k3_xboole_0(A_38,k3_xboole_0(A_38,k3_xboole_0(A_38,B_39))) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_307])).

tff(c_1692,plain,(
    k4_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k3_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k3_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k2_pre_topc('#skF_1','#skF_2')))) = k3_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k3_xboole_0(k2_pre_topc('#skF_1','#skF_2'),k3_xboole_0(k2_pre_topc('#skF_1','#skF_2'),'#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1688,c_331])).

tff(c_1707,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1627,c_2,c_1627,c_379,c_1627,c_77,c_2,c_126,c_244,c_178,c_850,c_1692])).

tff(c_1709,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1707])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:44:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.20/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.20/1.72  
% 4.20/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.20/1.72  %$ v3_tops_1 > v3_pre_topc > v2_tops_1 > m1_subset_1 > v2_pre_topc > l1_pre_topc > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tops_1 > k2_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.20/1.72  
% 4.20/1.72  %Foreground sorts:
% 4.20/1.72  
% 4.20/1.72  
% 4.20/1.72  %Background operators:
% 4.20/1.72  
% 4.20/1.72  
% 4.20/1.72  %Foreground operators:
% 4.20/1.72  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.20/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.20/1.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.20/1.72  tff(k2_tops_1, type, k2_tops_1: ($i * $i) > $i).
% 4.20/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.20/1.72  tff(v2_tops_1, type, v2_tops_1: ($i * $i) > $o).
% 4.20/1.72  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.20/1.72  tff(v3_tops_1, type, v3_tops_1: ($i * $i) > $o).
% 4.20/1.72  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.20/1.72  tff('#skF_2', type, '#skF_2': $i).
% 4.20/1.72  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.20/1.72  tff('#skF_1', type, '#skF_1': $i).
% 4.20/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.20/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.20/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.20/1.72  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.20/1.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.20/1.72  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.20/1.72  tff(k2_pre_topc, type, k2_pre_topc: ($i * $i) > $i).
% 4.20/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.20/1.72  
% 4.20/1.74  tff(f_118, negated_conjecture, ~(![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => ((v3_pre_topc(B, A) & v3_tops_1(B, A)) => (B = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_tops_1)).
% 4.20/1.74  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 4.20/1.74  tff(f_43, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => m1_subset_1(k2_pre_topc(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_pre_topc)).
% 4.20/1.74  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) <=> v2_tops_1(k2_pre_topc(A, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tops_1)).
% 4.20/1.74  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v2_tops_1(B, A) <=> (k1_tops_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tops_1)).
% 4.20/1.74  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), k1_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l78_tops_1)).
% 4.20/1.74  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.20/1.74  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tops_1(B, A) => v2_tops_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_tops_1)).
% 4.20/1.74  tff(f_75, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (k1_tops_1(A, B) = k7_subset_1(u1_struct_0(A), B, k2_tops_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tops_1)).
% 4.20/1.74  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.20/1.74  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.20/1.74  tff(f_29, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 4.20/1.74  tff(f_86, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_pre_topc(B, A) <=> (k2_tops_1(A, B) = k7_subset_1(u1_struct_0(A), k2_pre_topc(A, B), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_tops_1)).
% 4.20/1.74  tff(c_34, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.20/1.74  tff(c_6, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.20/1.74  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.20/1.74  tff(c_40, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.20/1.74  tff(c_12, plain, (![A_10, B_11]: (m1_subset_1(k2_pre_topc(A_10, B_11), k1_zfmisc_1(u1_struct_0(A_10))) | ~m1_subset_1(B_11, k1_zfmisc_1(u1_struct_0(A_10))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.20/1.74  tff(c_36, plain, (v3_tops_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.20/1.74  tff(c_602, plain, (![A_67, B_68]: (v2_tops_1(k2_pre_topc(A_67, B_68), A_67) | ~v3_tops_1(B_68, A_67) | ~m1_subset_1(B_68, k1_zfmisc_1(u1_struct_0(A_67))) | ~l1_pre_topc(A_67))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.20/1.74  tff(c_606, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_602])).
% 4.20/1.74  tff(c_610, plain, (v2_tops_1(k2_pre_topc('#skF_1', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36, c_606])).
% 4.20/1.74  tff(c_517, plain, (![A_61, B_62]: (m1_subset_1(k2_pre_topc(A_61, B_62), k1_zfmisc_1(u1_struct_0(A_61))) | ~m1_subset_1(B_62, k1_zfmisc_1(u1_struct_0(A_61))) | ~l1_pre_topc(A_61))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.20/1.74  tff(c_30, plain, (![A_27, B_29]: (k1_tops_1(A_27, B_29)=k1_xboole_0 | ~v2_tops_1(B_29, A_27) | ~m1_subset_1(B_29, k1_zfmisc_1(u1_struct_0(A_27))) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.20/1.74  tff(c_1197, plain, (![A_89, B_90]: (k1_tops_1(A_89, k2_pre_topc(A_89, B_90))=k1_xboole_0 | ~v2_tops_1(k2_pre_topc(A_89, B_90), A_89) | ~m1_subset_1(B_90, k1_zfmisc_1(u1_struct_0(A_89))) | ~l1_pre_topc(A_89))), inference(resolution, [status(thm)], [c_517, c_30])).
% 4.20/1.74  tff(c_1201, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_xboole_0 | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_610, c_1197])).
% 4.20/1.74  tff(c_1206, plain, (k1_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1201])).
% 4.20/1.74  tff(c_18, plain, (![A_15, B_17]: (k7_subset_1(u1_struct_0(A_15), k2_pre_topc(A_15, B_17), k1_tops_1(A_15, B_17))=k2_tops_1(A_15, B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(u1_struct_0(A_15))) | ~l1_pre_topc(A_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.20/1.74  tff(c_1212, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_xboole_0)=k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1206, c_18])).
% 4.20/1.74  tff(c_1216, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', k2_pre_topc('#skF_1', '#skF_2')), k1_xboole_0)=k2_tops_1('#skF_1', k2_pre_topc('#skF_1', '#skF_2')) | ~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1212])).
% 4.20/1.74  tff(c_1504, plain, (~m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitLeft, [status(thm)], [c_1216])).
% 4.20/1.74  tff(c_1507, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_12, c_1504])).
% 4.20/1.74  tff(c_1511, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1507])).
% 4.20/1.74  tff(c_1513, plain, (m1_subset_1(k2_pre_topc('#skF_1', '#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(splitRight, [status(thm)], [c_1216])).
% 4.20/1.74  tff(c_10, plain, (![A_7, B_8, C_9]: (k7_subset_1(A_7, B_8, C_9)=k4_xboole_0(B_8, C_9) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.20/1.74  tff(c_1577, plain, (![C_101]: (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), C_101)=k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), C_101))), inference(resolution, [status(thm)], [c_1513, c_10])).
% 4.20/1.74  tff(c_256, plain, (![B_49, A_50]: (v2_tops_1(B_49, A_50) | ~v3_tops_1(B_49, A_50) | ~m1_subset_1(B_49, k1_zfmisc_1(u1_struct_0(A_50))) | ~l1_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.20/1.74  tff(c_259, plain, (v2_tops_1('#skF_2', '#skF_1') | ~v3_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_256])).
% 4.20/1.74  tff(c_262, plain, (v2_tops_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36, c_259])).
% 4.20/1.74  tff(c_356, plain, (![A_55, B_56]: (k1_tops_1(A_55, B_56)=k1_xboole_0 | ~v2_tops_1(B_56, A_55) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_pre_topc(A_55))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.20/1.74  tff(c_359, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v2_tops_1('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_356])).
% 4.20/1.74  tff(c_362, plain, (k1_tops_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_262, c_359])).
% 4.20/1.74  tff(c_993, plain, (![A_79, B_80]: (k7_subset_1(u1_struct_0(A_79), k2_pre_topc(A_79, B_80), k1_tops_1(A_79, B_80))=k2_tops_1(A_79, B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0(A_79))) | ~l1_pre_topc(A_79))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.20/1.74  tff(c_1002, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~l1_pre_topc('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_362, c_993])).
% 4.20/1.74  tff(c_1006, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_1002])).
% 4.20/1.74  tff(c_1592, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k1_xboole_0)=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1577, c_1006])).
% 4.20/1.74  tff(c_1616, plain, (k2_tops_1('#skF_1', '#skF_2')=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1592])).
% 4.20/1.74  tff(c_184, plain, (![A_42, B_43, C_44]: (k7_subset_1(A_42, B_43, C_44)=k4_xboole_0(B_43, C_44) | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.20/1.74  tff(c_187, plain, (![C_44]: (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', C_44)=k4_xboole_0('#skF_2', C_44))), inference(resolution, [status(thm)], [c_40, c_184])).
% 4.20/1.74  tff(c_696, plain, (![A_73, B_74]: (k7_subset_1(u1_struct_0(A_73), B_74, k2_tops_1(A_73, B_74))=k1_tops_1(A_73, B_74) | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0(A_73))) | ~l1_pre_topc(A_73))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.20/1.74  tff(c_700, plain, (k7_subset_1(u1_struct_0('#skF_1'), '#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_tops_1('#skF_1', '#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_696])).
% 4.20/1.74  tff(c_704, plain, (k4_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_362, c_187, c_700])).
% 4.20/1.74  tff(c_8, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k4_xboole_0(A_5, B_6))=k3_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.20/1.74  tff(c_714, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))=k4_xboole_0('#skF_2', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_704, c_8])).
% 4.20/1.74  tff(c_719, plain, (k3_xboole_0('#skF_2', k2_tops_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_714])).
% 4.20/1.74  tff(c_1627, plain, (k3_xboole_0('#skF_2', k2_pre_topc('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1616, c_719])).
% 4.20/1.74  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.20/1.74  tff(c_108, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k4_xboole_0(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.20/1.74  tff(c_226, plain, (![A_47, B_48]: (k4_xboole_0(A_47, k3_xboole_0(A_47, B_48))=k3_xboole_0(A_47, k4_xboole_0(A_47, B_48)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_8])).
% 4.20/1.74  tff(c_264, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k3_xboole_0(B_52, A_51))=k3_xboole_0(A_51, k4_xboole_0(A_51, B_52)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_226])).
% 4.20/1.74  tff(c_367, plain, (![A_57, B_58]: (k4_xboole_0(A_57, k3_xboole_0(A_57, k4_xboole_0(A_57, B_58)))=k3_xboole_0(A_57, k3_xboole_0(B_58, A_57)))), inference(superposition, [status(thm), theory('equality')], [c_264, c_8])).
% 4.20/1.74  tff(c_232, plain, (![A_47, B_48]: (k4_xboole_0(A_47, k3_xboole_0(A_47, k4_xboole_0(A_47, B_48)))=k3_xboole_0(A_47, k3_xboole_0(A_47, B_48)))), inference(superposition, [status(thm), theory('equality')], [c_226, c_8])).
% 4.20/1.74  tff(c_379, plain, (![A_57, B_58]: (k3_xboole_0(A_57, k3_xboole_0(B_58, A_57))=k3_xboole_0(A_57, k3_xboole_0(A_57, B_58)))), inference(superposition, [status(thm), theory('equality')], [c_367, c_232])).
% 4.20/1.74  tff(c_61, plain, (![B_36, A_37]: (k3_xboole_0(B_36, A_37)=k3_xboole_0(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.20/1.74  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.20/1.74  tff(c_77, plain, (![A_37]: (k3_xboole_0(k1_xboole_0, A_37)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_61, c_4])).
% 4.20/1.74  tff(c_123, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_108])).
% 4.20/1.74  tff(c_126, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_123])).
% 4.20/1.74  tff(c_244, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k3_xboole_0(A_1, k4_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_226])).
% 4.20/1.74  tff(c_161, plain, (![A_41]: (k4_xboole_0(A_41, A_41)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_123])).
% 4.20/1.74  tff(c_166, plain, (![A_41]: (k4_xboole_0(A_41, k1_xboole_0)=k3_xboole_0(A_41, A_41))), inference(superposition, [status(thm), theory('equality')], [c_161, c_8])).
% 4.20/1.74  tff(c_178, plain, (![A_41]: (k3_xboole_0(A_41, A_41)=A_41)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_166])).
% 4.20/1.74  tff(c_307, plain, (![A_53, B_54]: (k4_xboole_0(A_53, k3_xboole_0(A_53, k4_xboole_0(A_53, B_54)))=k3_xboole_0(A_53, k3_xboole_0(A_53, B_54)))), inference(superposition, [status(thm), theory('equality')], [c_226, c_8])).
% 4.20/1.74  tff(c_771, plain, (![A_75, B_76]: (k4_xboole_0(A_75, k3_xboole_0(A_75, k3_xboole_0(A_75, k4_xboole_0(A_75, B_76))))=k3_xboole_0(A_75, k3_xboole_0(A_75, k3_xboole_0(B_76, A_75))))), inference(superposition, [status(thm), theory('equality')], [c_244, c_307])).
% 4.20/1.74  tff(c_345, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k3_xboole_0(A_5, k3_xboole_0(A_5, B_6)))=k3_xboole_0(A_5, k3_xboole_0(A_5, k4_xboole_0(A_5, B_6))))), inference(superposition, [status(thm), theory('equality')], [c_8, c_307])).
% 4.20/1.74  tff(c_780, plain, (![A_75, B_76]: (k3_xboole_0(A_75, k3_xboole_0(A_75, k4_xboole_0(A_75, k4_xboole_0(A_75, B_76))))=k3_xboole_0(A_75, k3_xboole_0(A_75, k3_xboole_0(B_76, A_75))))), inference(superposition, [status(thm), theory('equality')], [c_771, c_345])).
% 4.20/1.74  tff(c_850, plain, (![A_75, B_76]: (k3_xboole_0(A_75, k3_xboole_0(A_75, k3_xboole_0(B_76, A_75)))=k3_xboole_0(A_75, k3_xboole_0(A_75, k3_xboole_0(A_75, B_76))))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_780])).
% 4.20/1.74  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.20/1.74  tff(c_38, plain, (v3_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.20/1.74  tff(c_1218, plain, (![A_91, B_92]: (k7_subset_1(u1_struct_0(A_91), k2_pre_topc(A_91, B_92), B_92)=k2_tops_1(A_91, B_92) | ~v3_pre_topc(B_92, A_91) | ~m1_subset_1(B_92, k1_zfmisc_1(u1_struct_0(A_91))) | ~l1_pre_topc(A_91) | ~v2_pre_topc(A_91))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.20/1.74  tff(c_1222, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2') | ~v3_pre_topc('#skF_2', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_40, c_1218])).
% 4.20/1.74  tff(c_1226, plain, (k7_subset_1(u1_struct_0('#skF_1'), k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_38, c_1222])).
% 4.20/1.74  tff(c_1589, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_tops_1('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1577, c_1226])).
% 4.20/1.74  tff(c_1688, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')=k2_pre_topc('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1616, c_1589])).
% 4.20/1.74  tff(c_111, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k3_xboole_0(A_38, B_39))=k3_xboole_0(A_38, k4_xboole_0(A_38, B_39)))), inference(superposition, [status(thm), theory('equality')], [c_108, c_8])).
% 4.20/1.74  tff(c_331, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k3_xboole_0(A_38, k3_xboole_0(A_38, k4_xboole_0(A_38, B_39))))=k3_xboole_0(A_38, k3_xboole_0(A_38, k3_xboole_0(A_38, B_39))))), inference(superposition, [status(thm), theory('equality')], [c_111, c_307])).
% 4.20/1.74  tff(c_1692, plain, (k4_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k3_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k3_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k2_pre_topc('#skF_1', '#skF_2'))))=k3_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k3_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), k3_xboole_0(k2_pre_topc('#skF_1', '#skF_2'), '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1688, c_331])).
% 4.20/1.74  tff(c_1707, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1627, c_2, c_1627, c_379, c_1627, c_77, c_2, c_126, c_244, c_178, c_850, c_1692])).
% 4.20/1.74  tff(c_1709, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_1707])).
% 4.20/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.20/1.74  
% 4.20/1.74  Inference rules
% 4.20/1.74  ----------------------
% 4.20/1.74  #Ref     : 0
% 4.20/1.74  #Sup     : 411
% 4.20/1.74  #Fact    : 0
% 4.20/1.74  #Define  : 0
% 4.20/1.74  #Split   : 3
% 4.20/1.74  #Chain   : 0
% 4.20/1.74  #Close   : 0
% 4.20/1.74  
% 4.20/1.74  Ordering : KBO
% 4.20/1.74  
% 4.20/1.74  Simplification rules
% 4.20/1.74  ----------------------
% 4.20/1.74  #Subsume      : 19
% 4.20/1.74  #Demod        : 672
% 4.20/1.74  #Tautology    : 260
% 4.20/1.74  #SimpNegUnit  : 1
% 4.20/1.74  #BackRed      : 8
% 4.20/1.74  
% 4.20/1.74  #Partial instantiations: 0
% 4.20/1.74  #Strategies tried      : 1
% 4.20/1.74  
% 4.20/1.74  Timing (in seconds)
% 4.20/1.74  ----------------------
% 4.20/1.74  Preprocessing        : 0.35
% 4.20/1.74  Parsing              : 0.19
% 4.20/1.74  CNF conversion       : 0.02
% 4.20/1.74  Main loop            : 0.63
% 4.20/1.74  Inferencing          : 0.17
% 4.20/1.74  Reduction            : 0.33
% 4.20/1.74  Demodulation         : 0.28
% 4.20/1.74  BG Simplification    : 0.03
% 4.20/1.74  Subsumption          : 0.08
% 4.20/1.74  Abstraction          : 0.03
% 4.20/1.74  MUC search           : 0.00
% 4.20/1.74  Cooper               : 0.00
% 4.20/1.74  Total                : 1.02
% 4.20/1.74  Index Insertion      : 0.00
% 4.20/1.74  Index Deletion       : 0.00
% 4.20/1.74  Index Matching       : 0.00
% 4.20/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
