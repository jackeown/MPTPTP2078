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
% DateTime   : Thu Dec  3 09:56:10 EST 2020

% Result     : Theorem 4.29s
% Output     : CNFRefutation 4.29s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 313 expanded)
%              Number of leaves         :   34 ( 117 expanded)
%              Depth                    :   17
%              Number of atoms          :  112 ( 411 expanded)
%              Number of equality atoms :   66 ( 231 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_67,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_74,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_10,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_157,plain,(
    ! [A_44,B_45] :
      ( k3_xboole_0(A_44,B_45) = A_44
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_168,plain,(
    ! [A_46] : k3_xboole_0(k1_xboole_0,A_46) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_157])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_173,plain,(
    ! [A_46] : k3_xboole_0(A_46,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_4])).

tff(c_16,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_234,plain,(
    ! [A_50,B_51] : k5_xboole_0(A_50,k3_xboole_0(A_50,B_51)) = k4_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_243,plain,(
    ! [A_46] : k5_xboole_0(A_46,k1_xboole_0) = k4_xboole_0(A_46,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_234])).

tff(c_255,plain,(
    ! [A_46] : k4_xboole_0(A_46,k1_xboole_0) = A_46 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_243])).

tff(c_371,plain,(
    ! [A_59,B_60] : k4_xboole_0(A_59,k4_xboole_0(A_59,B_60)) = k3_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_396,plain,(
    ! [A_46] : k4_xboole_0(A_46,A_46) = k3_xboole_0(A_46,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_371])).

tff(c_408,plain,(
    ! [A_46] : k4_xboole_0(A_46,A_46) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_396])).

tff(c_40,plain,(
    ! [A_24] : k2_subset_1(A_24) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_54,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | k2_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_55,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_54])).

tff(c_145,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_55])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_146,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_46])).

tff(c_654,plain,(
    ! [A_76,B_77] :
      ( k4_xboole_0(A_76,B_77) = k3_subset_1(A_76,B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_660,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k3_subset_1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_146,c_654])).

tff(c_667,plain,(
    k3_subset_1('#skF_4','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_660])).

tff(c_48,plain,
    ( k2_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_56,plain,
    ( '#skF_3' != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_48])).

tff(c_167,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_145,c_56])).

tff(c_669,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_667,c_167])).

tff(c_672,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_669])).

tff(c_674,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_687,plain,(
    ! [A_82,B_83] :
      ( k3_xboole_0(A_82,B_83) = A_82
      | ~ r1_tarski(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_700,plain,(
    ! [A_84] : k3_xboole_0(k1_xboole_0,A_84) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_687])).

tff(c_705,plain,(
    ! [A_84] : k3_xboole_0(A_84,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_700,c_4])).

tff(c_778,plain,(
    ! [A_88,B_89] : k5_xboole_0(A_88,k3_xboole_0(A_88,B_89)) = k4_xboole_0(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_790,plain,(
    ! [A_84] : k5_xboole_0(A_84,k1_xboole_0) = k4_xboole_0(A_84,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_705,c_778])).

tff(c_802,plain,(
    ! [A_84] : k4_xboole_0(A_84,k1_xboole_0) = A_84 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_790])).

tff(c_874,plain,(
    ! [A_94,B_95] : k4_xboole_0(A_94,k4_xboole_0(A_94,B_95)) = k3_xboole_0(A_94,B_95) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_896,plain,(
    ! [A_84] : k4_xboole_0(A_84,A_84) = k3_xboole_0(A_84,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_802,c_874])).

tff(c_907,plain,(
    ! [A_84] : k4_xboole_0(A_84,A_84) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_705,c_896])).

tff(c_815,plain,(
    ! [A_91] : k4_xboole_0(A_91,k1_xboole_0) = A_91 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_790])).

tff(c_12,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_837,plain,(
    ! [A_92] : r1_tarski(A_92,A_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_815,c_12])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_842,plain,(
    ! [A_93] : k3_xboole_0(A_93,A_93) = A_93 ),
    inference(resolution,[status(thm)],[c_837,c_8])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_848,plain,(
    ! [A_93] : k5_xboole_0(A_93,A_93) = k4_xboole_0(A_93,A_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_842,c_6])).

tff(c_1015,plain,(
    ! [A_93] : k5_xboole_0(A_93,A_93) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_907,c_848])).

tff(c_44,plain,(
    ! [A_27] : ~ v1_xboole_0(k1_zfmisc_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1069,plain,(
    ! [B_108,A_109] :
      ( r2_hidden(B_108,A_109)
      | ~ m1_subset_1(B_108,A_109)
      | v1_xboole_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_20,plain,(
    ! [C_21,A_17] :
      ( r1_tarski(C_21,A_17)
      | ~ r2_hidden(C_21,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1076,plain,(
    ! [B_108,A_17] :
      ( r1_tarski(B_108,A_17)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(A_17))
      | v1_xboole_0(k1_zfmisc_1(A_17)) ) ),
    inference(resolution,[status(thm)],[c_1069,c_20])).

tff(c_1224,plain,(
    ! [B_114,A_115] :
      ( r1_tarski(B_114,A_115)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(A_115)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1076])).

tff(c_1237,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_1224])).

tff(c_1255,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1237,c_8])).

tff(c_1265,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1255,c_6])).

tff(c_1270,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1015,c_1265])).

tff(c_18,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1275,plain,(
    k5_xboole_0('#skF_3',k1_xboole_0) = k2_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1270,c_18])).

tff(c_1284,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2,c_1275])).

tff(c_1238,plain,(
    ! [A_116,B_117] :
      ( k4_xboole_0(A_116,B_117) = k3_subset_1(A_116,B_117)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(A_116)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1251,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_1238])).

tff(c_1291,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1251,c_18])).

tff(c_1412,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1284,c_1291])).

tff(c_673,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_697,plain,(
    k3_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_673,c_687])).

tff(c_1326,plain,(
    ! [B_118,A_119] : k5_xboole_0(B_118,k3_xboole_0(A_119,B_118)) = k4_xboole_0(B_118,A_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_778])).

tff(c_1360,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_697,c_1326])).

tff(c_4635,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1412,c_1360])).

tff(c_1417,plain,(
    ! [A_122,B_123] : k3_xboole_0(k4_xboole_0(A_122,B_123),A_122) = k4_xboole_0(A_122,B_123) ),
    inference(resolution,[status(thm)],[c_12,c_687])).

tff(c_1439,plain,(
    ! [A_122,B_123] : k3_xboole_0(A_122,k4_xboole_0(A_122,B_123)) = k4_xboole_0(A_122,B_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_1417,c_4])).

tff(c_4645,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4635,c_1439])).

tff(c_4668,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4635,c_1255,c_4645])).

tff(c_4670,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_674,c_4668])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:09:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.29/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.29/1.79  
% 4.29/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.29/1.79  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.29/1.79  
% 4.29/1.79  %Foreground sorts:
% 4.29/1.79  
% 4.29/1.79  
% 4.29/1.79  %Background operators:
% 4.29/1.79  
% 4.29/1.79  
% 4.29/1.79  %Foreground operators:
% 4.29/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.29/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.29/1.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.29/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.29/1.79  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.29/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.29/1.79  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.29/1.79  tff('#skF_3', type, '#skF_3': $i).
% 4.29/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.29/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.29/1.79  tff('#skF_4', type, '#skF_4': $i).
% 4.29/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.29/1.79  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.29/1.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.29/1.79  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.29/1.79  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.29/1.79  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.29/1.79  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.29/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.29/1.79  
% 4.29/1.81  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.29/1.81  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.29/1.81  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.29/1.81  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.29/1.81  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.29/1.81  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.29/1.81  tff(f_67, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.29/1.81  tff(f_81, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 4.29/1.81  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.29/1.81  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.29/1.81  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.29/1.81  tff(f_74, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.29/1.81  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 4.29/1.81  tff(f_52, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.29/1.81  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.29/1.81  tff(c_10, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.29/1.81  tff(c_157, plain, (![A_44, B_45]: (k3_xboole_0(A_44, B_45)=A_44 | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.29/1.81  tff(c_168, plain, (![A_46]: (k3_xboole_0(k1_xboole_0, A_46)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_157])).
% 4.29/1.81  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.29/1.81  tff(c_173, plain, (![A_46]: (k3_xboole_0(A_46, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_168, c_4])).
% 4.29/1.81  tff(c_16, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.29/1.81  tff(c_234, plain, (![A_50, B_51]: (k5_xboole_0(A_50, k3_xboole_0(A_50, B_51))=k4_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.29/1.81  tff(c_243, plain, (![A_46]: (k5_xboole_0(A_46, k1_xboole_0)=k4_xboole_0(A_46, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_173, c_234])).
% 4.29/1.81  tff(c_255, plain, (![A_46]: (k4_xboole_0(A_46, k1_xboole_0)=A_46)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_243])).
% 4.29/1.81  tff(c_371, plain, (![A_59, B_60]: (k4_xboole_0(A_59, k4_xboole_0(A_59, B_60))=k3_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.29/1.81  tff(c_396, plain, (![A_46]: (k4_xboole_0(A_46, A_46)=k3_xboole_0(A_46, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_255, c_371])).
% 4.29/1.81  tff(c_408, plain, (![A_46]: (k4_xboole_0(A_46, A_46)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_173, c_396])).
% 4.29/1.81  tff(c_40, plain, (![A_24]: (k2_subset_1(A_24)=A_24)), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.29/1.81  tff(c_54, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | k2_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.29/1.81  tff(c_55, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_54])).
% 4.29/1.81  tff(c_145, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_55])).
% 4.29/1.81  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.29/1.81  tff(c_146, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_46])).
% 4.29/1.81  tff(c_654, plain, (![A_76, B_77]: (k4_xboole_0(A_76, B_77)=k3_subset_1(A_76, B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.29/1.81  tff(c_660, plain, (k4_xboole_0('#skF_4', '#skF_4')=k3_subset_1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_146, c_654])).
% 4.29/1.81  tff(c_667, plain, (k3_subset_1('#skF_4', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_408, c_660])).
% 4.29/1.81  tff(c_48, plain, (k2_subset_1('#skF_3')!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.29/1.81  tff(c_56, plain, ('#skF_3'!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_48])).
% 4.29/1.81  tff(c_167, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_145, c_56])).
% 4.29/1.81  tff(c_669, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_667, c_167])).
% 4.29/1.81  tff(c_672, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_669])).
% 4.29/1.81  tff(c_674, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_55])).
% 4.29/1.81  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.29/1.81  tff(c_687, plain, (![A_82, B_83]: (k3_xboole_0(A_82, B_83)=A_82 | ~r1_tarski(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.29/1.81  tff(c_700, plain, (![A_84]: (k3_xboole_0(k1_xboole_0, A_84)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_687])).
% 4.29/1.81  tff(c_705, plain, (![A_84]: (k3_xboole_0(A_84, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_700, c_4])).
% 4.29/1.81  tff(c_778, plain, (![A_88, B_89]: (k5_xboole_0(A_88, k3_xboole_0(A_88, B_89))=k4_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.29/1.81  tff(c_790, plain, (![A_84]: (k5_xboole_0(A_84, k1_xboole_0)=k4_xboole_0(A_84, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_705, c_778])).
% 4.29/1.81  tff(c_802, plain, (![A_84]: (k4_xboole_0(A_84, k1_xboole_0)=A_84)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_790])).
% 4.29/1.81  tff(c_874, plain, (![A_94, B_95]: (k4_xboole_0(A_94, k4_xboole_0(A_94, B_95))=k3_xboole_0(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.29/1.81  tff(c_896, plain, (![A_84]: (k4_xboole_0(A_84, A_84)=k3_xboole_0(A_84, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_802, c_874])).
% 4.29/1.81  tff(c_907, plain, (![A_84]: (k4_xboole_0(A_84, A_84)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_705, c_896])).
% 4.29/1.81  tff(c_815, plain, (![A_91]: (k4_xboole_0(A_91, k1_xboole_0)=A_91)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_790])).
% 4.29/1.81  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.29/1.81  tff(c_837, plain, (![A_92]: (r1_tarski(A_92, A_92))), inference(superposition, [status(thm), theory('equality')], [c_815, c_12])).
% 4.29/1.81  tff(c_8, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.29/1.81  tff(c_842, plain, (![A_93]: (k3_xboole_0(A_93, A_93)=A_93)), inference(resolution, [status(thm)], [c_837, c_8])).
% 4.29/1.81  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.29/1.81  tff(c_848, plain, (![A_93]: (k5_xboole_0(A_93, A_93)=k4_xboole_0(A_93, A_93))), inference(superposition, [status(thm), theory('equality')], [c_842, c_6])).
% 4.29/1.81  tff(c_1015, plain, (![A_93]: (k5_xboole_0(A_93, A_93)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_907, c_848])).
% 4.29/1.81  tff(c_44, plain, (![A_27]: (~v1_xboole_0(k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.29/1.81  tff(c_1069, plain, (![B_108, A_109]: (r2_hidden(B_108, A_109) | ~m1_subset_1(B_108, A_109) | v1_xboole_0(A_109))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.29/1.81  tff(c_20, plain, (![C_21, A_17]: (r1_tarski(C_21, A_17) | ~r2_hidden(C_21, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.29/1.81  tff(c_1076, plain, (![B_108, A_17]: (r1_tarski(B_108, A_17) | ~m1_subset_1(B_108, k1_zfmisc_1(A_17)) | v1_xboole_0(k1_zfmisc_1(A_17)))), inference(resolution, [status(thm)], [c_1069, c_20])).
% 4.29/1.81  tff(c_1224, plain, (![B_114, A_115]: (r1_tarski(B_114, A_115) | ~m1_subset_1(B_114, k1_zfmisc_1(A_115)))), inference(negUnitSimplification, [status(thm)], [c_44, c_1076])).
% 4.29/1.81  tff(c_1237, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_1224])).
% 4.29/1.81  tff(c_1255, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_1237, c_8])).
% 4.29/1.81  tff(c_1265, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1255, c_6])).
% 4.29/1.81  tff(c_1270, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1015, c_1265])).
% 4.29/1.81  tff(c_18, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.29/1.81  tff(c_1275, plain, (k5_xboole_0('#skF_3', k1_xboole_0)=k2_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1270, c_18])).
% 4.29/1.81  tff(c_1284, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2, c_1275])).
% 4.29/1.81  tff(c_1238, plain, (![A_116, B_117]: (k4_xboole_0(A_116, B_117)=k3_subset_1(A_116, B_117) | ~m1_subset_1(B_117, k1_zfmisc_1(A_116)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.29/1.81  tff(c_1251, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_1238])).
% 4.29/1.81  tff(c_1291, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1251, c_18])).
% 4.29/1.81  tff(c_1412, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1284, c_1291])).
% 4.29/1.81  tff(c_673, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_55])).
% 4.29/1.81  tff(c_697, plain, (k3_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_673, c_687])).
% 4.29/1.81  tff(c_1326, plain, (![B_118, A_119]: (k5_xboole_0(B_118, k3_xboole_0(A_119, B_118))=k4_xboole_0(B_118, A_119))), inference(superposition, [status(thm), theory('equality')], [c_4, c_778])).
% 4.29/1.81  tff(c_1360, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_697, c_1326])).
% 4.29/1.81  tff(c_4635, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1412, c_1360])).
% 4.29/1.81  tff(c_1417, plain, (![A_122, B_123]: (k3_xboole_0(k4_xboole_0(A_122, B_123), A_122)=k4_xboole_0(A_122, B_123))), inference(resolution, [status(thm)], [c_12, c_687])).
% 4.29/1.81  tff(c_1439, plain, (![A_122, B_123]: (k3_xboole_0(A_122, k4_xboole_0(A_122, B_123))=k4_xboole_0(A_122, B_123))), inference(superposition, [status(thm), theory('equality')], [c_1417, c_4])).
% 4.29/1.81  tff(c_4645, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4635, c_1439])).
% 4.29/1.81  tff(c_4668, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4635, c_1255, c_4645])).
% 4.29/1.81  tff(c_4670, plain, $false, inference(negUnitSimplification, [status(thm)], [c_674, c_4668])).
% 4.29/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.29/1.81  
% 4.29/1.81  Inference rules
% 4.29/1.81  ----------------------
% 4.29/1.81  #Ref     : 0
% 4.29/1.81  #Sup     : 1125
% 4.29/1.81  #Fact    : 0
% 4.29/1.81  #Define  : 0
% 4.29/1.81  #Split   : 1
% 4.29/1.81  #Chain   : 0
% 4.29/1.81  #Close   : 0
% 4.29/1.81  
% 4.29/1.81  Ordering : KBO
% 4.29/1.81  
% 4.29/1.81  Simplification rules
% 4.29/1.81  ----------------------
% 4.29/1.81  #Subsume      : 28
% 4.29/1.81  #Demod        : 1298
% 4.29/1.81  #Tautology    : 939
% 4.29/1.81  #SimpNegUnit  : 7
% 4.29/1.81  #BackRed      : 2
% 4.29/1.81  
% 4.29/1.81  #Partial instantiations: 0
% 4.29/1.81  #Strategies tried      : 1
% 4.29/1.81  
% 4.29/1.81  Timing (in seconds)
% 4.29/1.81  ----------------------
% 4.29/1.81  Preprocessing        : 0.29
% 4.29/1.81  Parsing              : 0.15
% 4.29/1.81  CNF conversion       : 0.02
% 4.29/1.81  Main loop            : 0.73
% 4.29/1.81  Inferencing          : 0.23
% 4.29/1.81  Reduction            : 0.34
% 4.29/1.81  Demodulation         : 0.28
% 4.45/1.81  BG Simplification    : 0.03
% 4.45/1.81  Subsumption          : 0.09
% 4.45/1.81  Abstraction          : 0.04
% 4.45/1.81  MUC search           : 0.00
% 4.45/1.81  Cooper               : 0.00
% 4.45/1.81  Total                : 1.06
% 4.45/1.81  Index Insertion      : 0.00
% 4.45/1.81  Index Deletion       : 0.00
% 4.45/1.81  Index Matching       : 0.00
% 4.45/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
