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
% DateTime   : Thu Dec  3 09:56:12 EST 2020

% Result     : Theorem 4.00s
% Output     : CNFRefutation 4.34s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 252 expanded)
%              Number of leaves         :   33 (  95 expanded)
%              Depth                    :   14
%              Number of atoms          :  110 ( 341 expanded)
%              Number of equality atoms :   67 ( 188 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
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

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

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

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_10,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_239,plain,(
    ! [A_44,B_45] :
      ( k3_xboole_0(A_44,B_45) = A_44
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_244,plain,(
    ! [A_46] : k3_xboole_0(k1_xboole_0,A_46) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_239])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_249,plain,(
    ! [A_46] : k3_xboole_0(A_46,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_2])).

tff(c_14,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_310,plain,(
    ! [A_50,B_51] : k5_xboole_0(A_50,k3_xboole_0(A_50,B_51)) = k4_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_323,plain,(
    ! [A_46] : k5_xboole_0(A_46,k1_xboole_0) = k4_xboole_0(A_46,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_310])).

tff(c_340,plain,(
    ! [A_46] : k4_xboole_0(A_46,k1_xboole_0) = A_46 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_323])).

tff(c_401,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k4_xboole_0(A_58,B_59)) = k3_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_420,plain,(
    ! [A_46] : k4_xboole_0(A_46,A_46) = k3_xboole_0(A_46,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_340,c_401])).

tff(c_431,plain,(
    ! [A_46] : k4_xboole_0(A_46,A_46) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_420])).

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

tff(c_221,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_55])).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_222,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_46])).

tff(c_568,plain,(
    ! [A_68,B_69] :
      ( k4_xboole_0(A_68,B_69) = k3_subset_1(A_68,B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_578,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k3_subset_1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_222,c_568])).

tff(c_582,plain,(
    k3_subset_1('#skF_4','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_578])).

tff(c_48,plain,
    ( k2_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_56,plain,
    ( '#skF_3' != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_48])).

tff(c_238,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_221,c_56])).

tff(c_583,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_582,c_238])).

tff(c_586,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_583])).

tff(c_588,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_603,plain,(
    ! [A_76,B_77] :
      ( k3_xboole_0(A_76,B_77) = A_76
      | ~ r1_tarski(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_617,plain,(
    ! [A_80] : k3_xboole_0(k1_xboole_0,A_80) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_603])).

tff(c_622,plain,(
    ! [A_80] : k3_xboole_0(A_80,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_617,c_2])).

tff(c_702,plain,(
    ! [A_86,B_87] : k5_xboole_0(A_86,k3_xboole_0(A_86,B_87)) = k4_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_718,plain,(
    ! [A_80] : k5_xboole_0(A_80,k1_xboole_0) = k4_xboole_0(A_80,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_622,c_702])).

tff(c_736,plain,(
    ! [A_80] : k4_xboole_0(A_80,k1_xboole_0) = A_80 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_718])).

tff(c_18,plain,(
    ! [A_16] : k5_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_44,plain,(
    ! [A_27] : ~ v1_xboole_0(k1_zfmisc_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_739,plain,(
    ! [B_88,A_89] :
      ( r2_hidden(B_88,A_89)
      | ~ m1_subset_1(B_88,A_89)
      | v1_xboole_0(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_20,plain,(
    ! [C_21,A_17] :
      ( r1_tarski(C_21,A_17)
      | ~ r2_hidden(C_21,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_746,plain,(
    ! [B_88,A_17] :
      ( r1_tarski(B_88,A_17)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_17))
      | v1_xboole_0(k1_zfmisc_1(A_17)) ) ),
    inference(resolution,[status(thm)],[c_739,c_20])).

tff(c_790,plain,(
    ! [B_92,A_93] :
      ( r1_tarski(B_92,A_93)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_93)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_746])).

tff(c_803,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_790])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_807,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_803,c_8])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_811,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_807,c_6])).

tff(c_814,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_811])).

tff(c_587,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_610,plain,(
    k3_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_587,c_603])).

tff(c_682,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k3_subset_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_610])).

tff(c_1005,plain,(
    ! [A_100,B_101] :
      ( k4_xboole_0(A_100,B_101) = k3_subset_1(A_100,B_101)
      | ~ m1_subset_1(B_101,k1_zfmisc_1(A_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1018,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_1005])).

tff(c_924,plain,(
    ! [B_98,A_99] : k5_xboole_0(B_98,k3_xboole_0(A_99,B_98)) = k4_xboole_0(B_98,A_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_702])).

tff(c_944,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_807,c_924])).

tff(c_1020,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1018,c_944])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_127,plain,(
    ! [B_35,A_36] : k5_xboole_0(B_35,A_36) = k5_xboole_0(A_36,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_143,plain,(
    ! [A_36] : k5_xboole_0(k1_xboole_0,A_36) = A_36 ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_14])).

tff(c_1063,plain,(
    ! [A_102,B_103,C_104] : k5_xboole_0(k5_xboole_0(A_102,B_103),C_104) = k5_xboole_0(A_102,k5_xboole_0(B_103,C_104)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1144,plain,(
    ! [A_16,C_104] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_104)) = k5_xboole_0(k1_xboole_0,C_104) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1063])).

tff(c_1158,plain,(
    ! [A_105,C_106] : k5_xboole_0(A_105,k5_xboole_0(A_105,C_106)) = C_106 ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_1144])).

tff(c_1232,plain,(
    ! [A_107,B_108] : k5_xboole_0(A_107,k5_xboole_0(B_108,A_107)) = B_108 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1158])).

tff(c_1282,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1020,c_1232])).

tff(c_954,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_610,c_924])).

tff(c_1697,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1282,c_954])).

tff(c_12,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1701,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k4_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1697,c_12])).

tff(c_1704,plain,(
    k3_subset_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_814,c_682,c_1701])).

tff(c_1706,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1704,c_1697])).

tff(c_1719,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_736,c_1706])).

tff(c_1721,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_588,c_1719])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n017.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 11:02:16 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.00/2.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.00/2.15  
% 4.00/2.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.00/2.15  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.00/2.15  
% 4.00/2.15  %Foreground sorts:
% 4.00/2.15  
% 4.00/2.15  
% 4.00/2.15  %Background operators:
% 4.00/2.15  
% 4.00/2.15  
% 4.00/2.15  %Foreground operators:
% 4.00/2.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.00/2.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.00/2.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.00/2.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.00/2.15  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.00/2.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.00/2.15  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.00/2.15  tff('#skF_3', type, '#skF_3': $i).
% 4.00/2.15  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.00/2.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.00/2.15  tff('#skF_4', type, '#skF_4': $i).
% 4.00/2.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.00/2.15  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.00/2.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.00/2.15  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.00/2.15  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.00/2.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.00/2.15  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.00/2.15  
% 4.34/2.18  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.34/2.18  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.34/2.18  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.34/2.18  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.34/2.18  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.34/2.18  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.34/2.18  tff(f_67, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.34/2.18  tff(f_81, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 4.34/2.18  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.34/2.18  tff(f_45, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.34/2.18  tff(f_74, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.34/2.18  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 4.34/2.18  tff(f_52, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.34/2.18  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 4.34/2.18  tff(f_43, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.34/2.18  tff(c_10, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.34/2.18  tff(c_239, plain, (![A_44, B_45]: (k3_xboole_0(A_44, B_45)=A_44 | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.34/2.18  tff(c_244, plain, (![A_46]: (k3_xboole_0(k1_xboole_0, A_46)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_239])).
% 4.34/2.18  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.34/2.18  tff(c_249, plain, (![A_46]: (k3_xboole_0(A_46, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_244, c_2])).
% 4.34/2.18  tff(c_14, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.34/2.18  tff(c_310, plain, (![A_50, B_51]: (k5_xboole_0(A_50, k3_xboole_0(A_50, B_51))=k4_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.34/2.18  tff(c_323, plain, (![A_46]: (k5_xboole_0(A_46, k1_xboole_0)=k4_xboole_0(A_46, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_249, c_310])).
% 4.34/2.18  tff(c_340, plain, (![A_46]: (k4_xboole_0(A_46, k1_xboole_0)=A_46)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_323])).
% 4.34/2.18  tff(c_401, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k4_xboole_0(A_58, B_59))=k3_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.34/2.18  tff(c_420, plain, (![A_46]: (k4_xboole_0(A_46, A_46)=k3_xboole_0(A_46, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_340, c_401])).
% 4.34/2.18  tff(c_431, plain, (![A_46]: (k4_xboole_0(A_46, A_46)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_249, c_420])).
% 4.34/2.18  tff(c_40, plain, (![A_24]: (k2_subset_1(A_24)=A_24)), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.34/2.18  tff(c_54, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | k2_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.34/2.18  tff(c_55, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_54])).
% 4.34/2.18  tff(c_221, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_55])).
% 4.34/2.18  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.34/2.18  tff(c_222, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_221, c_46])).
% 4.34/2.18  tff(c_568, plain, (![A_68, B_69]: (k4_xboole_0(A_68, B_69)=k3_subset_1(A_68, B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.34/2.18  tff(c_578, plain, (k4_xboole_0('#skF_4', '#skF_4')=k3_subset_1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_222, c_568])).
% 4.34/2.18  tff(c_582, plain, (k3_subset_1('#skF_4', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_431, c_578])).
% 4.34/2.18  tff(c_48, plain, (k2_subset_1('#skF_3')!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.34/2.18  tff(c_56, plain, ('#skF_3'!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_48])).
% 4.34/2.18  tff(c_238, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_221, c_221, c_56])).
% 4.34/2.18  tff(c_583, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_582, c_238])).
% 4.34/2.18  tff(c_586, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_583])).
% 4.34/2.18  tff(c_588, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_55])).
% 4.34/2.18  tff(c_603, plain, (![A_76, B_77]: (k3_xboole_0(A_76, B_77)=A_76 | ~r1_tarski(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.34/2.18  tff(c_617, plain, (![A_80]: (k3_xboole_0(k1_xboole_0, A_80)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_603])).
% 4.34/2.18  tff(c_622, plain, (![A_80]: (k3_xboole_0(A_80, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_617, c_2])).
% 4.34/2.18  tff(c_702, plain, (![A_86, B_87]: (k5_xboole_0(A_86, k3_xboole_0(A_86, B_87))=k4_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.34/2.18  tff(c_718, plain, (![A_80]: (k5_xboole_0(A_80, k1_xboole_0)=k4_xboole_0(A_80, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_622, c_702])).
% 4.34/2.18  tff(c_736, plain, (![A_80]: (k4_xboole_0(A_80, k1_xboole_0)=A_80)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_718])).
% 4.34/2.18  tff(c_18, plain, (![A_16]: (k5_xboole_0(A_16, A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.34/2.18  tff(c_44, plain, (![A_27]: (~v1_xboole_0(k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.34/2.18  tff(c_739, plain, (![B_88, A_89]: (r2_hidden(B_88, A_89) | ~m1_subset_1(B_88, A_89) | v1_xboole_0(A_89))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.34/2.18  tff(c_20, plain, (![C_21, A_17]: (r1_tarski(C_21, A_17) | ~r2_hidden(C_21, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.34/2.18  tff(c_746, plain, (![B_88, A_17]: (r1_tarski(B_88, A_17) | ~m1_subset_1(B_88, k1_zfmisc_1(A_17)) | v1_xboole_0(k1_zfmisc_1(A_17)))), inference(resolution, [status(thm)], [c_739, c_20])).
% 4.34/2.18  tff(c_790, plain, (![B_92, A_93]: (r1_tarski(B_92, A_93) | ~m1_subset_1(B_92, k1_zfmisc_1(A_93)))), inference(negUnitSimplification, [status(thm)], [c_44, c_746])).
% 4.34/2.18  tff(c_803, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_790])).
% 4.34/2.18  tff(c_8, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.34/2.18  tff(c_807, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_803, c_8])).
% 4.34/2.18  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.34/2.18  tff(c_811, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_807, c_6])).
% 4.34/2.18  tff(c_814, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_18, c_811])).
% 4.34/2.18  tff(c_587, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_55])).
% 4.34/2.18  tff(c_610, plain, (k3_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_587, c_603])).
% 4.34/2.18  tff(c_682, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k3_subset_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2, c_610])).
% 4.34/2.18  tff(c_1005, plain, (![A_100, B_101]: (k4_xboole_0(A_100, B_101)=k3_subset_1(A_100, B_101) | ~m1_subset_1(B_101, k1_zfmisc_1(A_100)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.34/2.18  tff(c_1018, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_1005])).
% 4.34/2.18  tff(c_924, plain, (![B_98, A_99]: (k5_xboole_0(B_98, k3_xboole_0(A_99, B_98))=k4_xboole_0(B_98, A_99))), inference(superposition, [status(thm), theory('equality')], [c_2, c_702])).
% 4.34/2.18  tff(c_944, plain, (k5_xboole_0('#skF_3', '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_807, c_924])).
% 4.34/2.18  tff(c_1020, plain, (k5_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1018, c_944])).
% 4.34/2.18  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.34/2.18  tff(c_127, plain, (![B_35, A_36]: (k5_xboole_0(B_35, A_36)=k5_xboole_0(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.34/2.18  tff(c_143, plain, (![A_36]: (k5_xboole_0(k1_xboole_0, A_36)=A_36)), inference(superposition, [status(thm), theory('equality')], [c_127, c_14])).
% 4.34/2.18  tff(c_1063, plain, (![A_102, B_103, C_104]: (k5_xboole_0(k5_xboole_0(A_102, B_103), C_104)=k5_xboole_0(A_102, k5_xboole_0(B_103, C_104)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.34/2.18  tff(c_1144, plain, (![A_16, C_104]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_104))=k5_xboole_0(k1_xboole_0, C_104))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1063])).
% 4.34/2.18  tff(c_1158, plain, (![A_105, C_106]: (k5_xboole_0(A_105, k5_xboole_0(A_105, C_106))=C_106)), inference(demodulation, [status(thm), theory('equality')], [c_143, c_1144])).
% 4.34/2.18  tff(c_1232, plain, (![A_107, B_108]: (k5_xboole_0(A_107, k5_xboole_0(B_108, A_107))=B_108)), inference(superposition, [status(thm), theory('equality')], [c_4, c_1158])).
% 4.34/2.18  tff(c_1282, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1020, c_1232])).
% 4.34/2.18  tff(c_954, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_610, c_924])).
% 4.34/2.18  tff(c_1697, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1282, c_954])).
% 4.34/2.18  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.34/2.18  tff(c_1701, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k4_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1697, c_12])).
% 4.34/2.18  tff(c_1704, plain, (k3_subset_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_814, c_682, c_1701])).
% 4.34/2.18  tff(c_1706, plain, (k4_xboole_0('#skF_4', k1_xboole_0)='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1704, c_1697])).
% 4.34/2.18  tff(c_1719, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_736, c_1706])).
% 4.34/2.18  tff(c_1721, plain, $false, inference(negUnitSimplification, [status(thm)], [c_588, c_1719])).
% 4.34/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.34/2.18  
% 4.34/2.18  Inference rules
% 4.34/2.18  ----------------------
% 4.34/2.18  #Ref     : 0
% 4.34/2.18  #Sup     : 409
% 4.34/2.18  #Fact    : 0
% 4.34/2.18  #Define  : 0
% 4.34/2.18  #Split   : 1
% 4.34/2.18  #Chain   : 0
% 4.34/2.18  #Close   : 0
% 4.34/2.18  
% 4.34/2.18  Ordering : KBO
% 4.34/2.18  
% 4.34/2.18  Simplification rules
% 4.34/2.18  ----------------------
% 4.34/2.18  #Subsume      : 13
% 4.34/2.18  #Demod        : 224
% 4.34/2.18  #Tautology    : 298
% 4.34/2.18  #SimpNegUnit  : 5
% 4.34/2.18  #BackRed      : 17
% 4.34/2.18  
% 4.34/2.18  #Partial instantiations: 0
% 4.34/2.18  #Strategies tried      : 1
% 4.34/2.18  
% 4.34/2.18  Timing (in seconds)
% 4.34/2.18  ----------------------
% 4.34/2.19  Preprocessing        : 0.50
% 4.34/2.19  Parsing              : 0.25
% 4.34/2.19  CNF conversion       : 0.04
% 4.34/2.19  Main loop            : 0.77
% 4.34/2.19  Inferencing          : 0.26
% 4.34/2.19  Reduction            : 0.29
% 4.34/2.19  Demodulation         : 0.23
% 4.34/2.19  BG Simplification    : 0.04
% 4.34/2.19  Subsumption          : 0.11
% 4.34/2.19  Abstraction          : 0.04
% 4.34/2.19  MUC search           : 0.00
% 4.34/2.19  Cooper               : 0.00
% 4.34/2.19  Total                : 1.33
% 4.34/2.19  Index Insertion      : 0.00
% 4.34/2.19  Index Deletion       : 0.00
% 4.34/2.19  Index Matching       : 0.00
% 4.34/2.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
