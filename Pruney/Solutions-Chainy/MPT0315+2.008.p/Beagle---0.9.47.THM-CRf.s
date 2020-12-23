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
% DateTime   : Thu Dec  3 09:53:56 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 274 expanded)
%              Number of leaves         :   22 ( 100 expanded)
%              Depth                    :   12
%              Number of atoms          :  119 ( 428 expanded)
%              Number of equality atoms :   55 ( 160 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_45,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_xboole_0(A,B)
          | r1_xboole_0(C,D) )
       => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(c_8,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1111,plain,(
    ! [A_109,B_110] : k4_xboole_0(A_109,k4_xboole_0(A_109,B_110)) = k3_xboole_0(A_109,B_110) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_607,plain,(
    ! [A_71,B_72] :
      ( r1_xboole_0(A_71,B_72)
      | k4_xboole_0(A_71,B_72) != A_71 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_620,plain,(
    ! [B_72,A_71] :
      ( r1_xboole_0(B_72,A_71)
      | k4_xboole_0(A_71,B_72) != A_71 ) ),
    inference(resolution,[status(thm)],[c_607,c_2])).

tff(c_18,plain,(
    ! [A_13] : k2_zfmisc_1(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_639,plain,(
    ! [A_75,B_76,C_77] :
      ( ~ r1_xboole_0(A_75,B_76)
      | ~ r2_hidden(C_77,k3_xboole_0(A_75,B_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_642,plain,(
    ! [A_8,C_77] :
      ( ~ r1_xboole_0(A_8,k1_xboole_0)
      | ~ r2_hidden(C_77,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_639])).

tff(c_643,plain,(
    ! [C_77] : ~ r2_hidden(C_77,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_642])).

tff(c_726,plain,(
    ! [A_85,B_86] :
      ( r2_hidden('#skF_1'(A_85,B_86),k3_xboole_0(A_85,B_86))
      | r1_xboole_0(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_732,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_1'(A_8,k1_xboole_0),k1_xboole_0)
      | r1_xboole_0(A_8,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_726])).

tff(c_735,plain,(
    ! [A_87] : r1_xboole_0(A_87,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_643,c_732])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = A_11
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_752,plain,(
    ! [A_89] : k4_xboole_0(A_89,k1_xboole_0) = A_89 ),
    inference(resolution,[status(thm)],[c_735,c_12])).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_760,plain,(
    ! [A_89] : k4_xboole_0(A_89,A_89) = k3_xboole_0(A_89,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_752,c_10])).

tff(c_766,plain,(
    ! [A_89] : k4_xboole_0(A_89,A_89) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_760])).

tff(c_549,plain,(
    ! [A_64,B_65] : k4_xboole_0(A_64,k4_xboole_0(A_64,B_65)) = k3_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_65,plain,(
    ! [A_24,B_25] :
      ( r1_xboole_0(A_24,B_25)
      | k4_xboole_0(A_24,B_25) != A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_68,plain,(
    ! [B_25,A_24] :
      ( r1_xboole_0(B_25,A_24)
      | k4_xboole_0(A_24,B_25) != A_24 ) ),
    inference(resolution,[status(thm)],[c_65,c_2])).

tff(c_20,plain,(
    ! [B_14] : k2_zfmisc_1(k1_xboole_0,B_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_106,plain,(
    ! [A_30,B_31,C_32] :
      ( ~ r1_xboole_0(A_30,B_31)
      | ~ r2_hidden(C_32,k3_xboole_0(A_30,B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_109,plain,(
    ! [A_8,C_32] :
      ( ~ r1_xboole_0(A_8,k1_xboole_0)
      | ~ r2_hidden(C_32,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_106])).

tff(c_110,plain,(
    ! [C_32] : ~ r2_hidden(C_32,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_109])).

tff(c_193,plain,(
    ! [A_40,B_41] :
      ( r2_hidden('#skF_1'(A_40,B_41),k3_xboole_0(A_40,B_41))
      | r1_xboole_0(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_199,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_1'(A_8,k1_xboole_0),k1_xboole_0)
      | r1_xboole_0(A_8,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_193])).

tff(c_231,plain,(
    ! [A_46] : r1_xboole_0(A_46,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_199])).

tff(c_248,plain,(
    ! [A_48] : k4_xboole_0(A_48,k1_xboole_0) = A_48 ),
    inference(resolution,[status(thm)],[c_231,c_12])).

tff(c_256,plain,(
    ! [A_48] : k4_xboole_0(A_48,A_48) = k3_xboole_0(A_48,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_10])).

tff(c_262,plain,(
    ! [A_48] : k4_xboole_0(A_48,A_48) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_256])).

tff(c_26,plain,
    ( r1_xboole_0('#skF_4','#skF_5')
    | r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_56,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_69,plain,(
    ! [A_26,B_27] :
      ( k4_xboole_0(A_26,B_27) = A_26
      | ~ r1_xboole_0(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_81,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_56,c_69])).

tff(c_111,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k4_xboole_0(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_129,plain,(
    k4_xboole_0('#skF_2','#skF_2') = k3_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_111])).

tff(c_298,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_129])).

tff(c_22,plain,(
    ! [A_15,C_17,B_16,D_18] : k3_xboole_0(k2_zfmisc_1(A_15,C_17),k2_zfmisc_1(B_16,D_18)) = k2_zfmisc_1(k3_xboole_0(A_15,B_16),k3_xboole_0(C_17,D_18)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),k3_xboole_0(A_3,B_4))
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_237,plain,(
    ! [A_46] : k4_xboole_0(A_46,k1_xboole_0) = A_46 ),
    inference(resolution,[status(thm)],[c_231,c_12])).

tff(c_364,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k3_xboole_0(A_51,B_52)) = k3_xboole_0(A_51,k4_xboole_0(A_51,B_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_10])).

tff(c_395,plain,(
    ! [A_8] : k3_xboole_0(A_8,k4_xboole_0(A_8,k1_xboole_0)) = k4_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_364])).

tff(c_403,plain,(
    ! [A_53] : k3_xboole_0(A_53,A_53) = A_53 ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_237,c_395])).

tff(c_6,plain,(
    ! [A_3,B_4,C_7] :
      ( ~ r1_xboole_0(A_3,B_4)
      | ~ r2_hidden(C_7,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_490,plain,(
    ! [A_55,C_56] :
      ( ~ r1_xboole_0(A_55,A_55)
      | ~ r2_hidden(C_56,A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_6])).

tff(c_499,plain,(
    ! [C_56,A_24] :
      ( ~ r2_hidden(C_56,A_24)
      | k4_xboole_0(A_24,A_24) != A_24 ) ),
    inference(resolution,[status(thm)],[c_68,c_490])).

tff(c_510,plain,(
    ! [C_57,A_58] :
      ( ~ r2_hidden(C_57,A_58)
      | k1_xboole_0 != A_58 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_499])).

tff(c_517,plain,(
    ! [A_59,B_60] :
      ( k3_xboole_0(A_59,B_60) != k1_xboole_0
      | r1_xboole_0(A_59,B_60) ) ),
    inference(resolution,[status(thm)],[c_4,c_510])).

tff(c_24,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_2','#skF_4'),k2_zfmisc_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_523,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_2','#skF_4'),k2_zfmisc_1('#skF_3','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_517,c_24])).

tff(c_534,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_298,c_22,c_523])).

tff(c_536,plain,(
    ! [A_61] : ~ r1_xboole_0(A_61,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_109])).

tff(c_545,plain,(
    ! [B_25] : k4_xboole_0(k1_xboole_0,B_25) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_68,c_536])).

tff(c_574,plain,(
    ! [B_66] : k3_xboole_0(k1_xboole_0,B_66) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_549,c_545])).

tff(c_579,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_574])).

tff(c_580,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_590,plain,(
    ! [A_69,B_70] :
      ( k4_xboole_0(A_69,B_70) = A_69
      | ~ r1_xboole_0(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_598,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_580,c_590])).

tff(c_645,plain,(
    ! [A_79,B_80] : k4_xboole_0(A_79,k4_xboole_0(A_79,B_80)) = k3_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_663,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_598,c_645])).

tff(c_831,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_766,c_663])).

tff(c_741,plain,(
    ! [A_87] : k4_xboole_0(A_87,k1_xboole_0) = A_87 ),
    inference(resolution,[status(thm)],[c_735,c_12])).

tff(c_943,plain,(
    ! [A_97,B_98] : k4_xboole_0(A_97,k3_xboole_0(A_97,B_98)) = k3_xboole_0(A_97,k4_xboole_0(A_97,B_98)) ),
    inference(superposition,[status(thm),theory(equality)],[c_645,c_10])).

tff(c_983,plain,(
    ! [A_8] : k3_xboole_0(A_8,k4_xboole_0(A_8,k1_xboole_0)) = k4_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_943])).

tff(c_996,plain,(
    ! [A_99] : k3_xboole_0(A_99,A_99) = A_99 ),
    inference(demodulation,[status(thm),theory(equality)],[c_741,c_741,c_983])).

tff(c_1048,plain,(
    ! [A_100,C_101] :
      ( ~ r1_xboole_0(A_100,A_100)
      | ~ r2_hidden(C_101,A_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_996,c_6])).

tff(c_1057,plain,(
    ! [C_101,A_71] :
      ( ~ r2_hidden(C_101,A_71)
      | k4_xboole_0(A_71,A_71) != A_71 ) ),
    inference(resolution,[status(thm)],[c_620,c_1048])).

tff(c_1068,plain,(
    ! [C_102,A_103] :
      ( ~ r2_hidden(C_102,A_103)
      | k1_xboole_0 != A_103 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_766,c_1057])).

tff(c_1074,plain,(
    ! [A_104,B_105] :
      ( k3_xboole_0(A_104,B_105) != k1_xboole_0
      | r1_xboole_0(A_104,B_105) ) ),
    inference(resolution,[status(thm)],[c_4,c_1068])).

tff(c_1085,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_2','#skF_4'),k2_zfmisc_1('#skF_3','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1074,c_24])).

tff(c_1096,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_831,c_22,c_1085])).

tff(c_1098,plain,(
    ! [A_106] : ~ r1_xboole_0(A_106,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_642])).

tff(c_1107,plain,(
    ! [B_72] : k4_xboole_0(k1_xboole_0,B_72) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_620,c_1098])).

tff(c_1136,plain,(
    ! [B_111] : k3_xboole_0(k1_xboole_0,B_111) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1111,c_1107])).

tff(c_1141,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_1136])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n022.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 16:45:55 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.44  
% 2.69/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.45  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.69/1.45  
% 2.69/1.45  %Foreground sorts:
% 2.69/1.45  
% 2.69/1.45  
% 2.69/1.45  %Background operators:
% 2.69/1.45  
% 2.69/1.45  
% 2.69/1.45  %Foreground operators:
% 2.69/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.69/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.69/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.69/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.69/1.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.69/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.69/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.69/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.69/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.69/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.69/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.69/1.45  
% 2.96/1.47  tff(f_45, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.96/1.47  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.96/1.47  tff(f_51, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.96/1.47  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.96/1.47  tff(f_57, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.96/1.47  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.96/1.47  tff(f_66, negated_conjecture, ~(![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 2.96/1.47  tff(f_59, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 2.96/1.47  tff(c_8, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.96/1.47  tff(c_1111, plain, (![A_109, B_110]: (k4_xboole_0(A_109, k4_xboole_0(A_109, B_110))=k3_xboole_0(A_109, B_110))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.96/1.47  tff(c_607, plain, (![A_71, B_72]: (r1_xboole_0(A_71, B_72) | k4_xboole_0(A_71, B_72)!=A_71)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.96/1.47  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.96/1.47  tff(c_620, plain, (![B_72, A_71]: (r1_xboole_0(B_72, A_71) | k4_xboole_0(A_71, B_72)!=A_71)), inference(resolution, [status(thm)], [c_607, c_2])).
% 2.96/1.47  tff(c_18, plain, (![A_13]: (k2_zfmisc_1(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.96/1.47  tff(c_639, plain, (![A_75, B_76, C_77]: (~r1_xboole_0(A_75, B_76) | ~r2_hidden(C_77, k3_xboole_0(A_75, B_76)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.96/1.47  tff(c_642, plain, (![A_8, C_77]: (~r1_xboole_0(A_8, k1_xboole_0) | ~r2_hidden(C_77, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_639])).
% 2.96/1.47  tff(c_643, plain, (![C_77]: (~r2_hidden(C_77, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_642])).
% 2.96/1.47  tff(c_726, plain, (![A_85, B_86]: (r2_hidden('#skF_1'(A_85, B_86), k3_xboole_0(A_85, B_86)) | r1_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.96/1.47  tff(c_732, plain, (![A_8]: (r2_hidden('#skF_1'(A_8, k1_xboole_0), k1_xboole_0) | r1_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_726])).
% 2.96/1.47  tff(c_735, plain, (![A_87]: (r1_xboole_0(A_87, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_643, c_732])).
% 2.96/1.47  tff(c_12, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=A_11 | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.96/1.47  tff(c_752, plain, (![A_89]: (k4_xboole_0(A_89, k1_xboole_0)=A_89)), inference(resolution, [status(thm)], [c_735, c_12])).
% 2.96/1.47  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.96/1.47  tff(c_760, plain, (![A_89]: (k4_xboole_0(A_89, A_89)=k3_xboole_0(A_89, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_752, c_10])).
% 2.96/1.47  tff(c_766, plain, (![A_89]: (k4_xboole_0(A_89, A_89)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_760])).
% 2.96/1.47  tff(c_549, plain, (![A_64, B_65]: (k4_xboole_0(A_64, k4_xboole_0(A_64, B_65))=k3_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.96/1.47  tff(c_65, plain, (![A_24, B_25]: (r1_xboole_0(A_24, B_25) | k4_xboole_0(A_24, B_25)!=A_24)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.96/1.47  tff(c_68, plain, (![B_25, A_24]: (r1_xboole_0(B_25, A_24) | k4_xboole_0(A_24, B_25)!=A_24)), inference(resolution, [status(thm)], [c_65, c_2])).
% 2.96/1.47  tff(c_20, plain, (![B_14]: (k2_zfmisc_1(k1_xboole_0, B_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.96/1.47  tff(c_106, plain, (![A_30, B_31, C_32]: (~r1_xboole_0(A_30, B_31) | ~r2_hidden(C_32, k3_xboole_0(A_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.96/1.47  tff(c_109, plain, (![A_8, C_32]: (~r1_xboole_0(A_8, k1_xboole_0) | ~r2_hidden(C_32, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_106])).
% 2.96/1.47  tff(c_110, plain, (![C_32]: (~r2_hidden(C_32, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_109])).
% 2.96/1.47  tff(c_193, plain, (![A_40, B_41]: (r2_hidden('#skF_1'(A_40, B_41), k3_xboole_0(A_40, B_41)) | r1_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.96/1.47  tff(c_199, plain, (![A_8]: (r2_hidden('#skF_1'(A_8, k1_xboole_0), k1_xboole_0) | r1_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_193])).
% 2.96/1.47  tff(c_231, plain, (![A_46]: (r1_xboole_0(A_46, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_110, c_199])).
% 2.96/1.47  tff(c_248, plain, (![A_48]: (k4_xboole_0(A_48, k1_xboole_0)=A_48)), inference(resolution, [status(thm)], [c_231, c_12])).
% 2.96/1.47  tff(c_256, plain, (![A_48]: (k4_xboole_0(A_48, A_48)=k3_xboole_0(A_48, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_248, c_10])).
% 2.96/1.47  tff(c_262, plain, (![A_48]: (k4_xboole_0(A_48, A_48)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_256])).
% 2.96/1.47  tff(c_26, plain, (r1_xboole_0('#skF_4', '#skF_5') | r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.96/1.47  tff(c_56, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_26])).
% 2.96/1.47  tff(c_69, plain, (![A_26, B_27]: (k4_xboole_0(A_26, B_27)=A_26 | ~r1_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.96/1.47  tff(c_81, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_56, c_69])).
% 2.96/1.47  tff(c_111, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k4_xboole_0(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.96/1.47  tff(c_129, plain, (k4_xboole_0('#skF_2', '#skF_2')=k3_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_81, c_111])).
% 2.96/1.47  tff(c_298, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_262, c_129])).
% 2.96/1.47  tff(c_22, plain, (![A_15, C_17, B_16, D_18]: (k3_xboole_0(k2_zfmisc_1(A_15, C_17), k2_zfmisc_1(B_16, D_18))=k2_zfmisc_1(k3_xboole_0(A_15, B_16), k3_xboole_0(C_17, D_18)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.96/1.47  tff(c_4, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), k3_xboole_0(A_3, B_4)) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.96/1.47  tff(c_237, plain, (![A_46]: (k4_xboole_0(A_46, k1_xboole_0)=A_46)), inference(resolution, [status(thm)], [c_231, c_12])).
% 2.96/1.47  tff(c_364, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k3_xboole_0(A_51, B_52))=k3_xboole_0(A_51, k4_xboole_0(A_51, B_52)))), inference(superposition, [status(thm), theory('equality')], [c_111, c_10])).
% 2.96/1.47  tff(c_395, plain, (![A_8]: (k3_xboole_0(A_8, k4_xboole_0(A_8, k1_xboole_0))=k4_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_364])).
% 2.96/1.47  tff(c_403, plain, (![A_53]: (k3_xboole_0(A_53, A_53)=A_53)), inference(demodulation, [status(thm), theory('equality')], [c_237, c_237, c_395])).
% 2.96/1.47  tff(c_6, plain, (![A_3, B_4, C_7]: (~r1_xboole_0(A_3, B_4) | ~r2_hidden(C_7, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.96/1.47  tff(c_490, plain, (![A_55, C_56]: (~r1_xboole_0(A_55, A_55) | ~r2_hidden(C_56, A_55))), inference(superposition, [status(thm), theory('equality')], [c_403, c_6])).
% 2.96/1.47  tff(c_499, plain, (![C_56, A_24]: (~r2_hidden(C_56, A_24) | k4_xboole_0(A_24, A_24)!=A_24)), inference(resolution, [status(thm)], [c_68, c_490])).
% 2.96/1.47  tff(c_510, plain, (![C_57, A_58]: (~r2_hidden(C_57, A_58) | k1_xboole_0!=A_58)), inference(demodulation, [status(thm), theory('equality')], [c_262, c_499])).
% 2.96/1.47  tff(c_517, plain, (![A_59, B_60]: (k3_xboole_0(A_59, B_60)!=k1_xboole_0 | r1_xboole_0(A_59, B_60))), inference(resolution, [status(thm)], [c_4, c_510])).
% 2.96/1.47  tff(c_24, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_4'), k2_zfmisc_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.96/1.47  tff(c_523, plain, (k3_xboole_0(k2_zfmisc_1('#skF_2', '#skF_4'), k2_zfmisc_1('#skF_3', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_517, c_24])).
% 2.96/1.47  tff(c_534, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_298, c_22, c_523])).
% 2.96/1.47  tff(c_536, plain, (![A_61]: (~r1_xboole_0(A_61, k1_xboole_0))), inference(splitRight, [status(thm)], [c_109])).
% 2.96/1.47  tff(c_545, plain, (![B_25]: (k4_xboole_0(k1_xboole_0, B_25)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_68, c_536])).
% 2.96/1.47  tff(c_574, plain, (![B_66]: (k3_xboole_0(k1_xboole_0, B_66)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_549, c_545])).
% 2.96/1.47  tff(c_579, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_8, c_574])).
% 2.96/1.47  tff(c_580, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_26])).
% 2.96/1.47  tff(c_590, plain, (![A_69, B_70]: (k4_xboole_0(A_69, B_70)=A_69 | ~r1_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.96/1.47  tff(c_598, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_580, c_590])).
% 2.96/1.47  tff(c_645, plain, (![A_79, B_80]: (k4_xboole_0(A_79, k4_xboole_0(A_79, B_80))=k3_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.96/1.47  tff(c_663, plain, (k4_xboole_0('#skF_4', '#skF_4')=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_598, c_645])).
% 2.96/1.47  tff(c_831, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_766, c_663])).
% 2.96/1.47  tff(c_741, plain, (![A_87]: (k4_xboole_0(A_87, k1_xboole_0)=A_87)), inference(resolution, [status(thm)], [c_735, c_12])).
% 2.96/1.47  tff(c_943, plain, (![A_97, B_98]: (k4_xboole_0(A_97, k3_xboole_0(A_97, B_98))=k3_xboole_0(A_97, k4_xboole_0(A_97, B_98)))), inference(superposition, [status(thm), theory('equality')], [c_645, c_10])).
% 2.96/1.47  tff(c_983, plain, (![A_8]: (k3_xboole_0(A_8, k4_xboole_0(A_8, k1_xboole_0))=k4_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_943])).
% 2.96/1.47  tff(c_996, plain, (![A_99]: (k3_xboole_0(A_99, A_99)=A_99)), inference(demodulation, [status(thm), theory('equality')], [c_741, c_741, c_983])).
% 2.96/1.47  tff(c_1048, plain, (![A_100, C_101]: (~r1_xboole_0(A_100, A_100) | ~r2_hidden(C_101, A_100))), inference(superposition, [status(thm), theory('equality')], [c_996, c_6])).
% 2.96/1.47  tff(c_1057, plain, (![C_101, A_71]: (~r2_hidden(C_101, A_71) | k4_xboole_0(A_71, A_71)!=A_71)), inference(resolution, [status(thm)], [c_620, c_1048])).
% 2.96/1.47  tff(c_1068, plain, (![C_102, A_103]: (~r2_hidden(C_102, A_103) | k1_xboole_0!=A_103)), inference(demodulation, [status(thm), theory('equality')], [c_766, c_1057])).
% 2.96/1.47  tff(c_1074, plain, (![A_104, B_105]: (k3_xboole_0(A_104, B_105)!=k1_xboole_0 | r1_xboole_0(A_104, B_105))), inference(resolution, [status(thm)], [c_4, c_1068])).
% 2.96/1.47  tff(c_1085, plain, (k3_xboole_0(k2_zfmisc_1('#skF_2', '#skF_4'), k2_zfmisc_1('#skF_3', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_1074, c_24])).
% 2.96/1.47  tff(c_1096, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_831, c_22, c_1085])).
% 2.96/1.47  tff(c_1098, plain, (![A_106]: (~r1_xboole_0(A_106, k1_xboole_0))), inference(splitRight, [status(thm)], [c_642])).
% 2.96/1.47  tff(c_1107, plain, (![B_72]: (k4_xboole_0(k1_xboole_0, B_72)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_620, c_1098])).
% 2.96/1.47  tff(c_1136, plain, (![B_111]: (k3_xboole_0(k1_xboole_0, B_111)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1111, c_1107])).
% 2.96/1.47  tff(c_1141, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_8, c_1136])).
% 2.96/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.47  
% 2.96/1.47  Inference rules
% 2.96/1.47  ----------------------
% 2.96/1.47  #Ref     : 0
% 2.96/1.47  #Sup     : 283
% 2.96/1.47  #Fact    : 0
% 2.96/1.47  #Define  : 0
% 2.96/1.47  #Split   : 3
% 2.96/1.47  #Chain   : 0
% 2.96/1.47  #Close   : 0
% 2.96/1.47  
% 2.96/1.47  Ordering : KBO
% 2.96/1.47  
% 2.96/1.47  Simplification rules
% 2.96/1.47  ----------------------
% 2.96/1.47  #Subsume      : 18
% 2.96/1.47  #Demod        : 146
% 2.96/1.47  #Tautology    : 173
% 2.96/1.47  #SimpNegUnit  : 8
% 2.96/1.47  #BackRed      : 8
% 2.96/1.47  
% 2.96/1.47  #Partial instantiations: 0
% 2.96/1.47  #Strategies tried      : 1
% 2.96/1.47  
% 2.96/1.47  Timing (in seconds)
% 2.96/1.47  ----------------------
% 2.96/1.47  Preprocessing        : 0.31
% 2.96/1.47  Parsing              : 0.17
% 2.96/1.47  CNF conversion       : 0.02
% 2.96/1.47  Main loop            : 0.37
% 2.96/1.47  Inferencing          : 0.15
% 2.96/1.47  Reduction            : 0.12
% 2.96/1.47  Demodulation         : 0.09
% 2.96/1.47  BG Simplification    : 0.02
% 2.96/1.47  Subsumption          : 0.05
% 2.96/1.47  Abstraction          : 0.02
% 2.96/1.47  MUC search           : 0.00
% 2.96/1.47  Cooper               : 0.00
% 2.96/1.47  Total                : 0.72
% 2.96/1.47  Index Insertion      : 0.00
% 2.96/1.47  Index Deletion       : 0.00
% 2.96/1.47  Index Matching       : 0.00
% 2.96/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
