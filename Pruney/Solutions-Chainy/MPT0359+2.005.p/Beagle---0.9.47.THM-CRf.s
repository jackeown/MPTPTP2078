%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:09 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 145 expanded)
%              Number of leaves         :   35 (  61 expanded)
%              Depth                    :   11
%              Number of atoms          :   92 ( 178 expanded)
%              Number of equality atoms :   49 ( 100 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_49,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_61,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_72,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_55,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_45,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_10,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [A_18] : k1_subset_1(A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    ! [A_19] : k2_subset_1(A_19) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_30,plain,(
    ! [A_25] : k3_subset_1(A_25,k1_subset_1(A_25)) = k2_subset_1(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_47,plain,(
    ! [A_25] : k3_subset_1(A_25,k1_subset_1(A_25)) = A_25 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_30])).

tff(c_51,plain,(
    ! [A_25] : k3_subset_1(A_25,k1_xboole_0) = A_25 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_47])).

tff(c_36,plain,(
    ! [A_30] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_582,plain,(
    ! [A_70,B_71] :
      ( k3_subset_1(A_70,k3_subset_1(A_70,B_71)) = B_71
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_584,plain,(
    ! [A_30] : k3_subset_1(A_30,k3_subset_1(A_30,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_582])).

tff(c_588,plain,(
    ! [A_30] : k3_subset_1(A_30,A_30) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_584])).

tff(c_40,plain,
    ( k2_subset_1('#skF_1') != '#skF_2'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_50,plain,
    ( '#skF_2' != '#skF_1'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_40])).

tff(c_122,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_46,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | k2_subset_1('#skF_1') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_49,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_46])).

tff(c_281,plain,(
    '#skF_2' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_49])).

tff(c_282,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_281,c_122])).

tff(c_591,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_588,c_282])).

tff(c_594,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_591])).

tff(c_595,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_26,plain,(
    ! [A_22] : m1_subset_1(k2_subset_1(A_22),k1_zfmisc_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_48,plain,(
    ! [A_22] : m1_subset_1(A_22,k1_zfmisc_1(A_22)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26])).

tff(c_1169,plain,(
    ! [A_103,B_104] :
      ( k3_subset_1(A_103,k3_subset_1(A_103,B_104)) = B_104
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1173,plain,(
    ! [A_30] : k3_subset_1(A_30,k3_subset_1(A_30,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_1169])).

tff(c_1178,plain,(
    ! [A_30] : k3_subset_1(A_30,A_30) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_1173])).

tff(c_1258,plain,(
    ! [B_108,C_109,A_110] :
      ( r1_tarski(B_108,C_109)
      | ~ r1_tarski(k3_subset_1(A_110,C_109),k3_subset_1(A_110,B_108))
      | ~ m1_subset_1(C_109,k1_zfmisc_1(A_110))
      | ~ m1_subset_1(B_108,k1_zfmisc_1(A_110)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1261,plain,(
    ! [B_108,A_30] :
      ( r1_tarski(B_108,A_30)
      | ~ r1_tarski(k1_xboole_0,k3_subset_1(A_30,B_108))
      | ~ m1_subset_1(A_30,k1_zfmisc_1(A_30))
      | ~ m1_subset_1(B_108,k1_zfmisc_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1178,c_1258])).

tff(c_1292,plain,(
    ! [B_111,A_112] :
      ( r1_tarski(B_111,A_112)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(A_112)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_10,c_1261])).

tff(c_1302,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_1292])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1309,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1302,c_8])).

tff(c_599,plain,(
    ! [B_72,A_73] : k3_xboole_0(B_72,A_73) = k3_xboole_0(A_73,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_614,plain,(
    ! [A_73,B_72] : k2_xboole_0(A_73,k3_xboole_0(B_72,A_73)) = A_73 ),
    inference(superposition,[status(thm),theory(equality)],[c_599,c_6])).

tff(c_1330,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1309,c_614])).

tff(c_14,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_666,plain,(
    ! [A_76,B_77] : k3_tarski(k2_tarski(A_76,B_77)) = k2_xboole_0(A_76,B_77) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_815,plain,(
    ! [A_87,B_88] : k3_tarski(k2_tarski(A_87,B_88)) = k2_xboole_0(B_88,A_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_666])).

tff(c_18,plain,(
    ! [A_16,B_17] : k3_tarski(k2_tarski(A_16,B_17)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_821,plain,(
    ! [B_88,A_87] : k2_xboole_0(B_88,A_87) = k2_xboole_0(A_87,B_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_815,c_18])).

tff(c_596,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_690,plain,(
    ! [A_80,B_81] :
      ( k3_xboole_0(A_80,B_81) = A_80
      | ~ r1_tarski(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_697,plain,(
    k3_xboole_0(k3_subset_1('#skF_1','#skF_2'),'#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_596,c_690])).

tff(c_779,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_697,c_614])).

tff(c_1085,plain,(
    ! [A_99,B_100] :
      ( k4_xboole_0(A_99,B_100) = k3_subset_1(A_99,B_100)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1095,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_1085])).

tff(c_12,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1102,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1095,c_12])).

tff(c_1105,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_821,c_779,c_1102])).

tff(c_1469,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1330,c_1105])).

tff(c_1471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_595,c_1469])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:40:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.62  
% 2.94/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.63  %$ r1_tarski > m1_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.94/1.63  
% 2.94/1.63  %Foreground sorts:
% 2.94/1.63  
% 2.94/1.63  
% 2.94/1.63  %Background operators:
% 2.94/1.63  
% 2.94/1.63  
% 2.94/1.63  %Foreground operators:
% 2.94/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.94/1.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.94/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.94/1.63  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.94/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.94/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.94/1.63  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.94/1.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.94/1.63  tff('#skF_2', type, '#skF_2': $i).
% 2.94/1.63  tff('#skF_1', type, '#skF_1': $i).
% 2.94/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.94/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.94/1.63  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.94/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.94/1.63  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.94/1.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.94/1.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.94/1.63  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.94/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.94/1.63  
% 2.94/1.64  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.94/1.64  tff(f_47, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.94/1.64  tff(f_49, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.94/1.64  tff(f_61, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 2.94/1.64  tff(f_72, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.94/1.64  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.94/1.64  tff(f_79, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 2.94/1.64  tff(f_55, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.94/1.64  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 2.94/1.64  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.94/1.64  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.94/1.64  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.94/1.64  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.94/1.64  tff(f_45, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.94/1.64  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.94/1.64  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.94/1.64  tff(c_10, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.94/1.64  tff(c_20, plain, (![A_18]: (k1_subset_1(A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.94/1.64  tff(c_22, plain, (![A_19]: (k2_subset_1(A_19)=A_19)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.94/1.64  tff(c_30, plain, (![A_25]: (k3_subset_1(A_25, k1_subset_1(A_25))=k2_subset_1(A_25))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.94/1.64  tff(c_47, plain, (![A_25]: (k3_subset_1(A_25, k1_subset_1(A_25))=A_25)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_30])).
% 2.94/1.64  tff(c_51, plain, (![A_25]: (k3_subset_1(A_25, k1_xboole_0)=A_25)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_47])).
% 2.94/1.64  tff(c_36, plain, (![A_30]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.94/1.64  tff(c_582, plain, (![A_70, B_71]: (k3_subset_1(A_70, k3_subset_1(A_70, B_71))=B_71 | ~m1_subset_1(B_71, k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.94/1.64  tff(c_584, plain, (![A_30]: (k3_subset_1(A_30, k3_subset_1(A_30, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_582])).
% 2.94/1.64  tff(c_588, plain, (![A_30]: (k3_subset_1(A_30, A_30)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_51, c_584])).
% 2.94/1.64  tff(c_40, plain, (k2_subset_1('#skF_1')!='#skF_2' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.94/1.64  tff(c_50, plain, ('#skF_2'!='#skF_1' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_40])).
% 2.94/1.64  tff(c_122, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_50])).
% 2.94/1.64  tff(c_46, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | k2_subset_1('#skF_1')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.94/1.64  tff(c_49, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_46])).
% 2.94/1.64  tff(c_281, plain, ('#skF_2'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_122, c_49])).
% 2.94/1.64  tff(c_282, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_281, c_281, c_122])).
% 2.94/1.64  tff(c_591, plain, (~r1_tarski(k1_xboole_0, '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_588, c_282])).
% 2.94/1.64  tff(c_594, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_591])).
% 2.94/1.64  tff(c_595, plain, ('#skF_2'!='#skF_1'), inference(splitRight, [status(thm)], [c_50])).
% 2.94/1.64  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.94/1.64  tff(c_26, plain, (![A_22]: (m1_subset_1(k2_subset_1(A_22), k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.94/1.64  tff(c_48, plain, (![A_22]: (m1_subset_1(A_22, k1_zfmisc_1(A_22)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_26])).
% 2.94/1.64  tff(c_1169, plain, (![A_103, B_104]: (k3_subset_1(A_103, k3_subset_1(A_103, B_104))=B_104 | ~m1_subset_1(B_104, k1_zfmisc_1(A_103)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.94/1.64  tff(c_1173, plain, (![A_30]: (k3_subset_1(A_30, k3_subset_1(A_30, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_1169])).
% 2.94/1.64  tff(c_1178, plain, (![A_30]: (k3_subset_1(A_30, A_30)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_51, c_1173])).
% 2.94/1.64  tff(c_1258, plain, (![B_108, C_109, A_110]: (r1_tarski(B_108, C_109) | ~r1_tarski(k3_subset_1(A_110, C_109), k3_subset_1(A_110, B_108)) | ~m1_subset_1(C_109, k1_zfmisc_1(A_110)) | ~m1_subset_1(B_108, k1_zfmisc_1(A_110)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.94/1.64  tff(c_1261, plain, (![B_108, A_30]: (r1_tarski(B_108, A_30) | ~r1_tarski(k1_xboole_0, k3_subset_1(A_30, B_108)) | ~m1_subset_1(A_30, k1_zfmisc_1(A_30)) | ~m1_subset_1(B_108, k1_zfmisc_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_1178, c_1258])).
% 2.94/1.64  tff(c_1292, plain, (![B_111, A_112]: (r1_tarski(B_111, A_112) | ~m1_subset_1(B_111, k1_zfmisc_1(A_112)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_10, c_1261])).
% 2.94/1.64  tff(c_1302, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_1292])).
% 2.94/1.64  tff(c_8, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.94/1.64  tff(c_1309, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_1302, c_8])).
% 2.94/1.64  tff(c_599, plain, (![B_72, A_73]: (k3_xboole_0(B_72, A_73)=k3_xboole_0(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.94/1.64  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k3_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.94/1.64  tff(c_614, plain, (![A_73, B_72]: (k2_xboole_0(A_73, k3_xboole_0(B_72, A_73))=A_73)), inference(superposition, [status(thm), theory('equality')], [c_599, c_6])).
% 2.94/1.64  tff(c_1330, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1309, c_614])).
% 2.94/1.64  tff(c_14, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.94/1.64  tff(c_666, plain, (![A_76, B_77]: (k3_tarski(k2_tarski(A_76, B_77))=k2_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.94/1.64  tff(c_815, plain, (![A_87, B_88]: (k3_tarski(k2_tarski(A_87, B_88))=k2_xboole_0(B_88, A_87))), inference(superposition, [status(thm), theory('equality')], [c_14, c_666])).
% 2.94/1.64  tff(c_18, plain, (![A_16, B_17]: (k3_tarski(k2_tarski(A_16, B_17))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.94/1.64  tff(c_821, plain, (![B_88, A_87]: (k2_xboole_0(B_88, A_87)=k2_xboole_0(A_87, B_88))), inference(superposition, [status(thm), theory('equality')], [c_815, c_18])).
% 2.94/1.64  tff(c_596, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_50])).
% 2.94/1.64  tff(c_690, plain, (![A_80, B_81]: (k3_xboole_0(A_80, B_81)=A_80 | ~r1_tarski(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.94/1.64  tff(c_697, plain, (k3_xboole_0(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_596, c_690])).
% 2.94/1.64  tff(c_779, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_697, c_614])).
% 2.94/1.64  tff(c_1085, plain, (![A_99, B_100]: (k4_xboole_0(A_99, B_100)=k3_subset_1(A_99, B_100) | ~m1_subset_1(B_100, k1_zfmisc_1(A_99)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.94/1.64  tff(c_1095, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_1085])).
% 2.94/1.64  tff(c_12, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.94/1.64  tff(c_1102, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1095, c_12])).
% 2.94/1.64  tff(c_1105, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_821, c_779, c_1102])).
% 2.94/1.64  tff(c_1469, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1330, c_1105])).
% 2.94/1.64  tff(c_1471, plain, $false, inference(negUnitSimplification, [status(thm)], [c_595, c_1469])).
% 2.94/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.64  
% 2.94/1.64  Inference rules
% 2.94/1.64  ----------------------
% 2.94/1.64  #Ref     : 0
% 2.94/1.64  #Sup     : 341
% 2.94/1.64  #Fact    : 0
% 2.94/1.64  #Define  : 0
% 2.94/1.64  #Split   : 2
% 2.94/1.64  #Chain   : 0
% 2.94/1.64  #Close   : 0
% 2.94/1.64  
% 2.94/1.64  Ordering : KBO
% 2.94/1.64  
% 2.94/1.64  Simplification rules
% 2.94/1.64  ----------------------
% 2.94/1.64  #Subsume      : 7
% 2.94/1.64  #Demod        : 157
% 2.94/1.64  #Tautology    : 274
% 2.94/1.64  #SimpNegUnit  : 3
% 2.94/1.64  #BackRed      : 8
% 2.94/1.64  
% 2.94/1.64  #Partial instantiations: 0
% 2.94/1.64  #Strategies tried      : 1
% 2.94/1.64  
% 2.94/1.64  Timing (in seconds)
% 2.94/1.64  ----------------------
% 3.26/1.64  Preprocessing        : 0.38
% 3.26/1.64  Parsing              : 0.21
% 3.26/1.64  CNF conversion       : 0.02
% 3.26/1.64  Main loop            : 0.41
% 3.26/1.64  Inferencing          : 0.15
% 3.26/1.64  Reduction            : 0.15
% 3.26/1.64  Demodulation         : 0.11
% 3.26/1.65  BG Simplification    : 0.02
% 3.26/1.65  Subsumption          : 0.06
% 3.26/1.65  Abstraction          : 0.02
% 3.26/1.65  MUC search           : 0.00
% 3.26/1.65  Cooper               : 0.00
% 3.26/1.65  Total                : 0.83
% 3.26/1.65  Index Insertion      : 0.00
% 3.26/1.65  Index Deletion       : 0.00
% 3.26/1.65  Index Matching       : 0.00
% 3.26/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
