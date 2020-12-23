%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:37 EST 2020

% Result     : Theorem 4.26s
% Output     : CNFRefutation 4.26s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 247 expanded)
%              Number of leaves         :   30 (  92 expanded)
%              Depth                    :   16
%              Number of atoms          :  139 ( 419 expanded)
%              Number of equality atoms :   38 ( 127 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,C)
            <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_98,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_xboole_1)).

tff(f_57,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(k3_subset_1(A,B),B)
      <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1270,plain,(
    ! [A_136,B_137] :
      ( k4_xboole_0(A_136,B_137) = k3_subset_1(A_136,B_137)
      | ~ m1_subset_1(B_137,k1_zfmisc_1(A_136)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1283,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_1270])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1336,plain,
    ( k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_1'
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1283,c_14])).

tff(c_1677,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1336])).

tff(c_1361,plain,(
    ! [A_139,B_140] :
      ( k3_subset_1(A_139,k3_subset_1(A_139,B_140)) = B_140
      | ~ m1_subset_1(B_140,k1_zfmisc_1(A_139)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1371,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_44,c_1361])).

tff(c_30,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(k3_subset_1(A_20,B_21),k1_zfmisc_1(A_20))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_40,plain,(
    ! [A_30] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_16,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ! [A_37,B_38] : r1_xboole_0(k4_xboole_0(A_37,B_38),k4_xboole_0(B_38,A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    ! [A_10] :
      ( ~ r1_xboole_0(A_10,A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_71,plain,(
    ! [B_38] : k4_xboole_0(B_38,B_38) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_66,c_20])).

tff(c_993,plain,(
    ! [A_119,B_120] :
      ( k2_xboole_0(A_119,k4_xboole_0(B_120,A_119)) = B_120
      | ~ r1_tarski(A_119,B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1005,plain,(
    ! [B_38] :
      ( k2_xboole_0(B_38,k1_xboole_0) = B_38
      | ~ r1_tarski(B_38,B_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_993])).

tff(c_1009,plain,(
    ! [B_38] : k2_xboole_0(B_38,k1_xboole_0) = B_38 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1005])).

tff(c_1048,plain,(
    ! [A_127,B_128] :
      ( k4_xboole_0(k2_xboole_0(A_127,B_128),B_128) = A_127
      | ~ r1_xboole_0(A_127,B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1081,plain,(
    ! [B_38] :
      ( k4_xboole_0(B_38,k1_xboole_0) = B_38
      | ~ r1_xboole_0(B_38,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1009,c_1048])).

tff(c_1088,plain,(
    ! [B_38] : k4_xboole_0(B_38,k1_xboole_0) = B_38 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1081])).

tff(c_1276,plain,(
    ! [A_30] : k4_xboole_0(A_30,k1_xboole_0) = k3_subset_1(A_30,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_40,c_1270])).

tff(c_1282,plain,(
    ! [A_30] : k3_subset_1(A_30,k1_xboole_0) = A_30 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1088,c_1276])).

tff(c_1443,plain,(
    ! [A_146,B_147] :
      ( m1_subset_1(k3_subset_1(A_146,B_147),k1_zfmisc_1(A_146))
      | ~ m1_subset_1(B_147,k1_zfmisc_1(A_146)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1460,plain,(
    ! [A_30] :
      ( m1_subset_1(A_30,k1_zfmisc_1(A_30))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1282,c_1443])).

tff(c_1467,plain,(
    ! [A_30] : m1_subset_1(A_30,k1_zfmisc_1(A_30)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1460])).

tff(c_12,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1365,plain,(
    ! [A_30] : k3_subset_1(A_30,k3_subset_1(A_30,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_1361])).

tff(c_1370,plain,(
    ! [A_30] : k3_subset_1(A_30,A_30) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1282,c_1365])).

tff(c_2382,plain,(
    ! [A_188,B_189] :
      ( k2_subset_1(A_188) = B_189
      | ~ r1_tarski(k3_subset_1(A_188,B_189),B_189)
      | ~ m1_subset_1(B_189,k1_zfmisc_1(A_188)) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2399,plain,(
    ! [A_30] :
      ( k2_subset_1(A_30) = A_30
      | ~ r1_tarski(k1_xboole_0,A_30)
      | ~ m1_subset_1(A_30,k1_zfmisc_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1370,c_2382])).

tff(c_2406,plain,(
    ! [A_30] : k2_subset_1(A_30) = A_30 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1467,c_12,c_2399])).

tff(c_2393,plain,
    ( k3_subset_1('#skF_1','#skF_2') = k2_subset_1('#skF_1')
    | ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1371,c_2382])).

tff(c_2637,plain,
    ( k3_subset_1('#skF_1','#skF_2') = '#skF_1'
    | ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2406,c_2393])).

tff(c_2638,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_2637])).

tff(c_2641,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_2638])).

tff(c_2645,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2641])).

tff(c_2647,plain,(
    m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_2637])).

tff(c_28,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = k3_subset_1(A_18,B_19)
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2652,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2647,c_28])).

tff(c_2656,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1371,c_2652])).

tff(c_918,plain,(
    ! [A_113,B_114,C_115] :
      ( r1_tarski(A_113,B_114)
      | ~ r1_tarski(A_113,k4_xboole_0(B_114,C_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_930,plain,(
    ! [B_114,C_115] : r1_tarski(k4_xboole_0(B_114,C_115),B_114) ),
    inference(resolution,[status(thm)],[c_6,c_918])).

tff(c_2678,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2656,c_930])).

tff(c_2700,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1677,c_2678])).

tff(c_2702,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_1336])).

tff(c_46,plain,
    ( ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3'))
    | ~ r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_87,plain,(
    ~ r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_738,plain,(
    ! [A_97,B_98] :
      ( k4_xboole_0(A_97,B_98) = k3_subset_1(A_97,B_98)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(A_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_752,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_738])).

tff(c_88,plain,(
    ! [A_40,C_41,B_42] :
      ( r1_xboole_0(A_40,C_41)
      | ~ r1_tarski(A_40,k4_xboole_0(B_42,C_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_100,plain,(
    ! [B_42,C_41] : r1_xboole_0(k4_xboole_0(B_42,C_41),C_41) ),
    inference(resolution,[status(thm)],[c_6,c_88])).

tff(c_831,plain,(
    r1_xboole_0(k3_subset_1('#skF_1','#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_752,c_100])).

tff(c_52,plain,
    ( r1_xboole_0('#skF_2','#skF_3')
    | r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_124,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_52])).

tff(c_319,plain,(
    ! [A_68,B_69] :
      ( k4_xboole_0(k2_xboole_0(A_68,B_69),B_69) = A_68
      | ~ r1_xboole_0(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,C_5)
      | ~ r1_tarski(A_3,k4_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_526,plain,(
    ! [A_79,B_80,A_81] :
      ( r1_xboole_0(A_79,B_80)
      | ~ r1_tarski(A_79,A_81)
      | ~ r1_xboole_0(A_81,B_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_8])).

tff(c_542,plain,(
    ! [B_80] :
      ( r1_xboole_0('#skF_2',B_80)
      | ~ r1_xboole_0(k3_subset_1('#skF_1','#skF_3'),B_80) ) ),
    inference(resolution,[status(thm)],[c_124,c_526])).

tff(c_854,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_831,c_542])).

tff(c_858,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_854])).

tff(c_860,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_1280,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_1270])).

tff(c_1642,plain,(
    ! [A_161,B_162,C_163] :
      ( r1_tarski(A_161,k4_xboole_0(B_162,C_163))
      | ~ r1_xboole_0(A_161,C_163)
      | ~ r1_tarski(A_161,B_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3105,plain,(
    ! [A_214] :
      ( r1_tarski(A_214,k3_subset_1('#skF_1','#skF_3'))
      | ~ r1_xboole_0(A_214,'#skF_3')
      | ~ r1_tarski(A_214,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1280,c_1642])).

tff(c_859,plain,(
    ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_3120,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_3')
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_3105,c_859])).

tff(c_3131,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2702,c_860,c_3120])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:37:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.26/1.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.26/1.82  
% 4.26/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.26/1.82  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.26/1.82  
% 4.26/1.82  %Foreground sorts:
% 4.26/1.82  
% 4.26/1.82  
% 4.26/1.82  %Background operators:
% 4.26/1.82  
% 4.26/1.82  
% 4.26/1.82  %Foreground operators:
% 4.26/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.26/1.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.26/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.26/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.26/1.82  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.26/1.82  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.26/1.82  tff('#skF_2', type, '#skF_2': $i).
% 4.26/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.26/1.82  tff('#skF_1', type, '#skF_1': $i).
% 4.26/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.26/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.26/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.26/1.82  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.26/1.82  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.26/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.26/1.82  
% 4.26/1.84  tff(f_108, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 4.26/1.84  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 4.26/1.84  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 4.26/1.84  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.26/1.84  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.26/1.84  tff(f_98, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.26/1.84  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.26/1.84  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.26/1.84  tff(f_59, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_xboole_1)).
% 4.26/1.84  tff(f_57, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 4.26/1.84  tff(f_69, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 4.26/1.84  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.26/1.84  tff(f_96, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 4.26/1.84  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 4.26/1.84  tff(f_65, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 4.26/1.84  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.26/1.84  tff(c_1270, plain, (![A_136, B_137]: (k4_xboole_0(A_136, B_137)=k3_subset_1(A_136, B_137) | ~m1_subset_1(B_137, k1_zfmisc_1(A_136)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.26/1.84  tff(c_1283, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_1270])).
% 4.26/1.84  tff(c_14, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.26/1.84  tff(c_1336, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_1' | ~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1283, c_14])).
% 4.26/1.84  tff(c_1677, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_1336])).
% 4.26/1.84  tff(c_1361, plain, (![A_139, B_140]: (k3_subset_1(A_139, k3_subset_1(A_139, B_140))=B_140 | ~m1_subset_1(B_140, k1_zfmisc_1(A_139)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.26/1.84  tff(c_1371, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_44, c_1361])).
% 4.26/1.84  tff(c_30, plain, (![A_20, B_21]: (m1_subset_1(k3_subset_1(A_20, B_21), k1_zfmisc_1(A_20)) | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.26/1.84  tff(c_40, plain, (![A_30]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.26/1.84  tff(c_16, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.26/1.84  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.26/1.84  tff(c_66, plain, (![A_37, B_38]: (r1_xboole_0(k4_xboole_0(A_37, B_38), k4_xboole_0(B_38, A_37)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.26/1.84  tff(c_20, plain, (![A_10]: (~r1_xboole_0(A_10, A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.26/1.84  tff(c_71, plain, (![B_38]: (k4_xboole_0(B_38, B_38)=k1_xboole_0)), inference(resolution, [status(thm)], [c_66, c_20])).
% 4.26/1.84  tff(c_993, plain, (![A_119, B_120]: (k2_xboole_0(A_119, k4_xboole_0(B_120, A_119))=B_120 | ~r1_tarski(A_119, B_120))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.26/1.84  tff(c_1005, plain, (![B_38]: (k2_xboole_0(B_38, k1_xboole_0)=B_38 | ~r1_tarski(B_38, B_38))), inference(superposition, [status(thm), theory('equality')], [c_71, c_993])).
% 4.26/1.84  tff(c_1009, plain, (![B_38]: (k2_xboole_0(B_38, k1_xboole_0)=B_38)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1005])).
% 4.26/1.84  tff(c_1048, plain, (![A_127, B_128]: (k4_xboole_0(k2_xboole_0(A_127, B_128), B_128)=A_127 | ~r1_xboole_0(A_127, B_128))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.26/1.84  tff(c_1081, plain, (![B_38]: (k4_xboole_0(B_38, k1_xboole_0)=B_38 | ~r1_xboole_0(B_38, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1009, c_1048])).
% 4.26/1.84  tff(c_1088, plain, (![B_38]: (k4_xboole_0(B_38, k1_xboole_0)=B_38)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1081])).
% 4.26/1.84  tff(c_1276, plain, (![A_30]: (k4_xboole_0(A_30, k1_xboole_0)=k3_subset_1(A_30, k1_xboole_0))), inference(resolution, [status(thm)], [c_40, c_1270])).
% 4.26/1.84  tff(c_1282, plain, (![A_30]: (k3_subset_1(A_30, k1_xboole_0)=A_30)), inference(demodulation, [status(thm), theory('equality')], [c_1088, c_1276])).
% 4.26/1.84  tff(c_1443, plain, (![A_146, B_147]: (m1_subset_1(k3_subset_1(A_146, B_147), k1_zfmisc_1(A_146)) | ~m1_subset_1(B_147, k1_zfmisc_1(A_146)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.26/1.84  tff(c_1460, plain, (![A_30]: (m1_subset_1(A_30, k1_zfmisc_1(A_30)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_1282, c_1443])).
% 4.26/1.84  tff(c_1467, plain, (![A_30]: (m1_subset_1(A_30, k1_zfmisc_1(A_30)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1460])).
% 4.26/1.84  tff(c_12, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.26/1.84  tff(c_1365, plain, (![A_30]: (k3_subset_1(A_30, k3_subset_1(A_30, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_1361])).
% 4.26/1.84  tff(c_1370, plain, (![A_30]: (k3_subset_1(A_30, A_30)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1282, c_1365])).
% 4.26/1.84  tff(c_2382, plain, (![A_188, B_189]: (k2_subset_1(A_188)=B_189 | ~r1_tarski(k3_subset_1(A_188, B_189), B_189) | ~m1_subset_1(B_189, k1_zfmisc_1(A_188)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 4.26/1.84  tff(c_2399, plain, (![A_30]: (k2_subset_1(A_30)=A_30 | ~r1_tarski(k1_xboole_0, A_30) | ~m1_subset_1(A_30, k1_zfmisc_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_1370, c_2382])).
% 4.26/1.84  tff(c_2406, plain, (![A_30]: (k2_subset_1(A_30)=A_30)), inference(demodulation, [status(thm), theory('equality')], [c_1467, c_12, c_2399])).
% 4.26/1.84  tff(c_2393, plain, (k3_subset_1('#skF_1', '#skF_2')=k2_subset_1('#skF_1') | ~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1371, c_2382])).
% 4.26/1.84  tff(c_2637, plain, (k3_subset_1('#skF_1', '#skF_2')='#skF_1' | ~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2406, c_2393])).
% 4.26/1.84  tff(c_2638, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_2637])).
% 4.26/1.84  tff(c_2641, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_30, c_2638])).
% 4.26/1.84  tff(c_2645, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_2641])).
% 4.26/1.84  tff(c_2647, plain, (m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_2637])).
% 4.26/1.84  tff(c_28, plain, (![A_18, B_19]: (k4_xboole_0(A_18, B_19)=k3_subset_1(A_18, B_19) | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.26/1.84  tff(c_2652, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_2647, c_28])).
% 4.26/1.84  tff(c_2656, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1371, c_2652])).
% 4.26/1.84  tff(c_918, plain, (![A_113, B_114, C_115]: (r1_tarski(A_113, B_114) | ~r1_tarski(A_113, k4_xboole_0(B_114, C_115)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.26/1.84  tff(c_930, plain, (![B_114, C_115]: (r1_tarski(k4_xboole_0(B_114, C_115), B_114))), inference(resolution, [status(thm)], [c_6, c_918])).
% 4.26/1.84  tff(c_2678, plain, (r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2656, c_930])).
% 4.26/1.84  tff(c_2700, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1677, c_2678])).
% 4.26/1.84  tff(c_2702, plain, (r1_tarski('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_1336])).
% 4.26/1.84  tff(c_46, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3')) | ~r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.26/1.84  tff(c_87, plain, (~r1_xboole_0('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_46])).
% 4.26/1.84  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.26/1.84  tff(c_738, plain, (![A_97, B_98]: (k4_xboole_0(A_97, B_98)=k3_subset_1(A_97, B_98) | ~m1_subset_1(B_98, k1_zfmisc_1(A_97)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.26/1.84  tff(c_752, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_738])).
% 4.26/1.84  tff(c_88, plain, (![A_40, C_41, B_42]: (r1_xboole_0(A_40, C_41) | ~r1_tarski(A_40, k4_xboole_0(B_42, C_41)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.26/1.84  tff(c_100, plain, (![B_42, C_41]: (r1_xboole_0(k4_xboole_0(B_42, C_41), C_41))), inference(resolution, [status(thm)], [c_6, c_88])).
% 4.26/1.84  tff(c_831, plain, (r1_xboole_0(k3_subset_1('#skF_1', '#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_752, c_100])).
% 4.26/1.84  tff(c_52, plain, (r1_xboole_0('#skF_2', '#skF_3') | r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.26/1.84  tff(c_124, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_87, c_52])).
% 4.26/1.84  tff(c_319, plain, (![A_68, B_69]: (k4_xboole_0(k2_xboole_0(A_68, B_69), B_69)=A_68 | ~r1_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.26/1.84  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, C_5) | ~r1_tarski(A_3, k4_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.26/1.84  tff(c_526, plain, (![A_79, B_80, A_81]: (r1_xboole_0(A_79, B_80) | ~r1_tarski(A_79, A_81) | ~r1_xboole_0(A_81, B_80))), inference(superposition, [status(thm), theory('equality')], [c_319, c_8])).
% 4.26/1.84  tff(c_542, plain, (![B_80]: (r1_xboole_0('#skF_2', B_80) | ~r1_xboole_0(k3_subset_1('#skF_1', '#skF_3'), B_80))), inference(resolution, [status(thm)], [c_124, c_526])).
% 4.26/1.84  tff(c_854, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_831, c_542])).
% 4.26/1.84  tff(c_858, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_854])).
% 4.26/1.84  tff(c_860, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_46])).
% 4.26/1.84  tff(c_1280, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_1270])).
% 4.26/1.84  tff(c_1642, plain, (![A_161, B_162, C_163]: (r1_tarski(A_161, k4_xboole_0(B_162, C_163)) | ~r1_xboole_0(A_161, C_163) | ~r1_tarski(A_161, B_162))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.26/1.84  tff(c_3105, plain, (![A_214]: (r1_tarski(A_214, k3_subset_1('#skF_1', '#skF_3')) | ~r1_xboole_0(A_214, '#skF_3') | ~r1_tarski(A_214, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1280, c_1642])).
% 4.26/1.84  tff(c_859, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_46])).
% 4.26/1.84  tff(c_3120, plain, (~r1_xboole_0('#skF_2', '#skF_3') | ~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_3105, c_859])).
% 4.26/1.84  tff(c_3131, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2702, c_860, c_3120])).
% 4.26/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.26/1.84  
% 4.26/1.84  Inference rules
% 4.26/1.84  ----------------------
% 4.26/1.84  #Ref     : 0
% 4.26/1.84  #Sup     : 734
% 4.26/1.84  #Fact    : 0
% 4.26/1.84  #Define  : 0
% 4.26/1.84  #Split   : 15
% 4.26/1.84  #Chain   : 0
% 4.26/1.84  #Close   : 0
% 4.26/1.84  
% 4.26/1.84  Ordering : KBO
% 4.26/1.84  
% 4.26/1.84  Simplification rules
% 4.26/1.84  ----------------------
% 4.26/1.84  #Subsume      : 29
% 4.26/1.84  #Demod        : 377
% 4.26/1.84  #Tautology    : 359
% 4.26/1.84  #SimpNegUnit  : 5
% 4.26/1.84  #BackRed      : 4
% 4.26/1.84  
% 4.26/1.84  #Partial instantiations: 0
% 4.26/1.84  #Strategies tried      : 1
% 4.26/1.84  
% 4.26/1.84  Timing (in seconds)
% 4.26/1.84  ----------------------
% 4.26/1.84  Preprocessing        : 0.31
% 4.26/1.84  Parsing              : 0.16
% 4.26/1.84  CNF conversion       : 0.02
% 4.26/1.84  Main loop            : 0.67
% 4.26/1.84  Inferencing          : 0.24
% 4.26/1.84  Reduction            : 0.23
% 4.26/1.84  Demodulation         : 0.17
% 4.26/1.84  BG Simplification    : 0.03
% 4.26/1.84  Subsumption          : 0.12
% 4.26/1.84  Abstraction          : 0.03
% 4.26/1.84  MUC search           : 0.00
% 4.26/1.84  Cooper               : 0.00
% 4.26/1.84  Total                : 1.01
% 4.26/1.84  Index Insertion      : 0.00
% 4.26/1.84  Index Deletion       : 0.00
% 4.26/1.84  Index Matching       : 0.00
% 4.26/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
