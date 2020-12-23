%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:24 EST 2020

% Result     : Theorem 14.81s
% Output     : CNFRefutation 15.02s
% Verified   : 
% Statistics : Number of formulae       :  200 ( 808 expanded)
%              Number of leaves         :   37 ( 278 expanded)
%              Depth                    :   19
%              Number of atoms          :  305 (1515 expanded)
%              Number of equality atoms :  144 ( 623 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_2 > #skF_7 > #skF_9 > #skF_3 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_45,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_105,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_63,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_96,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
          | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
        & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(c_29487,plain,(
    ! [A_894,B_895] :
      ( r1_tarski(A_894,B_895)
      | k4_xboole_0(A_894,B_895) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_124,plain,(
    ! [A_72,B_73] :
      ( r1_tarski(A_72,B_73)
      | k4_xboole_0(A_72,B_73) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_78,plain,
    ( ~ r1_tarski('#skF_10','#skF_12')
    | ~ r1_tarski('#skF_9','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_101,plain,(
    ~ r1_tarski('#skF_9','#skF_11') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_132,plain,(
    k4_xboole_0('#skF_9','#skF_11') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_124,c_101])).

tff(c_102,plain,(
    ! [A_69,B_70] :
      ( k4_xboole_0(A_69,B_70) = k1_xboole_0
      | ~ r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_106,plain,(
    ! [B_8] : k4_xboole_0(B_8,B_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_102])).

tff(c_40,plain,(
    ! [A_19] : k4_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_26,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | k4_xboole_0(A_9,B_10) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_297,plain,(
    ! [A_98,B_99,C_100] :
      ( r1_tarski(A_98,B_99)
      | ~ r1_tarski(A_98,k4_xboole_0(B_99,C_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_551,plain,(
    ! [A_113,B_114] :
      ( r1_tarski(A_113,B_114)
      | ~ r1_tarski(A_113,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_297])).

tff(c_563,plain,(
    ! [A_9,B_114] :
      ( r1_tarski(A_9,B_114)
      | k4_xboole_0(A_9,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_551])).

tff(c_579,plain,(
    ! [A_115,B_116] :
      ( r1_tarski(A_115,B_116)
      | k1_xboole_0 != A_115 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_563])).

tff(c_34,plain,(
    ! [A_14,B_15] :
      ( k3_xboole_0(A_14,B_15) = A_14
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_614,plain,(
    ! [A_115,B_116] :
      ( k3_xboole_0(A_115,B_116) = A_115
      | k1_xboole_0 != A_115 ) ),
    inference(resolution,[status(thm)],[c_579,c_34])).

tff(c_3715,plain,(
    ! [A_236,C_237,B_238,D_239] : k3_xboole_0(k2_zfmisc_1(A_236,C_237),k2_zfmisc_1(B_238,D_239)) = k2_zfmisc_1(k3_xboole_0(A_236,B_238),k3_xboole_0(C_237,D_239)) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_82,plain,(
    r1_tarski(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1('#skF_11','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_163,plain,(
    ! [A_77,B_78] :
      ( k3_xboole_0(A_77,B_78) = A_77
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_173,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1('#skF_11','#skF_12')) = k2_zfmisc_1('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_82,c_163])).

tff(c_3766,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_9','#skF_11'),k3_xboole_0('#skF_10','#skF_12')) = k2_zfmisc_1('#skF_9','#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_3715,c_173])).

tff(c_4166,plain,
    ( k2_zfmisc_1(k3_xboole_0('#skF_9','#skF_11'),'#skF_10') = k2_zfmisc_1('#skF_9','#skF_10')
    | k1_xboole_0 != '#skF_10' ),
    inference(superposition,[status(thm),theory(equality)],[c_614,c_3766])).

tff(c_4765,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_4166])).

tff(c_42,plain,(
    ! [A_20,B_21] : k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_321,plain,(
    ! [B_102,C_103] : r1_tarski(k4_xboole_0(B_102,C_103),B_102) ),
    inference(resolution,[status(thm)],[c_24,c_297])).

tff(c_484,plain,(
    ! [A_107,B_108] : r1_tarski(k3_xboole_0(A_107,B_108),A_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_321])).

tff(c_28,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = k1_xboole_0
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_520,plain,(
    ! [A_107,B_108] : k4_xboole_0(k3_xboole_0(A_107,B_108),A_107) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_484,c_28])).

tff(c_618,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(resolution,[status(thm)],[c_579,c_101])).

tff(c_345,plain,(
    ! [A_20,B_21] : r1_tarski(k3_xboole_0(A_20,B_21),A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_321])).

tff(c_74,plain,(
    ! [A_59,C_61,B_60] :
      ( r1_tarski(k2_zfmisc_1(A_59,C_61),k2_zfmisc_1(B_60,C_61))
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_6232,plain,(
    ! [B_304] :
      ( r1_tarski(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1(B_304,k3_xboole_0('#skF_10','#skF_12')))
      | ~ r1_tarski(k3_xboole_0('#skF_9','#skF_11'),B_304) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3766,c_74])).

tff(c_68,plain,(
    ! [A_56,B_57,C_58] :
      ( ~ r1_tarski(k2_zfmisc_1(A_56,B_57),k2_zfmisc_1(A_56,C_58))
      | r1_tarski(B_57,C_58)
      | k1_xboole_0 = A_56 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6241,plain,
    ( r1_tarski('#skF_10',k3_xboole_0('#skF_10','#skF_12'))
    | k1_xboole_0 = '#skF_9'
    | ~ r1_tarski(k3_xboole_0('#skF_9','#skF_11'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_6232,c_68])).

tff(c_6269,plain,
    ( r1_tarski('#skF_10',k3_xboole_0('#skF_10','#skF_12'))
    | k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_6241])).

tff(c_6270,plain,(
    r1_tarski('#skF_10',k3_xboole_0('#skF_10','#skF_12')) ),
    inference(negUnitSimplification,[status(thm)],[c_618,c_6269])).

tff(c_525,plain,(
    ! [B_109,A_110] :
      ( B_109 = A_110
      | ~ r1_tarski(B_109,A_110)
      | ~ r1_tarski(A_110,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_542,plain,(
    ! [B_10,A_9] :
      ( B_10 = A_9
      | ~ r1_tarski(B_10,A_9)
      | k4_xboole_0(A_9,B_10) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_525])).

tff(c_6283,plain,
    ( k3_xboole_0('#skF_10','#skF_12') = '#skF_10'
    | k4_xboole_0(k3_xboole_0('#skF_10','#skF_12'),'#skF_10') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6270,c_542])).

tff(c_6311,plain,(
    k3_xboole_0('#skF_10','#skF_12') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_520,c_6283])).

tff(c_72,plain,(
    ! [C_61,A_59,B_60] :
      ( r1_tarski(k2_zfmisc_1(C_61,A_59),k2_zfmisc_1(C_61,B_60))
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_4144,plain,(
    ! [B_60] :
      ( r1_tarski(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1(k3_xboole_0('#skF_9','#skF_11'),B_60))
      | ~ r1_tarski(k3_xboole_0('#skF_10','#skF_12'),B_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3766,c_72])).

tff(c_7118,plain,(
    ! [B_326] :
      ( r1_tarski(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1(k3_xboole_0('#skF_9','#skF_11'),B_326))
      | ~ r1_tarski('#skF_10',B_326) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6311,c_4144])).

tff(c_70,plain,(
    ! [B_57,A_56,C_58] :
      ( ~ r1_tarski(k2_zfmisc_1(B_57,A_56),k2_zfmisc_1(C_58,A_56))
      | r1_tarski(B_57,C_58)
      | k1_xboole_0 = A_56 ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_7133,plain,
    ( r1_tarski('#skF_9',k3_xboole_0('#skF_9','#skF_11'))
    | k1_xboole_0 = '#skF_10'
    | ~ r1_tarski('#skF_10','#skF_10') ),
    inference(resolution,[status(thm)],[c_7118,c_70])).

tff(c_7164,plain,
    ( r1_tarski('#skF_9',k3_xboole_0('#skF_9','#skF_11'))
    | k1_xboole_0 = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_7133])).

tff(c_7165,plain,(
    r1_tarski('#skF_9',k3_xboole_0('#skF_9','#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_4765,c_7164])).

tff(c_319,plain,(
    ! [B_99,C_100] : r1_tarski(k4_xboole_0(B_99,C_100),B_99) ),
    inference(resolution,[status(thm)],[c_24,c_297])).

tff(c_5709,plain,(
    ! [B_288,C_289] :
      ( k4_xboole_0(B_288,C_289) = B_288
      | ~ r1_tarski(B_288,k4_xboole_0(B_288,C_289)) ) ),
    inference(resolution,[status(thm)],[c_319,c_525])).

tff(c_5766,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0(A_20,k4_xboole_0(A_20,B_21)) = A_20
      | ~ r1_tarski(A_20,k3_xboole_0(A_20,B_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_5709])).

tff(c_5796,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,B_21) = A_20
      | ~ r1_tarski(A_20,k3_xboole_0(A_20,B_21)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_5766])).

tff(c_7210,plain,(
    k3_xboole_0('#skF_9','#skF_11') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_7165,c_5796])).

tff(c_195,plain,(
    ! [A_80,B_81] : k4_xboole_0(A_80,k4_xboole_0(A_80,B_81)) = k3_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10465,plain,(
    ! [A_449,B_450] : k4_xboole_0(A_449,k3_xboole_0(A_449,B_450)) = k3_xboole_0(A_449,k4_xboole_0(A_449,B_450)) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_195])).

tff(c_10738,plain,(
    k3_xboole_0('#skF_9',k4_xboole_0('#skF_9','#skF_11')) = k4_xboole_0('#skF_9','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_7210,c_10465])).

tff(c_10842,plain,(
    k3_xboole_0('#skF_9',k4_xboole_0('#skF_9','#skF_11')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_10738])).

tff(c_5260,plain,(
    ! [B_281,A_282] :
      ( B_281 = A_282
      | ~ r1_tarski(B_281,A_282)
      | k4_xboole_0(A_282,B_281) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_525])).

tff(c_5293,plain,(
    ! [B_99,C_100] :
      ( k4_xboole_0(B_99,C_100) = B_99
      | k4_xboole_0(B_99,k4_xboole_0(B_99,C_100)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_319,c_5260])).

tff(c_5321,plain,(
    ! [B_283,C_284] :
      ( k4_xboole_0(B_283,C_284) = B_283
      | k3_xboole_0(B_283,C_284) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_5293])).

tff(c_38,plain,(
    ! [A_17,B_18] :
      ( k1_xboole_0 = A_17
      | ~ r1_tarski(A_17,k4_xboole_0(B_18,A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6980,plain,(
    ! [C_321,B_322] :
      ( k1_xboole_0 = C_321
      | ~ r1_tarski(C_321,B_322)
      | k3_xboole_0(B_322,C_321) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5321,c_38])).

tff(c_14670,plain,(
    ! [B_494,C_495] :
      ( k4_xboole_0(B_494,C_495) = k1_xboole_0
      | k3_xboole_0(B_494,k4_xboole_0(B_494,C_495)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_319,c_6980])).

tff(c_14688,plain,(
    k4_xboole_0('#skF_9','#skF_11') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10842,c_14670])).

tff(c_14781,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_132,c_14688])).

tff(c_14783,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_4166])).

tff(c_14834,plain,(
    ! [B_8] : k4_xboole_0(B_8,B_8) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14783,c_106])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_15666,plain,(
    ! [A_533,B_534,C_535] :
      ( ~ r2_hidden('#skF_1'(A_533,B_534,C_535),B_534)
      | r2_hidden('#skF_2'(A_533,B_534,C_535),C_535)
      | k4_xboole_0(A_533,B_534) = C_535 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_15669,plain,(
    ! [A_1,C_3] :
      ( r2_hidden('#skF_2'(A_1,A_1,C_3),C_3)
      | k4_xboole_0(A_1,A_1) = C_3 ) ),
    inference(resolution,[status(thm)],[c_18,c_15666])).

tff(c_15674,plain,(
    ! [A_1,C_3] :
      ( r2_hidden('#skF_2'(A_1,A_1,C_3),C_3)
      | C_3 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14834,c_15669])).

tff(c_4172,plain,(
    ! [A_246,B_247,D_248] :
      ( r2_hidden('#skF_8'(A_246,B_247,k2_zfmisc_1(A_246,B_247),D_248),B_247)
      | ~ r2_hidden(D_248,k2_zfmisc_1(A_246,B_247)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4204,plain,(
    ! [A_246,A_1,B_2,D_248] :
      ( r2_hidden('#skF_8'(A_246,k4_xboole_0(A_1,B_2),k2_zfmisc_1(A_246,k4_xboole_0(A_1,B_2)),D_248),A_1)
      | ~ r2_hidden(D_248,k2_zfmisc_1(A_246,k4_xboole_0(A_1,B_2))) ) ),
    inference(resolution,[status(thm)],[c_4172,c_6])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_29149,plain,(
    ! [A_885,A_886,B_887,D_888] :
      ( ~ r2_hidden('#skF_8'(A_885,k4_xboole_0(A_886,B_887),k2_zfmisc_1(A_885,k4_xboole_0(A_886,B_887)),D_888),B_887)
      | ~ r2_hidden(D_888,k2_zfmisc_1(A_885,k4_xboole_0(A_886,B_887))) ) ),
    inference(resolution,[status(thm)],[c_4172,c_4])).

tff(c_29153,plain,(
    ! [D_248,A_246,A_1] : ~ r2_hidden(D_248,k2_zfmisc_1(A_246,k4_xboole_0(A_1,A_1))) ),
    inference(resolution,[status(thm)],[c_4204,c_29149])).

tff(c_29328,plain,(
    ! [D_889,A_890] : ~ r2_hidden(D_889,k2_zfmisc_1(A_890,'#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14834,c_29153])).

tff(c_29412,plain,(
    ! [A_890] : k2_zfmisc_1(A_890,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_15674,c_29328])).

tff(c_80,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_14837,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14783,c_80])).

tff(c_136,plain,(
    k4_xboole_0(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1('#skF_11','#skF_12')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_82,c_28])).

tff(c_14828,plain,(
    k4_xboole_0(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1('#skF_11','#skF_12')) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14783,c_136])).

tff(c_20394,plain,(
    ! [B_685,C_686] :
      ( k4_xboole_0(B_685,C_686) = B_685
      | ~ r1_tarski(B_685,k4_xboole_0(B_685,C_686)) ) ),
    inference(resolution,[status(thm)],[c_319,c_525])).

tff(c_20455,plain,
    ( k4_xboole_0(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1('#skF_11','#skF_12')) = k2_zfmisc_1('#skF_9','#skF_10')
    | ~ r1_tarski(k2_zfmisc_1('#skF_9','#skF_10'),'#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_14828,c_20394])).

tff(c_20483,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') = '#skF_10'
    | ~ r1_tarski(k2_zfmisc_1('#skF_9','#skF_10'),'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14828,c_20455])).

tff(c_20484,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_9','#skF_10'),'#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_14837,c_20483])).

tff(c_29437,plain,(
    ~ r1_tarski('#skF_10','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29412,c_20484])).

tff(c_29450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_29437])).

tff(c_29451,plain,(
    ~ r1_tarski('#skF_10','#skF_12') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_29495,plain,(
    k4_xboole_0('#skF_10','#skF_12') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_29487,c_29451])).

tff(c_29622,plain,(
    ! [A_907,B_908,C_909] :
      ( r1_tarski(A_907,B_908)
      | ~ r1_tarski(A_907,k4_xboole_0(B_908,C_909)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_29647,plain,(
    ! [B_908,C_909] : r1_tarski(k4_xboole_0(B_908,C_909),B_908) ),
    inference(resolution,[status(thm)],[c_24,c_29622])).

tff(c_29648,plain,(
    ! [B_910,C_911] : r1_tarski(k4_xboole_0(B_910,C_911),B_910) ),
    inference(resolution,[status(thm)],[c_24,c_29622])).

tff(c_29665,plain,(
    ! [A_20,B_21] : r1_tarski(k3_xboole_0(A_20,B_21),A_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_29648])).

tff(c_29453,plain,(
    ! [A_891,B_892] :
      ( k4_xboole_0(A_891,B_892) = k1_xboole_0
      | ~ r1_tarski(A_891,B_892) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_29465,plain,(
    ! [B_8] : k4_xboole_0(B_8,B_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_29453])).

tff(c_30001,plain,(
    ! [A_928,B_929] :
      ( r1_tarski(A_928,B_929)
      | ~ r1_tarski(A_928,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29465,c_29622])).

tff(c_30013,plain,(
    ! [A_9,B_929] :
      ( r1_tarski(A_9,B_929)
      | k4_xboole_0(A_9,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_30001])).

tff(c_30024,plain,(
    ! [A_9,B_929] :
      ( r1_tarski(A_9,B_929)
      | k1_xboole_0 != A_9 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_30013])).

tff(c_29452,plain,(
    r1_tarski('#skF_9','#skF_11') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_29463,plain,(
    k4_xboole_0('#skF_9','#skF_11') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_29452,c_29453])).

tff(c_29866,plain,(
    ! [A_921] :
      ( r1_tarski(A_921,'#skF_9')
      | ~ r1_tarski(A_921,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29463,c_29622])).

tff(c_29882,plain,(
    ! [A_9] :
      ( r1_tarski(A_9,'#skF_9')
      | k4_xboole_0(A_9,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_29866])).

tff(c_29898,plain,(
    ! [A_922] :
      ( r1_tarski(A_922,'#skF_9')
      | k1_xboole_0 != A_922 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_29882])).

tff(c_20,plain,(
    ! [B_8,A_7] :
      ( B_8 = A_7
      | ~ r1_tarski(B_8,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_30942,plain,(
    ! [A_982] :
      ( A_982 = '#skF_9'
      | ~ r1_tarski('#skF_9',A_982)
      | k1_xboole_0 != A_982 ) ),
    inference(resolution,[status(thm)],[c_29898,c_20])).

tff(c_30958,plain,(
    ! [B_929] :
      ( B_929 = '#skF_9'
      | k1_xboole_0 != B_929
      | k1_xboole_0 != '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_30024,c_30942])).

tff(c_30963,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_30958])).

tff(c_29532,plain,(
    ! [A_899,B_900] :
      ( k3_xboole_0(A_899,B_900) = A_899
      | ~ r1_tarski(A_899,B_900) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_29546,plain,(
    k3_xboole_0('#skF_9','#skF_11') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_29452,c_29532])).

tff(c_32768,plain,(
    ! [A_1045,C_1046,B_1047,D_1048] : k3_xboole_0(k2_zfmisc_1(A_1045,C_1046),k2_zfmisc_1(B_1047,D_1048)) = k2_zfmisc_1(k3_xboole_0(A_1045,B_1047),k3_xboole_0(C_1046,D_1048)) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_29547,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1('#skF_11','#skF_12')) = k2_zfmisc_1('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_82,c_29532])).

tff(c_32816,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_9','#skF_11'),k3_xboole_0('#skF_10','#skF_12')) = k2_zfmisc_1('#skF_9','#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_32768,c_29547])).

tff(c_32839,plain,(
    k2_zfmisc_1('#skF_9',k3_xboole_0('#skF_10','#skF_12')) = k2_zfmisc_1('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29546,c_32816])).

tff(c_34695,plain,(
    ! [B_1105] :
      ( r1_tarski(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1(B_1105,k3_xboole_0('#skF_10','#skF_12')))
      | ~ r1_tarski('#skF_9',B_1105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32839,c_74])).

tff(c_34707,plain,
    ( r1_tarski('#skF_10',k3_xboole_0('#skF_10','#skF_12'))
    | k1_xboole_0 = '#skF_9'
    | ~ r1_tarski('#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_34695,c_68])).

tff(c_34732,plain,
    ( r1_tarski('#skF_10',k3_xboole_0('#skF_10','#skF_12'))
    | k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_34707])).

tff(c_34733,plain,(
    r1_tarski('#skF_10',k3_xboole_0('#skF_10','#skF_12')) ),
    inference(negUnitSimplification,[status(thm)],[c_30963,c_34732])).

tff(c_34752,plain,
    ( k3_xboole_0('#skF_10','#skF_12') = '#skF_10'
    | ~ r1_tarski(k3_xboole_0('#skF_10','#skF_12'),'#skF_10') ),
    inference(resolution,[status(thm)],[c_34733,c_20])).

tff(c_34774,plain,(
    k3_xboole_0('#skF_10','#skF_12') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29665,c_34752])).

tff(c_29572,plain,(
    ! [A_902,B_903] : k4_xboole_0(A_902,k4_xboole_0(A_902,B_903)) = k3_xboole_0(A_902,B_903) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_42239,plain,(
    ! [A_1311,B_1312] :
      ( k4_xboole_0(A_1311,B_1312) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(A_1311,B_1312),k3_xboole_0(A_1311,B_1312)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_29572,c_38])).

tff(c_42264,plain,
    ( k4_xboole_0('#skF_10','#skF_12') = k1_xboole_0
    | ~ r1_tarski(k4_xboole_0('#skF_10','#skF_12'),'#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_34774,c_42239])).

tff(c_42372,plain,(
    k4_xboole_0('#skF_10','#skF_12') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_29647,c_42264])).

tff(c_42374,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_29495,c_42372])).

tff(c_42376,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_30958])).

tff(c_42399,plain,(
    ! [B_8] : k4_xboole_0(B_8,B_8) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42376,c_29465])).

tff(c_45424,plain,(
    ! [A_1432,B_1433,C_1434] :
      ( ~ r2_hidden('#skF_1'(A_1432,B_1433,C_1434),B_1433)
      | r2_hidden('#skF_2'(A_1432,B_1433,C_1434),C_1434)
      | k4_xboole_0(A_1432,B_1433) = C_1434 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_45427,plain,(
    ! [A_1,C_3] :
      ( r2_hidden('#skF_2'(A_1,A_1,C_3),C_3)
      | k4_xboole_0(A_1,A_1) = C_3 ) ),
    inference(resolution,[status(thm)],[c_18,c_45424])).

tff(c_45435,plain,(
    ! [A_1,C_3] :
      ( r2_hidden('#skF_2'(A_1,A_1,C_3),C_3)
      | C_3 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42399,c_45427])).

tff(c_43394,plain,(
    ! [A_1356,B_1357,D_1358] :
      ( r2_hidden('#skF_7'(A_1356,B_1357,k2_zfmisc_1(A_1356,B_1357),D_1358),A_1356)
      | ~ r2_hidden(D_1358,k2_zfmisc_1(A_1356,B_1357)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_43411,plain,(
    ! [A_1,B_2,B_1357,D_1358] :
      ( r2_hidden('#skF_7'(k4_xboole_0(A_1,B_2),B_1357,k2_zfmisc_1(k4_xboole_0(A_1,B_2),B_1357),D_1358),A_1)
      | ~ r2_hidden(D_1358,k2_zfmisc_1(k4_xboole_0(A_1,B_2),B_1357)) ) ),
    inference(resolution,[status(thm)],[c_43394,c_6])).

tff(c_65549,plain,(
    ! [A_1797,B_1798,B_1799,D_1800] :
      ( ~ r2_hidden('#skF_7'(k4_xboole_0(A_1797,B_1798),B_1799,k2_zfmisc_1(k4_xboole_0(A_1797,B_1798),B_1799),D_1800),B_1798)
      | ~ r2_hidden(D_1800,k2_zfmisc_1(k4_xboole_0(A_1797,B_1798),B_1799)) ) ),
    inference(resolution,[status(thm)],[c_43394,c_4])).

tff(c_65571,plain,(
    ! [D_1358,A_1,B_1357] : ~ r2_hidden(D_1358,k2_zfmisc_1(k4_xboole_0(A_1,A_1),B_1357)) ),
    inference(resolution,[status(thm)],[c_43411,c_65549])).

tff(c_65834,plain,(
    ! [D_1801,B_1802] : ~ r2_hidden(D_1801,k2_zfmisc_1('#skF_9',B_1802)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42399,c_65571])).

tff(c_65920,plain,(
    ! [B_1802] : k2_zfmisc_1('#skF_9',B_1802) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_45435,c_65834])).

tff(c_42403,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42376,c_80])).

tff(c_29548,plain,(
    ! [B_8] : k3_xboole_0(B_8,B_8) = B_8 ),
    inference(resolution,[status(thm)],[c_24,c_29532])).

tff(c_76,plain,(
    ! [A_62,C_64,B_63,D_65] : k3_xboole_0(k2_zfmisc_1(A_62,C_64),k2_zfmisc_1(B_63,D_65)) = k2_zfmisc_1(k3_xboole_0(A_62,B_63),k3_xboole_0(C_64,D_65)) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_29834,plain,(
    ! [B_917,A_918] :
      ( B_917 = A_918
      | ~ r1_tarski(B_917,A_918)
      | ~ r1_tarski(A_918,B_917) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_29852,plain,(
    ! [B_10,A_9] :
      ( B_10 = A_9
      | ~ r1_tarski(B_10,A_9)
      | k4_xboole_0(A_9,B_10) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_29834])).

tff(c_47874,plain,(
    ! [B_1521,A_1522] :
      ( B_1521 = A_1522
      | ~ r1_tarski(B_1521,A_1522)
      | k4_xboole_0(A_1522,B_1521) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42376,c_29852])).

tff(c_47913,plain,(
    ! [B_908,C_909] :
      ( k4_xboole_0(B_908,C_909) = B_908
      | k4_xboole_0(B_908,k4_xboole_0(B_908,C_909)) != '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_29647,c_47874])).

tff(c_47933,plain,(
    ! [B_908,C_909] :
      ( k4_xboole_0(B_908,C_909) = B_908
      | k3_xboole_0(B_908,C_909) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_47913])).

tff(c_36,plain,(
    ! [A_16] : k3_xboole_0(A_16,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_42480,plain,(
    ! [A_1315] : k3_xboole_0(A_1315,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42376,c_42376,c_36])).

tff(c_32,plain,(
    ! [A_11,B_12,C_13] :
      ( r1_tarski(A_11,B_12)
      | ~ r1_tarski(A_11,k4_xboole_0(B_12,C_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_30640,plain,(
    ! [B_970,C_971,C_972] : r1_tarski(k4_xboole_0(k4_xboole_0(B_970,C_971),C_972),B_970) ),
    inference(resolution,[status(thm)],[c_29648,c_32])).

tff(c_30686,plain,(
    ! [B_970,C_971,B_21] : r1_tarski(k3_xboole_0(k4_xboole_0(B_970,C_971),B_21),B_970) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_30640])).

tff(c_42514,plain,(
    ! [B_1316] : r1_tarski('#skF_9',B_1316) ),
    inference(superposition,[status(thm),theory(equality)],[c_42480,c_30686])).

tff(c_42532,plain,(
    ! [B_1316] : k3_xboole_0('#skF_9',B_1316) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_42514,c_34])).

tff(c_42973,plain,(
    ! [A_1338,C_1339,B_1340,D_1341] : k3_xboole_0(k2_zfmisc_1(A_1338,C_1339),k2_zfmisc_1(B_1340,D_1341)) = k2_zfmisc_1(k3_xboole_0(A_1338,B_1340),k3_xboole_0(C_1339,D_1341)) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_42988,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_9','#skF_11'),k3_xboole_0('#skF_10','#skF_12')) = k2_zfmisc_1('#skF_9','#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_42973,c_29547])).

tff(c_43004,plain,(
    k2_zfmisc_1('#skF_9',k3_xboole_0('#skF_10','#skF_12')) = k2_zfmisc_1('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42532,c_42988])).

tff(c_30157,plain,(
    ! [C_944,A_945,B_946] :
      ( r1_tarski(k2_zfmisc_1(C_944,A_945),k2_zfmisc_1(C_944,B_946))
      | ~ r1_tarski(A_945,B_946) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_30168,plain,(
    ! [C_944,A_945,B_946] :
      ( k4_xboole_0(k2_zfmisc_1(C_944,A_945),k2_zfmisc_1(C_944,B_946)) = k1_xboole_0
      | ~ r1_tarski(A_945,B_946) ) ),
    inference(resolution,[status(thm)],[c_30157,c_28])).

tff(c_53301,plain,(
    ! [C_1659,A_1660,B_1661] :
      ( k4_xboole_0(k2_zfmisc_1(C_1659,A_1660),k2_zfmisc_1(C_1659,B_1661)) = '#skF_9'
      | ~ r1_tarski(A_1660,B_1661) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42376,c_30168])).

tff(c_53570,plain,(
    ! [B_1662] :
      ( k4_xboole_0(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1('#skF_9',B_1662)) = '#skF_9'
      | ~ r1_tarski(k3_xboole_0('#skF_10','#skF_12'),B_1662) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43004,c_53301])).

tff(c_53753,plain,(
    ! [B_1662] :
      ( k2_zfmisc_1('#skF_9','#skF_10') = '#skF_9'
      | ~ r1_tarski(k3_xboole_0('#skF_10','#skF_12'),B_1662)
      | k3_xboole_0(k2_zfmisc_1('#skF_9','#skF_10'),k2_zfmisc_1('#skF_9',B_1662)) != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47933,c_53570])).

tff(c_53830,plain,(
    ! [B_1662] :
      ( k2_zfmisc_1('#skF_9','#skF_10') = '#skF_9'
      | ~ r1_tarski(k3_xboole_0('#skF_10','#skF_12'),B_1662)
      | k2_zfmisc_1('#skF_9',k3_xboole_0('#skF_10',B_1662)) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29548,c_76,c_53753])).

tff(c_54110,plain,(
    ! [B_1671] :
      ( ~ r1_tarski(k3_xboole_0('#skF_10','#skF_12'),B_1671)
      | k2_zfmisc_1('#skF_9',k3_xboole_0('#skF_10',B_1671)) != '#skF_9' ) ),
    inference(negUnitSimplification,[status(thm)],[c_42403,c_53830])).

tff(c_54144,plain,(
    k2_zfmisc_1('#skF_9',k3_xboole_0('#skF_10',k3_xboole_0('#skF_10','#skF_12'))) != '#skF_9' ),
    inference(resolution,[status(thm)],[c_24,c_54110])).

tff(c_65964,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65920,c_54144])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:42:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.81/7.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.81/7.21  
% 14.81/7.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.81/7.21  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_2 > #skF_7 > #skF_9 > #skF_3 > #skF_12
% 14.81/7.21  
% 14.81/7.21  %Foreground sorts:
% 14.81/7.21  
% 14.81/7.21  
% 14.81/7.21  %Background operators:
% 14.81/7.21  
% 14.81/7.21  
% 14.81/7.21  %Foreground operators:
% 14.81/7.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 14.81/7.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.81/7.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.81/7.21  tff('#skF_11', type, '#skF_11': $i).
% 14.81/7.21  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 14.81/7.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.81/7.21  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 14.81/7.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.81/7.21  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 14.81/7.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.81/7.21  tff('#skF_10', type, '#skF_10': $i).
% 14.81/7.21  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 14.81/7.21  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 14.81/7.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 14.81/7.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 14.81/7.21  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 14.81/7.21  tff('#skF_9', type, '#skF_9': $i).
% 14.81/7.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.81/7.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.81/7.21  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 14.81/7.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.81/7.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.81/7.21  tff('#skF_12', type, '#skF_12': $i).
% 14.81/7.21  
% 15.02/7.24  tff(f_45, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 15.02/7.24  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.02/7.24  tff(f_105, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 15.02/7.24  tff(f_63, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 15.02/7.24  tff(f_51, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 15.02/7.24  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 15.02/7.24  tff(f_96, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 15.02/7.24  tff(f_65, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 15.02/7.24  tff(f_94, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 15.02/7.24  tff(f_88, axiom, (![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 15.02/7.24  tff(f_61, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 15.02/7.24  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 15.02/7.24  tff(f_77, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 15.02/7.24  tff(f_57, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 15.02/7.24  tff(c_29487, plain, (![A_894, B_895]: (r1_tarski(A_894, B_895) | k4_xboole_0(A_894, B_895)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.02/7.24  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.02/7.24  tff(c_124, plain, (![A_72, B_73]: (r1_tarski(A_72, B_73) | k4_xboole_0(A_72, B_73)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.02/7.24  tff(c_78, plain, (~r1_tarski('#skF_10', '#skF_12') | ~r1_tarski('#skF_9', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_105])).
% 15.02/7.24  tff(c_101, plain, (~r1_tarski('#skF_9', '#skF_11')), inference(splitLeft, [status(thm)], [c_78])).
% 15.02/7.24  tff(c_132, plain, (k4_xboole_0('#skF_9', '#skF_11')!=k1_xboole_0), inference(resolution, [status(thm)], [c_124, c_101])).
% 15.02/7.24  tff(c_102, plain, (![A_69, B_70]: (k4_xboole_0(A_69, B_70)=k1_xboole_0 | ~r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.02/7.24  tff(c_106, plain, (![B_8]: (k4_xboole_0(B_8, B_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_102])).
% 15.02/7.24  tff(c_40, plain, (![A_19]: (k4_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_63])).
% 15.02/7.24  tff(c_26, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | k4_xboole_0(A_9, B_10)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.02/7.24  tff(c_297, plain, (![A_98, B_99, C_100]: (r1_tarski(A_98, B_99) | ~r1_tarski(A_98, k4_xboole_0(B_99, C_100)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 15.02/7.24  tff(c_551, plain, (![A_113, B_114]: (r1_tarski(A_113, B_114) | ~r1_tarski(A_113, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_106, c_297])).
% 15.02/7.24  tff(c_563, plain, (![A_9, B_114]: (r1_tarski(A_9, B_114) | k4_xboole_0(A_9, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_551])).
% 15.02/7.24  tff(c_579, plain, (![A_115, B_116]: (r1_tarski(A_115, B_116) | k1_xboole_0!=A_115)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_563])).
% 15.02/7.24  tff(c_34, plain, (![A_14, B_15]: (k3_xboole_0(A_14, B_15)=A_14 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 15.02/7.24  tff(c_614, plain, (![A_115, B_116]: (k3_xboole_0(A_115, B_116)=A_115 | k1_xboole_0!=A_115)), inference(resolution, [status(thm)], [c_579, c_34])).
% 15.02/7.24  tff(c_3715, plain, (![A_236, C_237, B_238, D_239]: (k3_xboole_0(k2_zfmisc_1(A_236, C_237), k2_zfmisc_1(B_238, D_239))=k2_zfmisc_1(k3_xboole_0(A_236, B_238), k3_xboole_0(C_237, D_239)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 15.02/7.24  tff(c_82, plain, (r1_tarski(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_11', '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 15.02/7.24  tff(c_163, plain, (![A_77, B_78]: (k3_xboole_0(A_77, B_78)=A_77 | ~r1_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_55])).
% 15.02/7.24  tff(c_173, plain, (k3_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_11', '#skF_12'))=k2_zfmisc_1('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_82, c_163])).
% 15.02/7.24  tff(c_3766, plain, (k2_zfmisc_1(k3_xboole_0('#skF_9', '#skF_11'), k3_xboole_0('#skF_10', '#skF_12'))=k2_zfmisc_1('#skF_9', '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_3715, c_173])).
% 15.02/7.24  tff(c_4166, plain, (k2_zfmisc_1(k3_xboole_0('#skF_9', '#skF_11'), '#skF_10')=k2_zfmisc_1('#skF_9', '#skF_10') | k1_xboole_0!='#skF_10'), inference(superposition, [status(thm), theory('equality')], [c_614, c_3766])).
% 15.02/7.24  tff(c_4765, plain, (k1_xboole_0!='#skF_10'), inference(splitLeft, [status(thm)], [c_4166])).
% 15.02/7.24  tff(c_42, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_65])).
% 15.02/7.24  tff(c_321, plain, (![B_102, C_103]: (r1_tarski(k4_xboole_0(B_102, C_103), B_102))), inference(resolution, [status(thm)], [c_24, c_297])).
% 15.02/7.24  tff(c_484, plain, (![A_107, B_108]: (r1_tarski(k3_xboole_0(A_107, B_108), A_107))), inference(superposition, [status(thm), theory('equality')], [c_42, c_321])).
% 15.02/7.24  tff(c_28, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=k1_xboole_0 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.02/7.24  tff(c_520, plain, (![A_107, B_108]: (k4_xboole_0(k3_xboole_0(A_107, B_108), A_107)=k1_xboole_0)), inference(resolution, [status(thm)], [c_484, c_28])).
% 15.02/7.24  tff(c_618, plain, (k1_xboole_0!='#skF_9'), inference(resolution, [status(thm)], [c_579, c_101])).
% 15.02/7.24  tff(c_345, plain, (![A_20, B_21]: (r1_tarski(k3_xboole_0(A_20, B_21), A_20))), inference(superposition, [status(thm), theory('equality')], [c_42, c_321])).
% 15.02/7.24  tff(c_74, plain, (![A_59, C_61, B_60]: (r1_tarski(k2_zfmisc_1(A_59, C_61), k2_zfmisc_1(B_60, C_61)) | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_94])).
% 15.02/7.24  tff(c_6232, plain, (![B_304]: (r1_tarski(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1(B_304, k3_xboole_0('#skF_10', '#skF_12'))) | ~r1_tarski(k3_xboole_0('#skF_9', '#skF_11'), B_304))), inference(superposition, [status(thm), theory('equality')], [c_3766, c_74])).
% 15.02/7.24  tff(c_68, plain, (![A_56, B_57, C_58]: (~r1_tarski(k2_zfmisc_1(A_56, B_57), k2_zfmisc_1(A_56, C_58)) | r1_tarski(B_57, C_58) | k1_xboole_0=A_56)), inference(cnfTransformation, [status(thm)], [f_88])).
% 15.02/7.24  tff(c_6241, plain, (r1_tarski('#skF_10', k3_xboole_0('#skF_10', '#skF_12')) | k1_xboole_0='#skF_9' | ~r1_tarski(k3_xboole_0('#skF_9', '#skF_11'), '#skF_9')), inference(resolution, [status(thm)], [c_6232, c_68])).
% 15.02/7.24  tff(c_6269, plain, (r1_tarski('#skF_10', k3_xboole_0('#skF_10', '#skF_12')) | k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_345, c_6241])).
% 15.02/7.24  tff(c_6270, plain, (r1_tarski('#skF_10', k3_xboole_0('#skF_10', '#skF_12'))), inference(negUnitSimplification, [status(thm)], [c_618, c_6269])).
% 15.02/7.24  tff(c_525, plain, (![B_109, A_110]: (B_109=A_110 | ~r1_tarski(B_109, A_110) | ~r1_tarski(A_110, B_109))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.02/7.24  tff(c_542, plain, (![B_10, A_9]: (B_10=A_9 | ~r1_tarski(B_10, A_9) | k4_xboole_0(A_9, B_10)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_525])).
% 15.02/7.24  tff(c_6283, plain, (k3_xboole_0('#skF_10', '#skF_12')='#skF_10' | k4_xboole_0(k3_xboole_0('#skF_10', '#skF_12'), '#skF_10')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6270, c_542])).
% 15.02/7.24  tff(c_6311, plain, (k3_xboole_0('#skF_10', '#skF_12')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_520, c_6283])).
% 15.02/7.24  tff(c_72, plain, (![C_61, A_59, B_60]: (r1_tarski(k2_zfmisc_1(C_61, A_59), k2_zfmisc_1(C_61, B_60)) | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_94])).
% 15.02/7.24  tff(c_4144, plain, (![B_60]: (r1_tarski(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1(k3_xboole_0('#skF_9', '#skF_11'), B_60)) | ~r1_tarski(k3_xboole_0('#skF_10', '#skF_12'), B_60))), inference(superposition, [status(thm), theory('equality')], [c_3766, c_72])).
% 15.02/7.24  tff(c_7118, plain, (![B_326]: (r1_tarski(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1(k3_xboole_0('#skF_9', '#skF_11'), B_326)) | ~r1_tarski('#skF_10', B_326))), inference(demodulation, [status(thm), theory('equality')], [c_6311, c_4144])).
% 15.02/7.24  tff(c_70, plain, (![B_57, A_56, C_58]: (~r1_tarski(k2_zfmisc_1(B_57, A_56), k2_zfmisc_1(C_58, A_56)) | r1_tarski(B_57, C_58) | k1_xboole_0=A_56)), inference(cnfTransformation, [status(thm)], [f_88])).
% 15.02/7.24  tff(c_7133, plain, (r1_tarski('#skF_9', k3_xboole_0('#skF_9', '#skF_11')) | k1_xboole_0='#skF_10' | ~r1_tarski('#skF_10', '#skF_10')), inference(resolution, [status(thm)], [c_7118, c_70])).
% 15.02/7.24  tff(c_7164, plain, (r1_tarski('#skF_9', k3_xboole_0('#skF_9', '#skF_11')) | k1_xboole_0='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_7133])).
% 15.02/7.24  tff(c_7165, plain, (r1_tarski('#skF_9', k3_xboole_0('#skF_9', '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_4765, c_7164])).
% 15.02/7.24  tff(c_319, plain, (![B_99, C_100]: (r1_tarski(k4_xboole_0(B_99, C_100), B_99))), inference(resolution, [status(thm)], [c_24, c_297])).
% 15.02/7.24  tff(c_5709, plain, (![B_288, C_289]: (k4_xboole_0(B_288, C_289)=B_288 | ~r1_tarski(B_288, k4_xboole_0(B_288, C_289)))), inference(resolution, [status(thm)], [c_319, c_525])).
% 15.02/7.24  tff(c_5766, plain, (![A_20, B_21]: (k4_xboole_0(A_20, k4_xboole_0(A_20, B_21))=A_20 | ~r1_tarski(A_20, k3_xboole_0(A_20, B_21)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_5709])).
% 15.02/7.24  tff(c_5796, plain, (![A_20, B_21]: (k3_xboole_0(A_20, B_21)=A_20 | ~r1_tarski(A_20, k3_xboole_0(A_20, B_21)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_5766])).
% 15.02/7.24  tff(c_7210, plain, (k3_xboole_0('#skF_9', '#skF_11')='#skF_9'), inference(resolution, [status(thm)], [c_7165, c_5796])).
% 15.02/7.24  tff(c_195, plain, (![A_80, B_81]: (k4_xboole_0(A_80, k4_xboole_0(A_80, B_81))=k3_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_65])).
% 15.02/7.24  tff(c_10465, plain, (![A_449, B_450]: (k4_xboole_0(A_449, k3_xboole_0(A_449, B_450))=k3_xboole_0(A_449, k4_xboole_0(A_449, B_450)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_195])).
% 15.02/7.24  tff(c_10738, plain, (k3_xboole_0('#skF_9', k4_xboole_0('#skF_9', '#skF_11'))=k4_xboole_0('#skF_9', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_7210, c_10465])).
% 15.02/7.24  tff(c_10842, plain, (k3_xboole_0('#skF_9', k4_xboole_0('#skF_9', '#skF_11'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_106, c_10738])).
% 15.02/7.24  tff(c_5260, plain, (![B_281, A_282]: (B_281=A_282 | ~r1_tarski(B_281, A_282) | k4_xboole_0(A_282, B_281)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_525])).
% 15.02/7.24  tff(c_5293, plain, (![B_99, C_100]: (k4_xboole_0(B_99, C_100)=B_99 | k4_xboole_0(B_99, k4_xboole_0(B_99, C_100))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_319, c_5260])).
% 15.02/7.24  tff(c_5321, plain, (![B_283, C_284]: (k4_xboole_0(B_283, C_284)=B_283 | k3_xboole_0(B_283, C_284)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_5293])).
% 15.02/7.24  tff(c_38, plain, (![A_17, B_18]: (k1_xboole_0=A_17 | ~r1_tarski(A_17, k4_xboole_0(B_18, A_17)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 15.02/7.24  tff(c_6980, plain, (![C_321, B_322]: (k1_xboole_0=C_321 | ~r1_tarski(C_321, B_322) | k3_xboole_0(B_322, C_321)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5321, c_38])).
% 15.02/7.24  tff(c_14670, plain, (![B_494, C_495]: (k4_xboole_0(B_494, C_495)=k1_xboole_0 | k3_xboole_0(B_494, k4_xboole_0(B_494, C_495))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_319, c_6980])).
% 15.02/7.24  tff(c_14688, plain, (k4_xboole_0('#skF_9', '#skF_11')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_10842, c_14670])).
% 15.02/7.24  tff(c_14781, plain, $false, inference(negUnitSimplification, [status(thm)], [c_132, c_14688])).
% 15.02/7.24  tff(c_14783, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_4166])).
% 15.02/7.24  tff(c_14834, plain, (![B_8]: (k4_xboole_0(B_8, B_8)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_14783, c_106])).
% 15.02/7.24  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.02/7.24  tff(c_15666, plain, (![A_533, B_534, C_535]: (~r2_hidden('#skF_1'(A_533, B_534, C_535), B_534) | r2_hidden('#skF_2'(A_533, B_534, C_535), C_535) | k4_xboole_0(A_533, B_534)=C_535)), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.02/7.24  tff(c_15669, plain, (![A_1, C_3]: (r2_hidden('#skF_2'(A_1, A_1, C_3), C_3) | k4_xboole_0(A_1, A_1)=C_3)), inference(resolution, [status(thm)], [c_18, c_15666])).
% 15.02/7.24  tff(c_15674, plain, (![A_1, C_3]: (r2_hidden('#skF_2'(A_1, A_1, C_3), C_3) | C_3='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_14834, c_15669])).
% 15.02/7.24  tff(c_4172, plain, (![A_246, B_247, D_248]: (r2_hidden('#skF_8'(A_246, B_247, k2_zfmisc_1(A_246, B_247), D_248), B_247) | ~r2_hidden(D_248, k2_zfmisc_1(A_246, B_247)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 15.02/7.24  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.02/7.24  tff(c_4204, plain, (![A_246, A_1, B_2, D_248]: (r2_hidden('#skF_8'(A_246, k4_xboole_0(A_1, B_2), k2_zfmisc_1(A_246, k4_xboole_0(A_1, B_2)), D_248), A_1) | ~r2_hidden(D_248, k2_zfmisc_1(A_246, k4_xboole_0(A_1, B_2))))), inference(resolution, [status(thm)], [c_4172, c_6])).
% 15.02/7.24  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.02/7.24  tff(c_29149, plain, (![A_885, A_886, B_887, D_888]: (~r2_hidden('#skF_8'(A_885, k4_xboole_0(A_886, B_887), k2_zfmisc_1(A_885, k4_xboole_0(A_886, B_887)), D_888), B_887) | ~r2_hidden(D_888, k2_zfmisc_1(A_885, k4_xboole_0(A_886, B_887))))), inference(resolution, [status(thm)], [c_4172, c_4])).
% 15.02/7.24  tff(c_29153, plain, (![D_248, A_246, A_1]: (~r2_hidden(D_248, k2_zfmisc_1(A_246, k4_xboole_0(A_1, A_1))))), inference(resolution, [status(thm)], [c_4204, c_29149])).
% 15.02/7.24  tff(c_29328, plain, (![D_889, A_890]: (~r2_hidden(D_889, k2_zfmisc_1(A_890, '#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_14834, c_29153])).
% 15.02/7.24  tff(c_29412, plain, (![A_890]: (k2_zfmisc_1(A_890, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_15674, c_29328])).
% 15.02/7.24  tff(c_80, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_105])).
% 15.02/7.24  tff(c_14837, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_14783, c_80])).
% 15.02/7.24  tff(c_136, plain, (k4_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_11', '#skF_12'))=k1_xboole_0), inference(resolution, [status(thm)], [c_82, c_28])).
% 15.02/7.24  tff(c_14828, plain, (k4_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_11', '#skF_12'))='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_14783, c_136])).
% 15.02/7.24  tff(c_20394, plain, (![B_685, C_686]: (k4_xboole_0(B_685, C_686)=B_685 | ~r1_tarski(B_685, k4_xboole_0(B_685, C_686)))), inference(resolution, [status(thm)], [c_319, c_525])).
% 15.02/7.24  tff(c_20455, plain, (k4_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_11', '#skF_12'))=k2_zfmisc_1('#skF_9', '#skF_10') | ~r1_tarski(k2_zfmisc_1('#skF_9', '#skF_10'), '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_14828, c_20394])).
% 15.02/7.24  tff(c_20483, plain, (k2_zfmisc_1('#skF_9', '#skF_10')='#skF_10' | ~r1_tarski(k2_zfmisc_1('#skF_9', '#skF_10'), '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_14828, c_20455])).
% 15.02/7.24  tff(c_20484, plain, (~r1_tarski(k2_zfmisc_1('#skF_9', '#skF_10'), '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_14837, c_20483])).
% 15.02/7.24  tff(c_29437, plain, (~r1_tarski('#skF_10', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_29412, c_20484])).
% 15.02/7.24  tff(c_29450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_29437])).
% 15.02/7.24  tff(c_29451, plain, (~r1_tarski('#skF_10', '#skF_12')), inference(splitRight, [status(thm)], [c_78])).
% 15.02/7.24  tff(c_29495, plain, (k4_xboole_0('#skF_10', '#skF_12')!=k1_xboole_0), inference(resolution, [status(thm)], [c_29487, c_29451])).
% 15.02/7.24  tff(c_29622, plain, (![A_907, B_908, C_909]: (r1_tarski(A_907, B_908) | ~r1_tarski(A_907, k4_xboole_0(B_908, C_909)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 15.02/7.24  tff(c_29647, plain, (![B_908, C_909]: (r1_tarski(k4_xboole_0(B_908, C_909), B_908))), inference(resolution, [status(thm)], [c_24, c_29622])).
% 15.02/7.24  tff(c_29648, plain, (![B_910, C_911]: (r1_tarski(k4_xboole_0(B_910, C_911), B_910))), inference(resolution, [status(thm)], [c_24, c_29622])).
% 15.02/7.24  tff(c_29665, plain, (![A_20, B_21]: (r1_tarski(k3_xboole_0(A_20, B_21), A_20))), inference(superposition, [status(thm), theory('equality')], [c_42, c_29648])).
% 15.02/7.24  tff(c_29453, plain, (![A_891, B_892]: (k4_xboole_0(A_891, B_892)=k1_xboole_0 | ~r1_tarski(A_891, B_892))), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.02/7.24  tff(c_29465, plain, (![B_8]: (k4_xboole_0(B_8, B_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_29453])).
% 15.02/7.24  tff(c_30001, plain, (![A_928, B_929]: (r1_tarski(A_928, B_929) | ~r1_tarski(A_928, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_29465, c_29622])).
% 15.02/7.24  tff(c_30013, plain, (![A_9, B_929]: (r1_tarski(A_9, B_929) | k4_xboole_0(A_9, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_30001])).
% 15.02/7.24  tff(c_30024, plain, (![A_9, B_929]: (r1_tarski(A_9, B_929) | k1_xboole_0!=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_30013])).
% 15.02/7.24  tff(c_29452, plain, (r1_tarski('#skF_9', '#skF_11')), inference(splitRight, [status(thm)], [c_78])).
% 15.02/7.24  tff(c_29463, plain, (k4_xboole_0('#skF_9', '#skF_11')=k1_xboole_0), inference(resolution, [status(thm)], [c_29452, c_29453])).
% 15.02/7.24  tff(c_29866, plain, (![A_921]: (r1_tarski(A_921, '#skF_9') | ~r1_tarski(A_921, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_29463, c_29622])).
% 15.02/7.24  tff(c_29882, plain, (![A_9]: (r1_tarski(A_9, '#skF_9') | k4_xboole_0(A_9, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_29866])).
% 15.02/7.24  tff(c_29898, plain, (![A_922]: (r1_tarski(A_922, '#skF_9') | k1_xboole_0!=A_922)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_29882])).
% 15.02/7.24  tff(c_20, plain, (![B_8, A_7]: (B_8=A_7 | ~r1_tarski(B_8, A_7) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.02/7.24  tff(c_30942, plain, (![A_982]: (A_982='#skF_9' | ~r1_tarski('#skF_9', A_982) | k1_xboole_0!=A_982)), inference(resolution, [status(thm)], [c_29898, c_20])).
% 15.02/7.24  tff(c_30958, plain, (![B_929]: (B_929='#skF_9' | k1_xboole_0!=B_929 | k1_xboole_0!='#skF_9')), inference(resolution, [status(thm)], [c_30024, c_30942])).
% 15.02/7.24  tff(c_30963, plain, (k1_xboole_0!='#skF_9'), inference(splitLeft, [status(thm)], [c_30958])).
% 15.02/7.24  tff(c_29532, plain, (![A_899, B_900]: (k3_xboole_0(A_899, B_900)=A_899 | ~r1_tarski(A_899, B_900))), inference(cnfTransformation, [status(thm)], [f_55])).
% 15.02/7.24  tff(c_29546, plain, (k3_xboole_0('#skF_9', '#skF_11')='#skF_9'), inference(resolution, [status(thm)], [c_29452, c_29532])).
% 15.02/7.24  tff(c_32768, plain, (![A_1045, C_1046, B_1047, D_1048]: (k3_xboole_0(k2_zfmisc_1(A_1045, C_1046), k2_zfmisc_1(B_1047, D_1048))=k2_zfmisc_1(k3_xboole_0(A_1045, B_1047), k3_xboole_0(C_1046, D_1048)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 15.02/7.24  tff(c_29547, plain, (k3_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_11', '#skF_12'))=k2_zfmisc_1('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_82, c_29532])).
% 15.02/7.24  tff(c_32816, plain, (k2_zfmisc_1(k3_xboole_0('#skF_9', '#skF_11'), k3_xboole_0('#skF_10', '#skF_12'))=k2_zfmisc_1('#skF_9', '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_32768, c_29547])).
% 15.02/7.24  tff(c_32839, plain, (k2_zfmisc_1('#skF_9', k3_xboole_0('#skF_10', '#skF_12'))=k2_zfmisc_1('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_29546, c_32816])).
% 15.02/7.24  tff(c_34695, plain, (![B_1105]: (r1_tarski(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1(B_1105, k3_xboole_0('#skF_10', '#skF_12'))) | ~r1_tarski('#skF_9', B_1105))), inference(superposition, [status(thm), theory('equality')], [c_32839, c_74])).
% 15.02/7.24  tff(c_34707, plain, (r1_tarski('#skF_10', k3_xboole_0('#skF_10', '#skF_12')) | k1_xboole_0='#skF_9' | ~r1_tarski('#skF_9', '#skF_9')), inference(resolution, [status(thm)], [c_34695, c_68])).
% 15.02/7.24  tff(c_34732, plain, (r1_tarski('#skF_10', k3_xboole_0('#skF_10', '#skF_12')) | k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_34707])).
% 15.02/7.24  tff(c_34733, plain, (r1_tarski('#skF_10', k3_xboole_0('#skF_10', '#skF_12'))), inference(negUnitSimplification, [status(thm)], [c_30963, c_34732])).
% 15.02/7.24  tff(c_34752, plain, (k3_xboole_0('#skF_10', '#skF_12')='#skF_10' | ~r1_tarski(k3_xboole_0('#skF_10', '#skF_12'), '#skF_10')), inference(resolution, [status(thm)], [c_34733, c_20])).
% 15.02/7.24  tff(c_34774, plain, (k3_xboole_0('#skF_10', '#skF_12')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_29665, c_34752])).
% 15.02/7.24  tff(c_29572, plain, (![A_902, B_903]: (k4_xboole_0(A_902, k4_xboole_0(A_902, B_903))=k3_xboole_0(A_902, B_903))), inference(cnfTransformation, [status(thm)], [f_65])).
% 15.02/7.24  tff(c_42239, plain, (![A_1311, B_1312]: (k4_xboole_0(A_1311, B_1312)=k1_xboole_0 | ~r1_tarski(k4_xboole_0(A_1311, B_1312), k3_xboole_0(A_1311, B_1312)))), inference(superposition, [status(thm), theory('equality')], [c_29572, c_38])).
% 15.02/7.24  tff(c_42264, plain, (k4_xboole_0('#skF_10', '#skF_12')=k1_xboole_0 | ~r1_tarski(k4_xboole_0('#skF_10', '#skF_12'), '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_34774, c_42239])).
% 15.02/7.24  tff(c_42372, plain, (k4_xboole_0('#skF_10', '#skF_12')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_29647, c_42264])).
% 15.02/7.24  tff(c_42374, plain, $false, inference(negUnitSimplification, [status(thm)], [c_29495, c_42372])).
% 15.02/7.24  tff(c_42376, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_30958])).
% 15.02/7.24  tff(c_42399, plain, (![B_8]: (k4_xboole_0(B_8, B_8)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_42376, c_29465])).
% 15.02/7.24  tff(c_45424, plain, (![A_1432, B_1433, C_1434]: (~r2_hidden('#skF_1'(A_1432, B_1433, C_1434), B_1433) | r2_hidden('#skF_2'(A_1432, B_1433, C_1434), C_1434) | k4_xboole_0(A_1432, B_1433)=C_1434)), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.02/7.24  tff(c_45427, plain, (![A_1, C_3]: (r2_hidden('#skF_2'(A_1, A_1, C_3), C_3) | k4_xboole_0(A_1, A_1)=C_3)), inference(resolution, [status(thm)], [c_18, c_45424])).
% 15.02/7.24  tff(c_45435, plain, (![A_1, C_3]: (r2_hidden('#skF_2'(A_1, A_1, C_3), C_3) | C_3='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_42399, c_45427])).
% 15.02/7.24  tff(c_43394, plain, (![A_1356, B_1357, D_1358]: (r2_hidden('#skF_7'(A_1356, B_1357, k2_zfmisc_1(A_1356, B_1357), D_1358), A_1356) | ~r2_hidden(D_1358, k2_zfmisc_1(A_1356, B_1357)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 15.02/7.24  tff(c_43411, plain, (![A_1, B_2, B_1357, D_1358]: (r2_hidden('#skF_7'(k4_xboole_0(A_1, B_2), B_1357, k2_zfmisc_1(k4_xboole_0(A_1, B_2), B_1357), D_1358), A_1) | ~r2_hidden(D_1358, k2_zfmisc_1(k4_xboole_0(A_1, B_2), B_1357)))), inference(resolution, [status(thm)], [c_43394, c_6])).
% 15.02/7.24  tff(c_65549, plain, (![A_1797, B_1798, B_1799, D_1800]: (~r2_hidden('#skF_7'(k4_xboole_0(A_1797, B_1798), B_1799, k2_zfmisc_1(k4_xboole_0(A_1797, B_1798), B_1799), D_1800), B_1798) | ~r2_hidden(D_1800, k2_zfmisc_1(k4_xboole_0(A_1797, B_1798), B_1799)))), inference(resolution, [status(thm)], [c_43394, c_4])).
% 15.02/7.24  tff(c_65571, plain, (![D_1358, A_1, B_1357]: (~r2_hidden(D_1358, k2_zfmisc_1(k4_xboole_0(A_1, A_1), B_1357)))), inference(resolution, [status(thm)], [c_43411, c_65549])).
% 15.02/7.24  tff(c_65834, plain, (![D_1801, B_1802]: (~r2_hidden(D_1801, k2_zfmisc_1('#skF_9', B_1802)))), inference(demodulation, [status(thm), theory('equality')], [c_42399, c_65571])).
% 15.02/7.24  tff(c_65920, plain, (![B_1802]: (k2_zfmisc_1('#skF_9', B_1802)='#skF_9')), inference(resolution, [status(thm)], [c_45435, c_65834])).
% 15.02/7.24  tff(c_42403, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_42376, c_80])).
% 15.02/7.24  tff(c_29548, plain, (![B_8]: (k3_xboole_0(B_8, B_8)=B_8)), inference(resolution, [status(thm)], [c_24, c_29532])).
% 15.02/7.24  tff(c_76, plain, (![A_62, C_64, B_63, D_65]: (k3_xboole_0(k2_zfmisc_1(A_62, C_64), k2_zfmisc_1(B_63, D_65))=k2_zfmisc_1(k3_xboole_0(A_62, B_63), k3_xboole_0(C_64, D_65)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 15.02/7.24  tff(c_29834, plain, (![B_917, A_918]: (B_917=A_918 | ~r1_tarski(B_917, A_918) | ~r1_tarski(A_918, B_917))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.02/7.24  tff(c_29852, plain, (![B_10, A_9]: (B_10=A_9 | ~r1_tarski(B_10, A_9) | k4_xboole_0(A_9, B_10)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_29834])).
% 15.02/7.24  tff(c_47874, plain, (![B_1521, A_1522]: (B_1521=A_1522 | ~r1_tarski(B_1521, A_1522) | k4_xboole_0(A_1522, B_1521)!='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_42376, c_29852])).
% 15.02/7.24  tff(c_47913, plain, (![B_908, C_909]: (k4_xboole_0(B_908, C_909)=B_908 | k4_xboole_0(B_908, k4_xboole_0(B_908, C_909))!='#skF_9')), inference(resolution, [status(thm)], [c_29647, c_47874])).
% 15.02/7.24  tff(c_47933, plain, (![B_908, C_909]: (k4_xboole_0(B_908, C_909)=B_908 | k3_xboole_0(B_908, C_909)!='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_47913])).
% 15.02/7.24  tff(c_36, plain, (![A_16]: (k3_xboole_0(A_16, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 15.02/7.24  tff(c_42480, plain, (![A_1315]: (k3_xboole_0(A_1315, '#skF_9')='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_42376, c_42376, c_36])).
% 15.02/7.24  tff(c_32, plain, (![A_11, B_12, C_13]: (r1_tarski(A_11, B_12) | ~r1_tarski(A_11, k4_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 15.02/7.24  tff(c_30640, plain, (![B_970, C_971, C_972]: (r1_tarski(k4_xboole_0(k4_xboole_0(B_970, C_971), C_972), B_970))), inference(resolution, [status(thm)], [c_29648, c_32])).
% 15.02/7.24  tff(c_30686, plain, (![B_970, C_971, B_21]: (r1_tarski(k3_xboole_0(k4_xboole_0(B_970, C_971), B_21), B_970))), inference(superposition, [status(thm), theory('equality')], [c_42, c_30640])).
% 15.02/7.24  tff(c_42514, plain, (![B_1316]: (r1_tarski('#skF_9', B_1316))), inference(superposition, [status(thm), theory('equality')], [c_42480, c_30686])).
% 15.02/7.24  tff(c_42532, plain, (![B_1316]: (k3_xboole_0('#skF_9', B_1316)='#skF_9')), inference(resolution, [status(thm)], [c_42514, c_34])).
% 15.02/7.24  tff(c_42973, plain, (![A_1338, C_1339, B_1340, D_1341]: (k3_xboole_0(k2_zfmisc_1(A_1338, C_1339), k2_zfmisc_1(B_1340, D_1341))=k2_zfmisc_1(k3_xboole_0(A_1338, B_1340), k3_xboole_0(C_1339, D_1341)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 15.02/7.24  tff(c_42988, plain, (k2_zfmisc_1(k3_xboole_0('#skF_9', '#skF_11'), k3_xboole_0('#skF_10', '#skF_12'))=k2_zfmisc_1('#skF_9', '#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_42973, c_29547])).
% 15.02/7.24  tff(c_43004, plain, (k2_zfmisc_1('#skF_9', k3_xboole_0('#skF_10', '#skF_12'))=k2_zfmisc_1('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_42532, c_42988])).
% 15.02/7.24  tff(c_30157, plain, (![C_944, A_945, B_946]: (r1_tarski(k2_zfmisc_1(C_944, A_945), k2_zfmisc_1(C_944, B_946)) | ~r1_tarski(A_945, B_946))), inference(cnfTransformation, [status(thm)], [f_94])).
% 15.02/7.24  tff(c_30168, plain, (![C_944, A_945, B_946]: (k4_xboole_0(k2_zfmisc_1(C_944, A_945), k2_zfmisc_1(C_944, B_946))=k1_xboole_0 | ~r1_tarski(A_945, B_946))), inference(resolution, [status(thm)], [c_30157, c_28])).
% 15.02/7.24  tff(c_53301, plain, (![C_1659, A_1660, B_1661]: (k4_xboole_0(k2_zfmisc_1(C_1659, A_1660), k2_zfmisc_1(C_1659, B_1661))='#skF_9' | ~r1_tarski(A_1660, B_1661))), inference(demodulation, [status(thm), theory('equality')], [c_42376, c_30168])).
% 15.02/7.24  tff(c_53570, plain, (![B_1662]: (k4_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_9', B_1662))='#skF_9' | ~r1_tarski(k3_xboole_0('#skF_10', '#skF_12'), B_1662))), inference(superposition, [status(thm), theory('equality')], [c_43004, c_53301])).
% 15.02/7.24  tff(c_53753, plain, (![B_1662]: (k2_zfmisc_1('#skF_9', '#skF_10')='#skF_9' | ~r1_tarski(k3_xboole_0('#skF_10', '#skF_12'), B_1662) | k3_xboole_0(k2_zfmisc_1('#skF_9', '#skF_10'), k2_zfmisc_1('#skF_9', B_1662))!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_47933, c_53570])).
% 15.02/7.24  tff(c_53830, plain, (![B_1662]: (k2_zfmisc_1('#skF_9', '#skF_10')='#skF_9' | ~r1_tarski(k3_xboole_0('#skF_10', '#skF_12'), B_1662) | k2_zfmisc_1('#skF_9', k3_xboole_0('#skF_10', B_1662))!='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_29548, c_76, c_53753])).
% 15.02/7.24  tff(c_54110, plain, (![B_1671]: (~r1_tarski(k3_xboole_0('#skF_10', '#skF_12'), B_1671) | k2_zfmisc_1('#skF_9', k3_xboole_0('#skF_10', B_1671))!='#skF_9')), inference(negUnitSimplification, [status(thm)], [c_42403, c_53830])).
% 15.02/7.24  tff(c_54144, plain, (k2_zfmisc_1('#skF_9', k3_xboole_0('#skF_10', k3_xboole_0('#skF_10', '#skF_12')))!='#skF_9'), inference(resolution, [status(thm)], [c_24, c_54110])).
% 15.02/7.24  tff(c_65964, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65920, c_54144])).
% 15.02/7.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.02/7.24  
% 15.02/7.24  Inference rules
% 15.02/7.24  ----------------------
% 15.02/7.24  #Ref     : 12
% 15.02/7.24  #Sup     : 16575
% 15.02/7.24  #Fact    : 2
% 15.02/7.24  #Define  : 0
% 15.02/7.24  #Split   : 20
% 15.02/7.24  #Chain   : 0
% 15.02/7.24  #Close   : 0
% 15.02/7.24  
% 15.02/7.24  Ordering : KBO
% 15.02/7.24  
% 15.02/7.24  Simplification rules
% 15.02/7.24  ----------------------
% 15.02/7.24  #Subsume      : 4632
% 15.02/7.24  #Demod        : 11464
% 15.02/7.24  #Tautology    : 7858
% 15.02/7.24  #SimpNegUnit  : 184
% 15.02/7.24  #BackRed      : 139
% 15.02/7.24  
% 15.02/7.24  #Partial instantiations: 0
% 15.02/7.24  #Strategies tried      : 1
% 15.02/7.24  
% 15.02/7.24  Timing (in seconds)
% 15.02/7.24  ----------------------
% 15.02/7.25  Preprocessing        : 0.34
% 15.02/7.25  Parsing              : 0.17
% 15.02/7.25  CNF conversion       : 0.03
% 15.02/7.25  Main loop            : 6.10
% 15.02/7.25  Inferencing          : 1.22
% 15.02/7.25  Reduction            : 2.87
% 15.02/7.25  Demodulation         : 2.34
% 15.02/7.25  BG Simplification    : 0.14
% 15.02/7.25  Subsumption          : 1.55
% 15.02/7.25  Abstraction          : 0.21
% 15.02/7.25  MUC search           : 0.00
% 15.02/7.25  Cooper               : 0.00
% 15.02/7.25  Total                : 6.50
% 15.02/7.25  Index Insertion      : 0.00
% 15.02/7.25  Index Deletion       : 0.00
% 15.02/7.25  Index Matching       : 0.00
% 15.02/7.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
