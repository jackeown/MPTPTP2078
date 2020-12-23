%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:54 EST 2020

% Result     : Theorem 11.10s
% Output     : CNFRefutation 11.19s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 205 expanded)
%              Number of leaves         :   31 (  82 expanded)
%              Depth                    :   17
%              Number of atoms          :  106 ( 287 expanded)
%              Number of equality atoms :   47 ( 139 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(c_56,plain,(
    k3_xboole_0('#skF_4','#skF_6') != k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_40,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k4_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_62,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_139,plain,(
    ! [A_43,B_44] :
      ( k3_xboole_0(A_43,B_44) = A_43
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_147,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_62,c_139])).

tff(c_1376,plain,(
    ! [A_106,B_107,C_108] : k4_xboole_0(k3_xboole_0(A_106,B_107),C_108) = k3_xboole_0(A_106,k4_xboole_0(B_107,C_108)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1451,plain,(
    ! [C_108] : k3_xboole_0('#skF_4',k4_xboole_0('#skF_5',C_108)) = k4_xboole_0('#skF_4',C_108) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_1376])).

tff(c_60,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_298,plain,(
    ! [A_58,B_59] : k4_xboole_0(A_58,k3_xboole_0(A_58,B_59)) = k4_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_343,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_7')) = k4_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_298])).

tff(c_2520,plain,(
    ! [C_138] : k3_xboole_0('#skF_4',k4_xboole_0('#skF_5',C_138)) = k4_xboole_0('#skF_4',C_138) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_1376])).

tff(c_2570,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_7')) = k3_xboole_0('#skF_4',k4_xboole_0('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_2520])).

tff(c_2593,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_7')) = k4_xboole_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1451,c_2570])).

tff(c_2837,plain,(
    k4_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_6')) = k3_xboole_0('#skF_4',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2593,c_40])).

tff(c_2843,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_7')) = k3_xboole_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2837])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_221,plain,(
    ! [A_54,B_55] :
      ( r2_hidden('#skF_1'(A_54,B_55),A_54)
      | r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [D_13,A_8,B_9] :
      ( r2_hidden(D_13,A_8)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_18616,plain,(
    ! [A_342,B_343,B_344] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_342,B_343),B_344),A_342)
      | r1_tarski(k4_xboole_0(A_342,B_343),B_344) ) ),
    inference(resolution,[status(thm)],[c_221,c_14])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_18867,plain,(
    ! [A_345,B_346] : r1_tarski(k4_xboole_0(A_345,B_346),A_345) ),
    inference(resolution,[status(thm)],[c_18616,c_6])).

tff(c_19034,plain,(
    ! [A_347,B_348] : r1_tarski(k3_xboole_0(A_347,B_348),A_347) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_18867])).

tff(c_19280,plain,(
    ! [A_349,B_350] : r1_tarski(k3_xboole_0(A_349,B_350),B_350) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_19034])).

tff(c_19400,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_6'),k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2843,c_19280])).

tff(c_28,plain,(
    ! [B_15,A_14] :
      ( B_15 = A_14
      | ~ r1_tarski(B_15,A_14)
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_19811,plain,
    ( k3_xboole_0('#skF_4','#skF_6') = k1_tarski('#skF_7')
    | ~ r1_tarski(k1_tarski('#skF_7'),k3_xboole_0('#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_19400,c_28])).

tff(c_19819,plain,(
    ~ r1_tarski(k1_tarski('#skF_7'),k3_xboole_0('#skF_4','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_19811])).

tff(c_685,plain,(
    ! [A_84,B_85] :
      ( k4_xboole_0(k1_tarski(A_84),B_85) = k1_tarski(A_84)
      | r2_hidden(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_718,plain,(
    ! [A_84,B_22] :
      ( k3_xboole_0(k1_tarski(A_84),B_22) = k1_tarski(A_84)
      | r2_hidden(A_84,k4_xboole_0(k1_tarski(A_84),B_22)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_685,c_40])).

tff(c_36,plain,(
    ! [A_18] : k4_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_337,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_298])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_364,plain,(
    ! [D_60,B_61,A_62] :
      ( ~ r2_hidden(D_60,B_61)
      | ~ r2_hidden(D_60,k4_xboole_0(A_62,B_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_391,plain,(
    ! [D_63,A_64] :
      ( ~ r2_hidden(D_63,k1_xboole_0)
      | ~ r2_hidden(D_63,A_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_364])).

tff(c_868,plain,(
    ! [B_90,A_91] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0,B_90),A_91)
      | r1_tarski(k1_xboole_0,B_90) ) ),
    inference(resolution,[status(thm)],[c_8,c_391])).

tff(c_880,plain,(
    ! [B_92] : r1_tarski(k1_xboole_0,B_92) ),
    inference(resolution,[status(thm)],[c_8,c_868])).

tff(c_34,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_935,plain,(
    ! [B_96] : k3_xboole_0(k1_xboole_0,B_96) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_880,c_34])).

tff(c_974,plain,(
    ! [B_96] : k3_xboole_0(B_96,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_935,c_2])).

tff(c_174,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k4_xboole_0(A_51,B_52)) = k3_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_192,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k3_xboole_0(A_18,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_174])).

tff(c_1107,plain,(
    ! [A_18] : k4_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_974,c_192])).

tff(c_1383,plain,(
    ! [A_106,B_107] : k3_xboole_0(A_106,k4_xboole_0(B_107,k3_xboole_0(A_106,B_107))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1376,c_1107])).

tff(c_1487,plain,(
    ! [A_109,B_110] : k3_xboole_0(A_109,k4_xboole_0(B_110,A_109)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_1383])).

tff(c_38,plain,(
    ! [A_19,B_20] : k4_xboole_0(A_19,k3_xboole_0(A_19,B_20)) = k4_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1513,plain,(
    ! [A_109,B_110] : k4_xboole_0(A_109,k4_xboole_0(B_110,A_109)) = k4_xboole_0(A_109,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1487,c_38])).

tff(c_1561,plain,(
    ! [A_109,B_110] : k4_xboole_0(A_109,k4_xboole_0(B_110,A_109)) = A_109 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1513])).

tff(c_20101,plain,(
    ! [C_358] : r1_tarski(k4_xboole_0('#skF_4',C_358),k4_xboole_0('#skF_5',C_358)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1451,c_19280])).

tff(c_28829,plain,(
    ! [B_429] : r1_tarski('#skF_4',k4_xboole_0('#skF_5',k4_xboole_0(B_429,'#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1561,c_20101])).

tff(c_58,plain,(
    r2_hidden('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1178,plain,(
    ! [C_100,B_101,A_102] :
      ( r2_hidden(C_100,B_101)
      | ~ r2_hidden(C_100,A_102)
      | ~ r1_tarski(A_102,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1265,plain,(
    ! [B_105] :
      ( r2_hidden('#skF_7',B_105)
      | ~ r1_tarski('#skF_4',B_105) ) ),
    inference(resolution,[status(thm)],[c_58,c_1178])).

tff(c_12,plain,(
    ! [D_13,B_9,A_8] :
      ( ~ r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,k4_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1307,plain,(
    ! [B_9,A_8] :
      ( ~ r2_hidden('#skF_7',B_9)
      | ~ r1_tarski('#skF_4',k4_xboole_0(A_8,B_9)) ) ),
    inference(resolution,[status(thm)],[c_1265,c_12])).

tff(c_28901,plain,(
    ! [B_430] : ~ r2_hidden('#skF_7',k4_xboole_0(B_430,'#skF_4')) ),
    inference(resolution,[status(thm)],[c_28829,c_1307])).

tff(c_28959,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),'#skF_4') = k1_tarski('#skF_7') ),
    inference(resolution,[status(thm)],[c_718,c_28901])).

tff(c_567,plain,(
    ! [A_79,B_80] : k4_xboole_0(A_79,k3_xboole_0(B_80,A_79)) = k4_xboole_0(A_79,B_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_298])).

tff(c_588,plain,(
    ! [A_79,B_80] : k4_xboole_0(A_79,k4_xboole_0(A_79,B_80)) = k3_xboole_0(A_79,k3_xboole_0(B_80,A_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_567,c_40])).

tff(c_637,plain,(
    ! [A_79,B_80] : k3_xboole_0(A_79,k3_xboole_0(B_80,A_79)) = k3_xboole_0(A_79,B_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_588])).

tff(c_19427,plain,(
    ! [A_79,B_80] : r1_tarski(k3_xboole_0(A_79,B_80),k3_xboole_0(B_80,A_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_637,c_19280])).

tff(c_29165,plain,(
    r1_tarski(k1_tarski('#skF_7'),k3_xboole_0('#skF_4',k1_tarski('#skF_7'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_28959,c_19427])).

tff(c_29279,plain,(
    r1_tarski(k1_tarski('#skF_7'),k3_xboole_0('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2843,c_29165])).

tff(c_29281,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19819,c_29279])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:52:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.10/4.89  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.19/4.90  
% 11.19/4.90  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.19/4.90  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 11.19/4.90  
% 11.19/4.90  %Foreground sorts:
% 11.19/4.90  
% 11.19/4.90  
% 11.19/4.90  %Background operators:
% 11.19/4.90  
% 11.19/4.90  
% 11.19/4.90  %Foreground operators:
% 11.19/4.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.19/4.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.19/4.90  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.19/4.90  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.19/4.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.19/4.90  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.19/4.90  tff('#skF_7', type, '#skF_7': $i).
% 11.19/4.90  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.19/4.90  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.19/4.90  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.19/4.90  tff('#skF_5', type, '#skF_5': $i).
% 11.19/4.90  tff('#skF_6', type, '#skF_6': $i).
% 11.19/4.90  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.19/4.90  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 11.19/4.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.19/4.90  tff('#skF_4', type, '#skF_4': $i).
% 11.19/4.90  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 11.19/4.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.19/4.90  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.19/4.90  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.19/4.90  
% 11.19/4.92  tff(f_84, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 11.19/4.92  tff(f_60, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.19/4.92  tff(f_54, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 11.19/4.92  tff(f_62, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 11.19/4.92  tff(f_58, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 11.19/4.92  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.19/4.92  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 11.19/4.92  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 11.19/4.92  tff(f_50, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.19/4.92  tff(f_75, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 11.19/4.92  tff(f_56, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 11.19/4.92  tff(c_56, plain, (k3_xboole_0('#skF_4', '#skF_6')!=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.19/4.92  tff(c_40, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k4_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.19/4.92  tff(c_62, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.19/4.92  tff(c_139, plain, (![A_43, B_44]: (k3_xboole_0(A_43, B_44)=A_43 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.19/4.92  tff(c_147, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_62, c_139])).
% 11.19/4.92  tff(c_1376, plain, (![A_106, B_107, C_108]: (k4_xboole_0(k3_xboole_0(A_106, B_107), C_108)=k3_xboole_0(A_106, k4_xboole_0(B_107, C_108)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.19/4.92  tff(c_1451, plain, (![C_108]: (k3_xboole_0('#skF_4', k4_xboole_0('#skF_5', C_108))=k4_xboole_0('#skF_4', C_108))), inference(superposition, [status(thm), theory('equality')], [c_147, c_1376])).
% 11.19/4.92  tff(c_60, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.19/4.92  tff(c_298, plain, (![A_58, B_59]: (k4_xboole_0(A_58, k3_xboole_0(A_58, B_59))=k4_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.19/4.92  tff(c_343, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_7'))=k4_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_60, c_298])).
% 11.19/4.92  tff(c_2520, plain, (![C_138]: (k3_xboole_0('#skF_4', k4_xboole_0('#skF_5', C_138))=k4_xboole_0('#skF_4', C_138))), inference(superposition, [status(thm), theory('equality')], [c_147, c_1376])).
% 11.19/4.92  tff(c_2570, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_7'))=k3_xboole_0('#skF_4', k4_xboole_0('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_343, c_2520])).
% 11.19/4.92  tff(c_2593, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_7'))=k4_xboole_0('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1451, c_2570])).
% 11.19/4.92  tff(c_2837, plain, (k4_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_6'))=k3_xboole_0('#skF_4', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2593, c_40])).
% 11.19/4.92  tff(c_2843, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_7'))=k3_xboole_0('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_2837])).
% 11.19/4.92  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.19/4.92  tff(c_221, plain, (![A_54, B_55]: (r2_hidden('#skF_1'(A_54, B_55), A_54) | r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.19/4.92  tff(c_14, plain, (![D_13, A_8, B_9]: (r2_hidden(D_13, A_8) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.19/4.92  tff(c_18616, plain, (![A_342, B_343, B_344]: (r2_hidden('#skF_1'(k4_xboole_0(A_342, B_343), B_344), A_342) | r1_tarski(k4_xboole_0(A_342, B_343), B_344))), inference(resolution, [status(thm)], [c_221, c_14])).
% 11.19/4.92  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.19/4.92  tff(c_18867, plain, (![A_345, B_346]: (r1_tarski(k4_xboole_0(A_345, B_346), A_345))), inference(resolution, [status(thm)], [c_18616, c_6])).
% 11.19/4.92  tff(c_19034, plain, (![A_347, B_348]: (r1_tarski(k3_xboole_0(A_347, B_348), A_347))), inference(superposition, [status(thm), theory('equality')], [c_40, c_18867])).
% 11.19/4.92  tff(c_19280, plain, (![A_349, B_350]: (r1_tarski(k3_xboole_0(A_349, B_350), B_350))), inference(superposition, [status(thm), theory('equality')], [c_2, c_19034])).
% 11.19/4.92  tff(c_19400, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_6'), k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_2843, c_19280])).
% 11.19/4.92  tff(c_28, plain, (![B_15, A_14]: (B_15=A_14 | ~r1_tarski(B_15, A_14) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.19/4.92  tff(c_19811, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_tarski('#skF_7') | ~r1_tarski(k1_tarski('#skF_7'), k3_xboole_0('#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_19400, c_28])).
% 11.19/4.92  tff(c_19819, plain, (~r1_tarski(k1_tarski('#skF_7'), k3_xboole_0('#skF_4', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_56, c_19811])).
% 11.19/4.92  tff(c_685, plain, (![A_84, B_85]: (k4_xboole_0(k1_tarski(A_84), B_85)=k1_tarski(A_84) | r2_hidden(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_75])).
% 11.19/4.92  tff(c_718, plain, (![A_84, B_22]: (k3_xboole_0(k1_tarski(A_84), B_22)=k1_tarski(A_84) | r2_hidden(A_84, k4_xboole_0(k1_tarski(A_84), B_22)))), inference(superposition, [status(thm), theory('equality')], [c_685, c_40])).
% 11.19/4.92  tff(c_36, plain, (![A_18]: (k4_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.19/4.92  tff(c_337, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_298])).
% 11.19/4.92  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.19/4.92  tff(c_364, plain, (![D_60, B_61, A_62]: (~r2_hidden(D_60, B_61) | ~r2_hidden(D_60, k4_xboole_0(A_62, B_61)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.19/4.92  tff(c_391, plain, (![D_63, A_64]: (~r2_hidden(D_63, k1_xboole_0) | ~r2_hidden(D_63, A_64))), inference(superposition, [status(thm), theory('equality')], [c_36, c_364])).
% 11.19/4.92  tff(c_868, plain, (![B_90, A_91]: (~r2_hidden('#skF_1'(k1_xboole_0, B_90), A_91) | r1_tarski(k1_xboole_0, B_90))), inference(resolution, [status(thm)], [c_8, c_391])).
% 11.19/4.92  tff(c_880, plain, (![B_92]: (r1_tarski(k1_xboole_0, B_92))), inference(resolution, [status(thm)], [c_8, c_868])).
% 11.19/4.92  tff(c_34, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 11.19/4.92  tff(c_935, plain, (![B_96]: (k3_xboole_0(k1_xboole_0, B_96)=k1_xboole_0)), inference(resolution, [status(thm)], [c_880, c_34])).
% 11.19/4.92  tff(c_974, plain, (![B_96]: (k3_xboole_0(B_96, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_935, c_2])).
% 11.19/4.92  tff(c_174, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k4_xboole_0(A_51, B_52))=k3_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_60])).
% 11.19/4.92  tff(c_192, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k3_xboole_0(A_18, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36, c_174])).
% 11.19/4.92  tff(c_1107, plain, (![A_18]: (k4_xboole_0(A_18, A_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_974, c_192])).
% 11.19/4.92  tff(c_1383, plain, (![A_106, B_107]: (k3_xboole_0(A_106, k4_xboole_0(B_107, k3_xboole_0(A_106, B_107)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1376, c_1107])).
% 11.19/4.92  tff(c_1487, plain, (![A_109, B_110]: (k3_xboole_0(A_109, k4_xboole_0(B_110, A_109))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_337, c_1383])).
% 11.19/4.92  tff(c_38, plain, (![A_19, B_20]: (k4_xboole_0(A_19, k3_xboole_0(A_19, B_20))=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_58])).
% 11.19/4.92  tff(c_1513, plain, (![A_109, B_110]: (k4_xboole_0(A_109, k4_xboole_0(B_110, A_109))=k4_xboole_0(A_109, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1487, c_38])).
% 11.19/4.92  tff(c_1561, plain, (![A_109, B_110]: (k4_xboole_0(A_109, k4_xboole_0(B_110, A_109))=A_109)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1513])).
% 11.19/4.92  tff(c_20101, plain, (![C_358]: (r1_tarski(k4_xboole_0('#skF_4', C_358), k4_xboole_0('#skF_5', C_358)))), inference(superposition, [status(thm), theory('equality')], [c_1451, c_19280])).
% 11.19/4.92  tff(c_28829, plain, (![B_429]: (r1_tarski('#skF_4', k4_xboole_0('#skF_5', k4_xboole_0(B_429, '#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_1561, c_20101])).
% 11.19/4.92  tff(c_58, plain, (r2_hidden('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.19/4.92  tff(c_1178, plain, (![C_100, B_101, A_102]: (r2_hidden(C_100, B_101) | ~r2_hidden(C_100, A_102) | ~r1_tarski(A_102, B_101))), inference(cnfTransformation, [status(thm)], [f_34])).
% 11.19/4.92  tff(c_1265, plain, (![B_105]: (r2_hidden('#skF_7', B_105) | ~r1_tarski('#skF_4', B_105))), inference(resolution, [status(thm)], [c_58, c_1178])).
% 11.19/4.92  tff(c_12, plain, (![D_13, B_9, A_8]: (~r2_hidden(D_13, B_9) | ~r2_hidden(D_13, k4_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.19/4.92  tff(c_1307, plain, (![B_9, A_8]: (~r2_hidden('#skF_7', B_9) | ~r1_tarski('#skF_4', k4_xboole_0(A_8, B_9)))), inference(resolution, [status(thm)], [c_1265, c_12])).
% 11.19/4.92  tff(c_28901, plain, (![B_430]: (~r2_hidden('#skF_7', k4_xboole_0(B_430, '#skF_4')))), inference(resolution, [status(thm)], [c_28829, c_1307])).
% 11.19/4.92  tff(c_28959, plain, (k3_xboole_0(k1_tarski('#skF_7'), '#skF_4')=k1_tarski('#skF_7')), inference(resolution, [status(thm)], [c_718, c_28901])).
% 11.19/4.92  tff(c_567, plain, (![A_79, B_80]: (k4_xboole_0(A_79, k3_xboole_0(B_80, A_79))=k4_xboole_0(A_79, B_80))), inference(superposition, [status(thm), theory('equality')], [c_2, c_298])).
% 11.19/4.92  tff(c_588, plain, (![A_79, B_80]: (k4_xboole_0(A_79, k4_xboole_0(A_79, B_80))=k3_xboole_0(A_79, k3_xboole_0(B_80, A_79)))), inference(superposition, [status(thm), theory('equality')], [c_567, c_40])).
% 11.19/4.92  tff(c_637, plain, (![A_79, B_80]: (k3_xboole_0(A_79, k3_xboole_0(B_80, A_79))=k3_xboole_0(A_79, B_80))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_588])).
% 11.19/4.92  tff(c_19427, plain, (![A_79, B_80]: (r1_tarski(k3_xboole_0(A_79, B_80), k3_xboole_0(B_80, A_79)))), inference(superposition, [status(thm), theory('equality')], [c_637, c_19280])).
% 11.19/4.92  tff(c_29165, plain, (r1_tarski(k1_tarski('#skF_7'), k3_xboole_0('#skF_4', k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_28959, c_19427])).
% 11.19/4.92  tff(c_29279, plain, (r1_tarski(k1_tarski('#skF_7'), k3_xboole_0('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2843, c_29165])).
% 11.19/4.92  tff(c_29281, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19819, c_29279])).
% 11.19/4.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.19/4.92  
% 11.19/4.92  Inference rules
% 11.19/4.92  ----------------------
% 11.19/4.92  #Ref     : 0
% 11.19/4.92  #Sup     : 7251
% 11.19/4.92  #Fact    : 0
% 11.19/4.92  #Define  : 0
% 11.19/4.92  #Split   : 4
% 11.19/4.92  #Chain   : 0
% 11.19/4.92  #Close   : 0
% 11.19/4.92  
% 11.19/4.92  Ordering : KBO
% 11.19/4.92  
% 11.19/4.92  Simplification rules
% 11.19/4.92  ----------------------
% 11.19/4.92  #Subsume      : 1352
% 11.19/4.92  #Demod        : 7479
% 11.19/4.92  #Tautology    : 3922
% 11.19/4.92  #SimpNegUnit  : 156
% 11.19/4.92  #BackRed      : 9
% 11.19/4.92  
% 11.19/4.92  #Partial instantiations: 0
% 11.19/4.92  #Strategies tried      : 1
% 11.19/4.92  
% 11.19/4.92  Timing (in seconds)
% 11.19/4.92  ----------------------
% 11.19/4.92  Preprocessing        : 0.30
% 11.19/4.92  Parsing              : 0.16
% 11.19/4.92  CNF conversion       : 0.02
% 11.19/4.92  Main loop            : 3.76
% 11.19/4.92  Inferencing          : 0.70
% 11.19/4.92  Reduction            : 2.07
% 11.19/4.92  Demodulation         : 1.73
% 11.19/4.92  BG Simplification    : 0.08
% 11.19/4.92  Subsumption          : 0.75
% 11.19/4.92  Abstraction          : 0.11
% 11.19/4.92  MUC search           : 0.00
% 11.19/4.92  Cooper               : 0.00
% 11.19/4.92  Total                : 4.11
% 11.19/4.92  Index Insertion      : 0.00
% 11.19/4.92  Index Deletion       : 0.00
% 11.19/4.92  Index Matching       : 0.00
% 11.19/4.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
