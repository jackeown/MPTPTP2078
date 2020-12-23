%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:02 EST 2020

% Result     : Theorem 4.80s
% Output     : CNFRefutation 4.80s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 302 expanded)
%              Number of leaves         :   26 ( 110 expanded)
%              Depth                    :   24
%              Number of atoms          :  229 ( 601 expanded)
%              Number of equality atoms :   63 ( 143 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_87,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(c_36,plain,
    ( k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_61,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_38,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_16,plain,(
    ! [A_6] :
      ( v1_relat_1(k4_relat_1(A_6))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_50,plain,(
    ! [A_20] :
      ( v1_relat_1(A_20)
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_54,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_50])).

tff(c_34,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_24,plain,(
    ! [A_11] :
      ( k2_relat_1(k4_relat_1(A_11)) = k1_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_107,plain,(
    ! [A_26] :
      ( ~ v1_xboole_0(k2_relat_1(A_26))
      | ~ v1_relat_1(A_26)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_183,plain,(
    ! [A_36] :
      ( ~ v1_xboole_0(k1_relat_1(A_36))
      | ~ v1_relat_1(k4_relat_1(A_36))
      | v1_xboole_0(k4_relat_1(A_36))
      | ~ v1_relat_1(A_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_107])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_216,plain,(
    ! [A_39] :
      ( k4_relat_1(A_39) = k1_xboole_0
      | ~ v1_xboole_0(k1_relat_1(A_39))
      | ~ v1_relat_1(k4_relat_1(A_39))
      | ~ v1_relat_1(A_39) ) ),
    inference(resolution,[status(thm)],[c_183,c_4])).

tff(c_225,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_216])).

tff(c_229,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2,c_225])).

tff(c_230,plain,(
    ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_229])).

tff(c_233,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_230])).

tff(c_237,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_233])).

tff(c_238,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_229])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k5_relat_1(A_7,B_8))
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_26,plain,(
    ! [A_11] :
      ( k1_relat_1(k4_relat_1(A_11)) = k2_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_30,plain,(
    ! [B_17,A_15] :
      ( k5_relat_1(k4_relat_1(B_17),k4_relat_1(A_15)) = k4_relat_1(k5_relat_1(A_15,B_17))
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_264,plain,(
    ! [A_15] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_15)) = k4_relat_1(k5_relat_1(A_15,k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_30])).

tff(c_303,plain,(
    ! [A_42] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_42)) = k4_relat_1(k5_relat_1(A_42,k1_xboole_0))
      | ~ v1_relat_1(A_42) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_264])).

tff(c_140,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_32,B_33)),k1_relat_1(A_32))
      | ~ v1_relat_1(B_33)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_148,plain,(
    ! [B_33] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_33)),k1_xboole_0)
      | ~ v1_relat_1(B_33)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_140])).

tff(c_152,plain,(
    ! [B_34] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_34)),k1_xboole_0)
      | ~ v1_relat_1(B_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_148])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_116,plain,(
    ! [B_27,A_28] :
      ( B_27 = A_28
      | ~ r1_tarski(B_27,A_28)
      | ~ r1_tarski(A_28,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_125,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_116])).

tff(c_158,plain,(
    ! [B_34] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_34)) = k1_xboole_0
      | ~ v1_relat_1(B_34) ) ),
    inference(resolution,[status(thm)],[c_152,c_125])).

tff(c_594,plain,(
    ! [A_50] :
      ( k1_relat_1(k4_relat_1(k5_relat_1(A_50,k1_xboole_0))) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(A_50))
      | ~ v1_relat_1(A_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_303,c_158])).

tff(c_1343,plain,(
    ! [A_66] :
      ( k2_relat_1(k5_relat_1(A_66,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(A_66))
      | ~ v1_relat_1(A_66)
      | ~ v1_relat_1(k5_relat_1(A_66,k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_594])).

tff(c_1360,plain,(
    ! [A_7] :
      ( k2_relat_1(k5_relat_1(A_7,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(A_7))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_18,c_1343])).

tff(c_1370,plain,(
    ! [A_67] :
      ( k2_relat_1(k5_relat_1(A_67,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(A_67))
      | ~ v1_relat_1(A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1360])).

tff(c_1413,plain,(
    ! [A_68] :
      ( k2_relat_1(k5_relat_1(A_68,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_68) ) ),
    inference(resolution,[status(thm)],[c_16,c_1370])).

tff(c_20,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(k2_relat_1(A_9))
      | ~ v1_relat_1(A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1425,plain,(
    ! [A_68] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_68,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_68,k1_xboole_0))
      | ~ v1_relat_1(A_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1413,c_20])).

tff(c_1441,plain,(
    ! [A_69] :
      ( ~ v1_relat_1(k5_relat_1(A_69,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_69,k1_xboole_0))
      | ~ v1_relat_1(A_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1425])).

tff(c_1458,plain,(
    ! [A_70] :
      ( k5_relat_1(A_70,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_70,k1_xboole_0))
      | ~ v1_relat_1(A_70) ) ),
    inference(resolution,[status(thm)],[c_1441,c_4])).

tff(c_1475,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_18,c_1458])).

tff(c_1563,plain,(
    ! [A_73] :
      ( k5_relat_1(A_73,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1475])).

tff(c_1665,plain,(
    ! [A_74] :
      ( k5_relat_1(k4_relat_1(A_74),k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_74) ) ),
    inference(resolution,[status(thm)],[c_16,c_1563])).

tff(c_22,plain,(
    ! [A_10] :
      ( k4_relat_1(k4_relat_1(A_10)) = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_195,plain,(
    ! [B_37,A_38] :
      ( k5_relat_1(k4_relat_1(B_37),k4_relat_1(A_38)) = k4_relat_1(k5_relat_1(A_38,B_37))
      | ~ v1_relat_1(B_37)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_213,plain,(
    ! [A_10,B_37] :
      ( k4_relat_1(k5_relat_1(k4_relat_1(A_10),B_37)) = k5_relat_1(k4_relat_1(B_37),A_10)
      | ~ v1_relat_1(B_37)
      | ~ v1_relat_1(k4_relat_1(A_10))
      | ~ v1_relat_1(A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_195])).

tff(c_1698,plain,(
    ! [A_74] :
      ( k5_relat_1(k4_relat_1(k1_xboole_0),A_74) = k4_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k4_relat_1(A_74))
      | ~ v1_relat_1(A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1665,c_213])).

tff(c_2021,plain,(
    ! [A_78] :
      ( k5_relat_1(k1_xboole_0,A_78) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(A_78))
      | ~ v1_relat_1(A_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_238,c_238,c_1698])).

tff(c_2069,plain,(
    ! [A_79] :
      ( k5_relat_1(k1_xboole_0,A_79) = k1_xboole_0
      | ~ v1_relat_1(A_79) ) ),
    inference(resolution,[status(thm)],[c_16,c_2021])).

tff(c_2096,plain,(
    k5_relat_1(k1_xboole_0,'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_2069])).

tff(c_2109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_2096])).

tff(c_2110,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_2155,plain,(
    ! [A_84] :
      ( k2_relat_1(k4_relat_1(A_84)) = k1_relat_1(A_84)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2278,plain,(
    ! [A_96] :
      ( ~ v1_xboole_0(k1_relat_1(A_96))
      | ~ v1_relat_1(k4_relat_1(A_96))
      | v1_xboole_0(k4_relat_1(A_96))
      | ~ v1_relat_1(A_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2155,c_20])).

tff(c_2290,plain,(
    ! [A_97] :
      ( k4_relat_1(A_97) = k1_xboole_0
      | ~ v1_xboole_0(k1_relat_1(A_97))
      | ~ v1_relat_1(k4_relat_1(A_97))
      | ~ v1_relat_1(A_97) ) ),
    inference(resolution,[status(thm)],[c_2278,c_4])).

tff(c_2299,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2290])).

tff(c_2303,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2,c_2299])).

tff(c_2304,plain,(
    ~ v1_relat_1(k4_relat_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_2303])).

tff(c_2307,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_2304])).

tff(c_2311,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2307])).

tff(c_2312,plain,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_2303])).

tff(c_2341,plain,(
    ! [A_15] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_15)) = k4_relat_1(k5_relat_1(A_15,k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2312,c_30])).

tff(c_2377,plain,(
    ! [A_100] :
      ( k5_relat_1(k1_xboole_0,k4_relat_1(A_100)) = k4_relat_1(k5_relat_1(A_100,k1_xboole_0))
      | ~ v1_relat_1(A_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2341])).

tff(c_2199,plain,(
    ! [A_90,B_91] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_90,B_91)),k1_relat_1(A_90))
      | ~ v1_relat_1(B_91)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2210,plain,(
    ! [B_91] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_91)),k1_xboole_0)
      | ~ v1_relat_1(B_91)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_2199])).

tff(c_2216,plain,(
    ! [B_92] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,B_92)),k1_xboole_0)
      | ~ v1_relat_1(B_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2210])).

tff(c_2176,plain,(
    ! [B_87,A_88] :
      ( B_87 = A_88
      | ~ r1_tarski(B_87,A_88)
      | ~ r1_tarski(A_88,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2185,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_2176])).

tff(c_2225,plain,(
    ! [B_92] :
      ( k1_relat_1(k5_relat_1(k1_xboole_0,B_92)) = k1_xboole_0
      | ~ v1_relat_1(B_92) ) ),
    inference(resolution,[status(thm)],[c_2216,c_2185])).

tff(c_2595,plain,(
    ! [A_107] :
      ( k1_relat_1(k4_relat_1(k5_relat_1(A_107,k1_xboole_0))) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(A_107))
      | ~ v1_relat_1(A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2377,c_2225])).

tff(c_3419,plain,(
    ! [A_122] :
      ( k2_relat_1(k5_relat_1(A_122,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(A_122))
      | ~ v1_relat_1(A_122)
      | ~ v1_relat_1(k5_relat_1(A_122,k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2595])).

tff(c_3436,plain,(
    ! [A_7] :
      ( k2_relat_1(k5_relat_1(A_7,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(A_7))
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_18,c_3419])).

tff(c_3446,plain,(
    ! [A_123] :
      ( k2_relat_1(k5_relat_1(A_123,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(k4_relat_1(A_123))
      | ~ v1_relat_1(A_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3436])).

tff(c_3489,plain,(
    ! [A_124] :
      ( k2_relat_1(k5_relat_1(A_124,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_124) ) ),
    inference(resolution,[status(thm)],[c_16,c_3446])).

tff(c_3501,plain,(
    ! [A_124] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_124,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_124,k1_xboole_0))
      | ~ v1_relat_1(A_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3489,c_20])).

tff(c_3564,plain,(
    ! [A_127] :
      ( ~ v1_relat_1(k5_relat_1(A_127,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_127,k1_xboole_0))
      | ~ v1_relat_1(A_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3501])).

tff(c_3581,plain,(
    ! [A_128] :
      ( k5_relat_1(A_128,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_128,k1_xboole_0))
      | ~ v1_relat_1(A_128) ) ),
    inference(resolution,[status(thm)],[c_3564,c_4])).

tff(c_3598,plain,(
    ! [A_7] :
      ( k5_relat_1(A_7,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_18,c_3581])).

tff(c_3608,plain,(
    ! [A_129] :
      ( k5_relat_1(A_129,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_129) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3598])).

tff(c_3635,plain,(
    k5_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_3608])).

tff(c_3648,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2110,c_3635])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:59:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.80/1.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.80/1.87  
% 4.80/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.80/1.88  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k5_relat_1 > #nlpp > k4_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 4.80/1.88  
% 4.80/1.88  %Foreground sorts:
% 4.80/1.88  
% 4.80/1.88  
% 4.80/1.88  %Background operators:
% 4.80/1.88  
% 4.80/1.88  
% 4.80/1.88  %Foreground operators:
% 4.80/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.80/1.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.80/1.88  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.80/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.80/1.88  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.80/1.88  tff('#skF_1', type, '#skF_1': $i).
% 4.80/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.80/1.88  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.80/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.80/1.88  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.80/1.88  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.80/1.88  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 4.80/1.88  
% 4.80/1.89  tff(f_94, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_relat_1)).
% 4.80/1.89  tff(f_46, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 4.80/1.89  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.80/1.89  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 4.80/1.89  tff(f_87, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 4.80/1.89  tff(f_70, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 4.80/1.89  tff(f_60, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 4.80/1.89  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.80/1.89  tff(f_52, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 4.80/1.89  tff(f_84, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 4.80/1.89  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 4.80/1.89  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.80/1.89  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.80/1.89  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 4.80/1.89  tff(c_36, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.80/1.89  tff(c_61, plain, (k5_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 4.80/1.89  tff(c_38, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.80/1.89  tff(c_16, plain, (![A_6]: (v1_relat_1(k4_relat_1(A_6)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.80/1.89  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.80/1.89  tff(c_50, plain, (![A_20]: (v1_relat_1(A_20) | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.80/1.89  tff(c_54, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_50])).
% 4.80/1.89  tff(c_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.80/1.89  tff(c_24, plain, (![A_11]: (k2_relat_1(k4_relat_1(A_11))=k1_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.80/1.89  tff(c_107, plain, (![A_26]: (~v1_xboole_0(k2_relat_1(A_26)) | ~v1_relat_1(A_26) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.80/1.89  tff(c_183, plain, (![A_36]: (~v1_xboole_0(k1_relat_1(A_36)) | ~v1_relat_1(k4_relat_1(A_36)) | v1_xboole_0(k4_relat_1(A_36)) | ~v1_relat_1(A_36))), inference(superposition, [status(thm), theory('equality')], [c_24, c_107])).
% 4.80/1.89  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.80/1.89  tff(c_216, plain, (![A_39]: (k4_relat_1(A_39)=k1_xboole_0 | ~v1_xboole_0(k1_relat_1(A_39)) | ~v1_relat_1(k4_relat_1(A_39)) | ~v1_relat_1(A_39))), inference(resolution, [status(thm)], [c_183, c_4])).
% 4.80/1.89  tff(c_225, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_34, c_216])).
% 4.80/1.89  tff(c_229, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2, c_225])).
% 4.80/1.89  tff(c_230, plain, (~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_229])).
% 4.80/1.89  tff(c_233, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_230])).
% 4.80/1.89  tff(c_237, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_233])).
% 4.80/1.89  tff(c_238, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_229])).
% 4.80/1.89  tff(c_18, plain, (![A_7, B_8]: (v1_relat_1(k5_relat_1(A_7, B_8)) | ~v1_relat_1(B_8) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.80/1.89  tff(c_26, plain, (![A_11]: (k1_relat_1(k4_relat_1(A_11))=k2_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.80/1.89  tff(c_30, plain, (![B_17, A_15]: (k5_relat_1(k4_relat_1(B_17), k4_relat_1(A_15))=k4_relat_1(k5_relat_1(A_15, B_17)) | ~v1_relat_1(B_17) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.80/1.89  tff(c_264, plain, (![A_15]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_15))=k4_relat_1(k5_relat_1(A_15, k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_15))), inference(superposition, [status(thm), theory('equality')], [c_238, c_30])).
% 4.80/1.89  tff(c_303, plain, (![A_42]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_42))=k4_relat_1(k5_relat_1(A_42, k1_xboole_0)) | ~v1_relat_1(A_42))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_264])).
% 4.80/1.89  tff(c_140, plain, (![A_32, B_33]: (r1_tarski(k1_relat_1(k5_relat_1(A_32, B_33)), k1_relat_1(A_32)) | ~v1_relat_1(B_33) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.80/1.89  tff(c_148, plain, (![B_33]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_33)), k1_xboole_0) | ~v1_relat_1(B_33) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_140])).
% 4.80/1.89  tff(c_152, plain, (![B_34]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_34)), k1_xboole_0) | ~v1_relat_1(B_34))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_148])).
% 4.80/1.89  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.80/1.89  tff(c_116, plain, (![B_27, A_28]: (B_27=A_28 | ~r1_tarski(B_27, A_28) | ~r1_tarski(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.80/1.89  tff(c_125, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_116])).
% 4.80/1.89  tff(c_158, plain, (![B_34]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_34))=k1_xboole_0 | ~v1_relat_1(B_34))), inference(resolution, [status(thm)], [c_152, c_125])).
% 4.80/1.89  tff(c_594, plain, (![A_50]: (k1_relat_1(k4_relat_1(k5_relat_1(A_50, k1_xboole_0)))=k1_xboole_0 | ~v1_relat_1(k4_relat_1(A_50)) | ~v1_relat_1(A_50))), inference(superposition, [status(thm), theory('equality')], [c_303, c_158])).
% 4.80/1.89  tff(c_1343, plain, (![A_66]: (k2_relat_1(k5_relat_1(A_66, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(k4_relat_1(A_66)) | ~v1_relat_1(A_66) | ~v1_relat_1(k5_relat_1(A_66, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_594])).
% 4.80/1.89  tff(c_1360, plain, (![A_7]: (k2_relat_1(k5_relat_1(A_7, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(k4_relat_1(A_7)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_18, c_1343])).
% 4.80/1.89  tff(c_1370, plain, (![A_67]: (k2_relat_1(k5_relat_1(A_67, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(k4_relat_1(A_67)) | ~v1_relat_1(A_67))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1360])).
% 4.80/1.89  tff(c_1413, plain, (![A_68]: (k2_relat_1(k5_relat_1(A_68, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_68))), inference(resolution, [status(thm)], [c_16, c_1370])).
% 4.80/1.89  tff(c_20, plain, (![A_9]: (~v1_xboole_0(k2_relat_1(A_9)) | ~v1_relat_1(A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.80/1.89  tff(c_1425, plain, (![A_68]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_68, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_68, k1_xboole_0)) | ~v1_relat_1(A_68))), inference(superposition, [status(thm), theory('equality')], [c_1413, c_20])).
% 4.80/1.89  tff(c_1441, plain, (![A_69]: (~v1_relat_1(k5_relat_1(A_69, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_69, k1_xboole_0)) | ~v1_relat_1(A_69))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1425])).
% 4.80/1.89  tff(c_1458, plain, (![A_70]: (k5_relat_1(A_70, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_70, k1_xboole_0)) | ~v1_relat_1(A_70))), inference(resolution, [status(thm)], [c_1441, c_4])).
% 4.80/1.89  tff(c_1475, plain, (![A_7]: (k5_relat_1(A_7, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_18, c_1458])).
% 4.80/1.89  tff(c_1563, plain, (![A_73]: (k5_relat_1(A_73, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_73))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1475])).
% 4.80/1.89  tff(c_1665, plain, (![A_74]: (k5_relat_1(k4_relat_1(A_74), k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_74))), inference(resolution, [status(thm)], [c_16, c_1563])).
% 4.80/1.89  tff(c_22, plain, (![A_10]: (k4_relat_1(k4_relat_1(A_10))=A_10 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.80/1.89  tff(c_195, plain, (![B_37, A_38]: (k5_relat_1(k4_relat_1(B_37), k4_relat_1(A_38))=k4_relat_1(k5_relat_1(A_38, B_37)) | ~v1_relat_1(B_37) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.80/1.89  tff(c_213, plain, (![A_10, B_37]: (k4_relat_1(k5_relat_1(k4_relat_1(A_10), B_37))=k5_relat_1(k4_relat_1(B_37), A_10) | ~v1_relat_1(B_37) | ~v1_relat_1(k4_relat_1(A_10)) | ~v1_relat_1(A_10))), inference(superposition, [status(thm), theory('equality')], [c_22, c_195])).
% 4.80/1.89  tff(c_1698, plain, (![A_74]: (k5_relat_1(k4_relat_1(k1_xboole_0), A_74)=k4_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k4_relat_1(A_74)) | ~v1_relat_1(A_74) | ~v1_relat_1(A_74))), inference(superposition, [status(thm), theory('equality')], [c_1665, c_213])).
% 4.80/1.89  tff(c_2021, plain, (![A_78]: (k5_relat_1(k1_xboole_0, A_78)=k1_xboole_0 | ~v1_relat_1(k4_relat_1(A_78)) | ~v1_relat_1(A_78))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_238, c_238, c_1698])).
% 4.80/1.89  tff(c_2069, plain, (![A_79]: (k5_relat_1(k1_xboole_0, A_79)=k1_xboole_0 | ~v1_relat_1(A_79))), inference(resolution, [status(thm)], [c_16, c_2021])).
% 4.80/1.89  tff(c_2096, plain, (k5_relat_1(k1_xboole_0, '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_2069])).
% 4.80/1.89  tff(c_2109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_2096])).
% 4.80/1.89  tff(c_2110, plain, (k5_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 4.80/1.89  tff(c_2155, plain, (![A_84]: (k2_relat_1(k4_relat_1(A_84))=k1_relat_1(A_84) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.80/1.89  tff(c_2278, plain, (![A_96]: (~v1_xboole_0(k1_relat_1(A_96)) | ~v1_relat_1(k4_relat_1(A_96)) | v1_xboole_0(k4_relat_1(A_96)) | ~v1_relat_1(A_96))), inference(superposition, [status(thm), theory('equality')], [c_2155, c_20])).
% 4.80/1.89  tff(c_2290, plain, (![A_97]: (k4_relat_1(A_97)=k1_xboole_0 | ~v1_xboole_0(k1_relat_1(A_97)) | ~v1_relat_1(k4_relat_1(A_97)) | ~v1_relat_1(A_97))), inference(resolution, [status(thm)], [c_2278, c_4])).
% 4.80/1.89  tff(c_2299, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k4_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_34, c_2290])).
% 4.80/1.89  tff(c_2303, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2, c_2299])).
% 4.80/1.89  tff(c_2304, plain, (~v1_relat_1(k4_relat_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_2303])).
% 4.80/1.89  tff(c_2307, plain, (~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_2304])).
% 4.80/1.89  tff(c_2311, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_2307])).
% 4.80/1.89  tff(c_2312, plain, (k4_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_2303])).
% 4.80/1.89  tff(c_2341, plain, (![A_15]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_15))=k4_relat_1(k5_relat_1(A_15, k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_15))), inference(superposition, [status(thm), theory('equality')], [c_2312, c_30])).
% 4.80/1.89  tff(c_2377, plain, (![A_100]: (k5_relat_1(k1_xboole_0, k4_relat_1(A_100))=k4_relat_1(k5_relat_1(A_100, k1_xboole_0)) | ~v1_relat_1(A_100))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2341])).
% 4.80/1.89  tff(c_2199, plain, (![A_90, B_91]: (r1_tarski(k1_relat_1(k5_relat_1(A_90, B_91)), k1_relat_1(A_90)) | ~v1_relat_1(B_91) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.80/1.89  tff(c_2210, plain, (![B_91]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_91)), k1_xboole_0) | ~v1_relat_1(B_91) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_2199])).
% 4.80/1.89  tff(c_2216, plain, (![B_92]: (r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0, B_92)), k1_xboole_0) | ~v1_relat_1(B_92))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_2210])).
% 4.80/1.89  tff(c_2176, plain, (![B_87, A_88]: (B_87=A_88 | ~r1_tarski(B_87, A_88) | ~r1_tarski(A_88, B_87))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.80/1.89  tff(c_2185, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_2176])).
% 4.80/1.89  tff(c_2225, plain, (![B_92]: (k1_relat_1(k5_relat_1(k1_xboole_0, B_92))=k1_xboole_0 | ~v1_relat_1(B_92))), inference(resolution, [status(thm)], [c_2216, c_2185])).
% 4.80/1.89  tff(c_2595, plain, (![A_107]: (k1_relat_1(k4_relat_1(k5_relat_1(A_107, k1_xboole_0)))=k1_xboole_0 | ~v1_relat_1(k4_relat_1(A_107)) | ~v1_relat_1(A_107))), inference(superposition, [status(thm), theory('equality')], [c_2377, c_2225])).
% 4.80/1.89  tff(c_3419, plain, (![A_122]: (k2_relat_1(k5_relat_1(A_122, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(k4_relat_1(A_122)) | ~v1_relat_1(A_122) | ~v1_relat_1(k5_relat_1(A_122, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2595])).
% 4.80/1.89  tff(c_3436, plain, (![A_7]: (k2_relat_1(k5_relat_1(A_7, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(k4_relat_1(A_7)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_18, c_3419])).
% 4.80/1.89  tff(c_3446, plain, (![A_123]: (k2_relat_1(k5_relat_1(A_123, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(k4_relat_1(A_123)) | ~v1_relat_1(A_123))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3436])).
% 4.80/1.89  tff(c_3489, plain, (![A_124]: (k2_relat_1(k5_relat_1(A_124, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_124))), inference(resolution, [status(thm)], [c_16, c_3446])).
% 4.80/1.89  tff(c_3501, plain, (![A_124]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_124, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_124, k1_xboole_0)) | ~v1_relat_1(A_124))), inference(superposition, [status(thm), theory('equality')], [c_3489, c_20])).
% 4.80/1.89  tff(c_3564, plain, (![A_127]: (~v1_relat_1(k5_relat_1(A_127, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_127, k1_xboole_0)) | ~v1_relat_1(A_127))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_3501])).
% 4.80/1.89  tff(c_3581, plain, (![A_128]: (k5_relat_1(A_128, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_128, k1_xboole_0)) | ~v1_relat_1(A_128))), inference(resolution, [status(thm)], [c_3564, c_4])).
% 4.80/1.89  tff(c_3598, plain, (![A_7]: (k5_relat_1(A_7, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_18, c_3581])).
% 4.80/1.89  tff(c_3608, plain, (![A_129]: (k5_relat_1(A_129, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_129))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3598])).
% 4.80/1.89  tff(c_3635, plain, (k5_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_3608])).
% 4.80/1.89  tff(c_3648, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2110, c_3635])).
% 4.80/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.80/1.89  
% 4.80/1.89  Inference rules
% 4.80/1.89  ----------------------
% 4.80/1.89  #Ref     : 0
% 4.80/1.89  #Sup     : 904
% 4.80/1.89  #Fact    : 0
% 4.80/1.89  #Define  : 0
% 4.80/1.89  #Split   : 4
% 4.80/1.89  #Chain   : 0
% 4.80/1.89  #Close   : 0
% 4.80/1.89  
% 4.80/1.89  Ordering : KBO
% 4.80/1.89  
% 4.80/1.89  Simplification rules
% 4.80/1.89  ----------------------
% 4.80/1.90  #Subsume      : 107
% 4.80/1.90  #Demod        : 967
% 4.80/1.90  #Tautology    : 309
% 4.80/1.90  #SimpNegUnit  : 2
% 4.80/1.90  #BackRed      : 8
% 4.80/1.90  
% 4.80/1.90  #Partial instantiations: 0
% 4.80/1.90  #Strategies tried      : 1
% 4.80/1.90  
% 4.80/1.90  Timing (in seconds)
% 4.80/1.90  ----------------------
% 4.80/1.90  Preprocessing        : 0.30
% 4.80/1.90  Parsing              : 0.17
% 4.80/1.90  CNF conversion       : 0.02
% 4.80/1.90  Main loop            : 0.83
% 4.80/1.90  Inferencing          : 0.28
% 4.80/1.90  Reduction            : 0.25
% 4.80/1.90  Demodulation         : 0.18
% 4.80/1.90  BG Simplification    : 0.04
% 4.80/1.90  Subsumption          : 0.20
% 4.80/1.90  Abstraction          : 0.04
% 4.80/1.90  MUC search           : 0.00
% 4.80/1.90  Cooper               : 0.00
% 4.80/1.90  Total                : 1.17
% 4.80/1.90  Index Insertion      : 0.00
% 4.80/1.90  Index Deletion       : 0.00
% 4.80/1.90  Index Matching       : 0.00
% 4.80/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
