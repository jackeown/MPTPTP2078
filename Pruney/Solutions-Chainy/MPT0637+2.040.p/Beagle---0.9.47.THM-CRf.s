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
% DateTime   : Thu Dec  3 10:03:29 EST 2020

% Result     : Theorem 19.03s
% Output     : CNFRefutation 19.03s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 377 expanded)
%              Number of leaves         :   30 ( 148 expanded)
%              Depth                    :   15
%              Number of atoms          :  125 ( 731 expanded)
%              Number of equality atoms :   45 ( 242 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_55,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_56,plain,(
    ! [B_37,A_38] : k3_xboole_0(B_37,A_38) = k3_xboole_0(A_38,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_71,plain,(
    ! [B_37,A_38] : r1_tarski(k3_xboole_0(B_37,A_38),A_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_4])).

tff(c_30,plain,(
    ! [A_30] : v1_relat_1(k6_relat_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_18,plain,(
    ! [A_21] : k2_relat_1(k6_relat_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_124,plain,(
    ! [A_47] :
      ( k5_relat_1(A_47,k6_relat_1(k2_relat_1(A_47))) = A_47
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_136,plain,(
    ! [A_21] :
      ( k5_relat_1(k6_relat_1(A_21),k6_relat_1(A_21)) = k6_relat_1(A_21)
      | ~ v1_relat_1(k6_relat_1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_124])).

tff(c_142,plain,(
    ! [A_21] : k5_relat_1(k6_relat_1(A_21),k6_relat_1(A_21)) = k6_relat_1(A_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_136])).

tff(c_28,plain,(
    ! [A_28,B_29] :
      ( k5_relat_1(k6_relat_1(A_28),B_29) = k7_relat_1(B_29,A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_466,plain,(
    ! [A_72,B_73,C_74] :
      ( k5_relat_1(k5_relat_1(A_72,B_73),C_74) = k5_relat_1(A_72,k5_relat_1(B_73,C_74))
      | ~ v1_relat_1(C_74)
      | ~ v1_relat_1(B_73)
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_488,plain,(
    ! [A_28,B_29,C_74] :
      ( k5_relat_1(k6_relat_1(A_28),k5_relat_1(B_29,C_74)) = k5_relat_1(k7_relat_1(B_29,A_28),C_74)
      | ~ v1_relat_1(C_74)
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(k6_relat_1(A_28))
      | ~ v1_relat_1(B_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_466])).

tff(c_1993,plain,(
    ! [A_107,B_108,C_109] :
      ( k5_relat_1(k6_relat_1(A_107),k5_relat_1(B_108,C_109)) = k5_relat_1(k7_relat_1(B_108,A_107),C_109)
      | ~ v1_relat_1(C_109)
      | ~ v1_relat_1(B_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_488])).

tff(c_2069,plain,(
    ! [A_21,A_107] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_21),A_107),k6_relat_1(A_21)) = k5_relat_1(k6_relat_1(A_107),k6_relat_1(A_21))
      | ~ v1_relat_1(k6_relat_1(A_21))
      | ~ v1_relat_1(k6_relat_1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_1993])).

tff(c_2098,plain,(
    ! [A_21,A_107] : k5_relat_1(k7_relat_1(k6_relat_1(A_21),A_107),k6_relat_1(A_21)) = k5_relat_1(k6_relat_1(A_107),k6_relat_1(A_21)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_2069])).

tff(c_22113,plain,(
    ! [B_322,C_323,A_324] :
      ( k7_relat_1(k5_relat_1(B_322,C_323),A_324) = k5_relat_1(k7_relat_1(B_322,A_324),C_323)
      | ~ v1_relat_1(k5_relat_1(B_322,C_323))
      | ~ v1_relat_1(C_323)
      | ~ v1_relat_1(B_322) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1993,c_28])).

tff(c_22179,plain,(
    ! [A_21,A_324] :
      ( k7_relat_1(k5_relat_1(k6_relat_1(A_21),k6_relat_1(A_21)),A_324) = k5_relat_1(k7_relat_1(k6_relat_1(A_21),A_324),k6_relat_1(A_21))
      | ~ v1_relat_1(k6_relat_1(A_21))
      | ~ v1_relat_1(k6_relat_1(A_21))
      | ~ v1_relat_1(k6_relat_1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_22113])).

tff(c_22237,plain,(
    ! [A_324,A_21] : k5_relat_1(k6_relat_1(A_324),k6_relat_1(A_21)) = k7_relat_1(k6_relat_1(A_21),A_324) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_30,c_2098,c_142,c_22179])).

tff(c_355,plain,(
    ! [B_65,A_66] :
      ( k5_relat_1(B_65,k6_relat_1(A_66)) = B_65
      | ~ r1_tarski(k2_relat_1(B_65),A_66)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_362,plain,(
    ! [A_21,A_66] :
      ( k5_relat_1(k6_relat_1(A_21),k6_relat_1(A_66)) = k6_relat_1(A_21)
      | ~ r1_tarski(A_21,A_66)
      | ~ v1_relat_1(k6_relat_1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_355])).

tff(c_572,plain,(
    ! [A_77,A_78] :
      ( k5_relat_1(k6_relat_1(A_77),k6_relat_1(A_78)) = k6_relat_1(A_77)
      | ~ r1_tarski(A_77,A_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_362])).

tff(c_581,plain,(
    ! [A_78,A_77] :
      ( k7_relat_1(k6_relat_1(A_78),A_77) = k6_relat_1(A_77)
      | ~ v1_relat_1(k6_relat_1(A_78))
      | ~ r1_tarski(A_77,A_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_572,c_28])).

tff(c_622,plain,(
    ! [A_78,A_77] :
      ( k7_relat_1(k6_relat_1(A_78),A_77) = k6_relat_1(A_77)
      | ~ r1_tarski(A_77,A_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_581])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k5_relat_1(A_12,B_13))
      | ~ v1_relat_1(B_13)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2027,plain,(
    ! [B_108,A_107,C_109] :
      ( v1_relat_1(k5_relat_1(k7_relat_1(B_108,A_107),C_109))
      | ~ v1_relat_1(k5_relat_1(B_108,C_109))
      | ~ v1_relat_1(k6_relat_1(A_107))
      | ~ v1_relat_1(C_109)
      | ~ v1_relat_1(B_108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1993,c_12])).

tff(c_7781,plain,(
    ! [B_196,A_197,C_198] :
      ( v1_relat_1(k5_relat_1(k7_relat_1(B_196,A_197),C_198))
      | ~ v1_relat_1(k5_relat_1(B_196,C_198))
      | ~ v1_relat_1(C_198)
      | ~ v1_relat_1(B_196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2027])).

tff(c_7797,plain,(
    ! [A_107,A_21] :
      ( v1_relat_1(k5_relat_1(k6_relat_1(A_107),k6_relat_1(A_21)))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(A_21),k6_relat_1(A_21)))
      | ~ v1_relat_1(k6_relat_1(A_21))
      | ~ v1_relat_1(k6_relat_1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2098,c_7781])).

tff(c_7836,plain,(
    ! [A_199,A_200] : v1_relat_1(k5_relat_1(k6_relat_1(A_199),k6_relat_1(A_200))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_30,c_142,c_7797])).

tff(c_7850,plain,(
    ! [A_200,A_28] :
      ( v1_relat_1(k7_relat_1(k6_relat_1(A_200),A_28))
      | ~ v1_relat_1(k6_relat_1(A_200)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_7836])).

tff(c_7867,plain,(
    ! [A_200,A_28] : v1_relat_1(k7_relat_1(k6_relat_1(A_200),A_28)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_7850])).

tff(c_16,plain,(
    ! [A_21] : k1_relat_1(k6_relat_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_269,plain,(
    ! [B_59,A_60] :
      ( k3_xboole_0(k1_relat_1(B_59),A_60) = k1_relat_1(k7_relat_1(B_59,A_60))
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_298,plain,(
    ! [A_21,A_60] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_21),A_60)) = k3_xboole_0(A_21,A_60)
      | ~ v1_relat_1(k6_relat_1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_269])).

tff(c_302,plain,(
    ! [A_21,A_60] : k1_relat_1(k7_relat_1(k6_relat_1(A_21),A_60)) = k3_xboole_0(A_21,A_60) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_298])).

tff(c_20,plain,(
    ! [A_22] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_22)),A_22) = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_24951,plain,(
    ! [B_355,C_356] :
      ( k5_relat_1(k7_relat_1(B_355,k1_relat_1(k5_relat_1(B_355,C_356))),C_356) = k5_relat_1(B_355,C_356)
      | ~ v1_relat_1(k5_relat_1(B_355,C_356))
      | ~ v1_relat_1(C_356)
      | ~ v1_relat_1(B_355) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1993,c_20])).

tff(c_25043,plain,(
    ! [A_324,A_21] :
      ( k5_relat_1(k7_relat_1(k6_relat_1(A_324),k1_relat_1(k7_relat_1(k6_relat_1(A_21),A_324))),k6_relat_1(A_21)) = k5_relat_1(k6_relat_1(A_324),k6_relat_1(A_21))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(A_324),k6_relat_1(A_21)))
      | ~ v1_relat_1(k6_relat_1(A_21))
      | ~ v1_relat_1(k6_relat_1(A_324)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22237,c_24951])).

tff(c_63338,plain,(
    ! [A_600,A_601] : k5_relat_1(k7_relat_1(k6_relat_1(A_600),k3_xboole_0(A_601,A_600)),k6_relat_1(A_601)) = k7_relat_1(k6_relat_1(A_601),A_600) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_7867,c_22237,c_22237,c_302,c_25043])).

tff(c_63664,plain,(
    ! [A_601,A_78] :
      ( k5_relat_1(k6_relat_1(k3_xboole_0(A_601,A_78)),k6_relat_1(A_601)) = k7_relat_1(k6_relat_1(A_601),A_78)
      | ~ r1_tarski(k3_xboole_0(A_601,A_78),A_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_622,c_63338])).

tff(c_63782,plain,(
    ! [A_602,A_603] : k7_relat_1(k6_relat_1(A_602),k3_xboole_0(A_602,A_603)) = k7_relat_1(k6_relat_1(A_602),A_603) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_22237,c_63664])).

tff(c_63958,plain,(
    ! [A_602,A_603] :
      ( k7_relat_1(k6_relat_1(A_602),A_603) = k6_relat_1(k3_xboole_0(A_602,A_603))
      | ~ r1_tarski(k3_xboole_0(A_602,A_603),A_602) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63782,c_622])).

tff(c_64220,plain,(
    ! [A_602,A_603] : k7_relat_1(k6_relat_1(A_602),A_603) = k6_relat_1(k3_xboole_0(A_602,A_603)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_63958])).

tff(c_176,plain,(
    ! [A_50,B_51] :
      ( k5_relat_1(k6_relat_1(A_50),B_51) = k7_relat_1(B_51,A_50)
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_34,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_197,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_34])).

tff(c_219,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_197])).

tff(c_64296,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64220,c_219])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n007.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 12:04:21 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.03/11.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.03/11.63  
% 19.03/11.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.03/11.63  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 19.03/11.63  
% 19.03/11.63  %Foreground sorts:
% 19.03/11.63  
% 19.03/11.63  
% 19.03/11.63  %Background operators:
% 19.03/11.63  
% 19.03/11.63  
% 19.03/11.63  %Foreground operators:
% 19.03/11.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 19.03/11.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.03/11.63  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 19.03/11.63  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 19.03/11.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.03/11.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 19.03/11.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 19.03/11.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 19.03/11.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 19.03/11.63  tff('#skF_2', type, '#skF_2': $i).
% 19.03/11.63  tff('#skF_1', type, '#skF_1': $i).
% 19.03/11.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.03/11.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 19.03/11.63  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 19.03/11.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.03/11.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 19.03/11.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 19.03/11.63  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 19.03/11.63  
% 19.03/11.65  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 19.03/11.65  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 19.03/11.65  tff(f_81, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 19.03/11.65  tff(f_55, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 19.03/11.65  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 19.03/11.65  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 19.03/11.65  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 19.03/11.65  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 19.03/11.65  tff(f_41, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 19.03/11.65  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 19.03/11.65  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 19.03/11.65  tff(f_84, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 19.03/11.65  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 19.03/11.65  tff(c_56, plain, (![B_37, A_38]: (k3_xboole_0(B_37, A_38)=k3_xboole_0(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_27])).
% 19.03/11.65  tff(c_71, plain, (![B_37, A_38]: (r1_tarski(k3_xboole_0(B_37, A_38), A_38))), inference(superposition, [status(thm), theory('equality')], [c_56, c_4])).
% 19.03/11.65  tff(c_30, plain, (![A_30]: (v1_relat_1(k6_relat_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 19.03/11.65  tff(c_18, plain, (![A_21]: (k2_relat_1(k6_relat_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_55])).
% 19.03/11.65  tff(c_124, plain, (![A_47]: (k5_relat_1(A_47, k6_relat_1(k2_relat_1(A_47)))=A_47 | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_69])).
% 19.03/11.65  tff(c_136, plain, (![A_21]: (k5_relat_1(k6_relat_1(A_21), k6_relat_1(A_21))=k6_relat_1(A_21) | ~v1_relat_1(k6_relat_1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_124])).
% 19.03/11.65  tff(c_142, plain, (![A_21]: (k5_relat_1(k6_relat_1(A_21), k6_relat_1(A_21))=k6_relat_1(A_21))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_136])).
% 19.03/11.65  tff(c_28, plain, (![A_28, B_29]: (k5_relat_1(k6_relat_1(A_28), B_29)=k7_relat_1(B_29, A_28) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_77])).
% 19.03/11.65  tff(c_466, plain, (![A_72, B_73, C_74]: (k5_relat_1(k5_relat_1(A_72, B_73), C_74)=k5_relat_1(A_72, k5_relat_1(B_73, C_74)) | ~v1_relat_1(C_74) | ~v1_relat_1(B_73) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_51])).
% 19.03/11.65  tff(c_488, plain, (![A_28, B_29, C_74]: (k5_relat_1(k6_relat_1(A_28), k5_relat_1(B_29, C_74))=k5_relat_1(k7_relat_1(B_29, A_28), C_74) | ~v1_relat_1(C_74) | ~v1_relat_1(B_29) | ~v1_relat_1(k6_relat_1(A_28)) | ~v1_relat_1(B_29))), inference(superposition, [status(thm), theory('equality')], [c_28, c_466])).
% 19.03/11.65  tff(c_1993, plain, (![A_107, B_108, C_109]: (k5_relat_1(k6_relat_1(A_107), k5_relat_1(B_108, C_109))=k5_relat_1(k7_relat_1(B_108, A_107), C_109) | ~v1_relat_1(C_109) | ~v1_relat_1(B_108))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_488])).
% 19.03/11.65  tff(c_2069, plain, (![A_21, A_107]: (k5_relat_1(k7_relat_1(k6_relat_1(A_21), A_107), k6_relat_1(A_21))=k5_relat_1(k6_relat_1(A_107), k6_relat_1(A_21)) | ~v1_relat_1(k6_relat_1(A_21)) | ~v1_relat_1(k6_relat_1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_142, c_1993])).
% 19.03/11.65  tff(c_2098, plain, (![A_21, A_107]: (k5_relat_1(k7_relat_1(k6_relat_1(A_21), A_107), k6_relat_1(A_21))=k5_relat_1(k6_relat_1(A_107), k6_relat_1(A_21)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_2069])).
% 19.03/11.65  tff(c_22113, plain, (![B_322, C_323, A_324]: (k7_relat_1(k5_relat_1(B_322, C_323), A_324)=k5_relat_1(k7_relat_1(B_322, A_324), C_323) | ~v1_relat_1(k5_relat_1(B_322, C_323)) | ~v1_relat_1(C_323) | ~v1_relat_1(B_322))), inference(superposition, [status(thm), theory('equality')], [c_1993, c_28])).
% 19.03/11.65  tff(c_22179, plain, (![A_21, A_324]: (k7_relat_1(k5_relat_1(k6_relat_1(A_21), k6_relat_1(A_21)), A_324)=k5_relat_1(k7_relat_1(k6_relat_1(A_21), A_324), k6_relat_1(A_21)) | ~v1_relat_1(k6_relat_1(A_21)) | ~v1_relat_1(k6_relat_1(A_21)) | ~v1_relat_1(k6_relat_1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_142, c_22113])).
% 19.03/11.65  tff(c_22237, plain, (![A_324, A_21]: (k5_relat_1(k6_relat_1(A_324), k6_relat_1(A_21))=k7_relat_1(k6_relat_1(A_21), A_324))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_30, c_2098, c_142, c_22179])).
% 19.03/11.65  tff(c_355, plain, (![B_65, A_66]: (k5_relat_1(B_65, k6_relat_1(A_66))=B_65 | ~r1_tarski(k2_relat_1(B_65), A_66) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_65])).
% 19.03/11.65  tff(c_362, plain, (![A_21, A_66]: (k5_relat_1(k6_relat_1(A_21), k6_relat_1(A_66))=k6_relat_1(A_21) | ~r1_tarski(A_21, A_66) | ~v1_relat_1(k6_relat_1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_355])).
% 19.03/11.65  tff(c_572, plain, (![A_77, A_78]: (k5_relat_1(k6_relat_1(A_77), k6_relat_1(A_78))=k6_relat_1(A_77) | ~r1_tarski(A_77, A_78))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_362])).
% 19.03/11.65  tff(c_581, plain, (![A_78, A_77]: (k7_relat_1(k6_relat_1(A_78), A_77)=k6_relat_1(A_77) | ~v1_relat_1(k6_relat_1(A_78)) | ~r1_tarski(A_77, A_78))), inference(superposition, [status(thm), theory('equality')], [c_572, c_28])).
% 19.03/11.65  tff(c_622, plain, (![A_78, A_77]: (k7_relat_1(k6_relat_1(A_78), A_77)=k6_relat_1(A_77) | ~r1_tarski(A_77, A_78))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_581])).
% 19.03/11.65  tff(c_12, plain, (![A_12, B_13]: (v1_relat_1(k5_relat_1(A_12, B_13)) | ~v1_relat_1(B_13) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 19.03/11.65  tff(c_2027, plain, (![B_108, A_107, C_109]: (v1_relat_1(k5_relat_1(k7_relat_1(B_108, A_107), C_109)) | ~v1_relat_1(k5_relat_1(B_108, C_109)) | ~v1_relat_1(k6_relat_1(A_107)) | ~v1_relat_1(C_109) | ~v1_relat_1(B_108))), inference(superposition, [status(thm), theory('equality')], [c_1993, c_12])).
% 19.03/11.65  tff(c_7781, plain, (![B_196, A_197, C_198]: (v1_relat_1(k5_relat_1(k7_relat_1(B_196, A_197), C_198)) | ~v1_relat_1(k5_relat_1(B_196, C_198)) | ~v1_relat_1(C_198) | ~v1_relat_1(B_196))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2027])).
% 19.03/11.65  tff(c_7797, plain, (![A_107, A_21]: (v1_relat_1(k5_relat_1(k6_relat_1(A_107), k6_relat_1(A_21))) | ~v1_relat_1(k5_relat_1(k6_relat_1(A_21), k6_relat_1(A_21))) | ~v1_relat_1(k6_relat_1(A_21)) | ~v1_relat_1(k6_relat_1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_2098, c_7781])).
% 19.03/11.65  tff(c_7836, plain, (![A_199, A_200]: (v1_relat_1(k5_relat_1(k6_relat_1(A_199), k6_relat_1(A_200))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_30, c_142, c_7797])).
% 19.03/11.65  tff(c_7850, plain, (![A_200, A_28]: (v1_relat_1(k7_relat_1(k6_relat_1(A_200), A_28)) | ~v1_relat_1(k6_relat_1(A_200)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_7836])).
% 19.03/11.65  tff(c_7867, plain, (![A_200, A_28]: (v1_relat_1(k7_relat_1(k6_relat_1(A_200), A_28)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_7850])).
% 19.03/11.65  tff(c_16, plain, (![A_21]: (k1_relat_1(k6_relat_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_55])).
% 19.03/11.65  tff(c_269, plain, (![B_59, A_60]: (k3_xboole_0(k1_relat_1(B_59), A_60)=k1_relat_1(k7_relat_1(B_59, A_60)) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_73])).
% 19.03/11.65  tff(c_298, plain, (![A_21, A_60]: (k1_relat_1(k7_relat_1(k6_relat_1(A_21), A_60))=k3_xboole_0(A_21, A_60) | ~v1_relat_1(k6_relat_1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_269])).
% 19.03/11.65  tff(c_302, plain, (![A_21, A_60]: (k1_relat_1(k7_relat_1(k6_relat_1(A_21), A_60))=k3_xboole_0(A_21, A_60))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_298])).
% 19.03/11.65  tff(c_20, plain, (![A_22]: (k5_relat_1(k6_relat_1(k1_relat_1(A_22)), A_22)=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_59])).
% 19.03/11.65  tff(c_24951, plain, (![B_355, C_356]: (k5_relat_1(k7_relat_1(B_355, k1_relat_1(k5_relat_1(B_355, C_356))), C_356)=k5_relat_1(B_355, C_356) | ~v1_relat_1(k5_relat_1(B_355, C_356)) | ~v1_relat_1(C_356) | ~v1_relat_1(B_355))), inference(superposition, [status(thm), theory('equality')], [c_1993, c_20])).
% 19.03/11.65  tff(c_25043, plain, (![A_324, A_21]: (k5_relat_1(k7_relat_1(k6_relat_1(A_324), k1_relat_1(k7_relat_1(k6_relat_1(A_21), A_324))), k6_relat_1(A_21))=k5_relat_1(k6_relat_1(A_324), k6_relat_1(A_21)) | ~v1_relat_1(k5_relat_1(k6_relat_1(A_324), k6_relat_1(A_21))) | ~v1_relat_1(k6_relat_1(A_21)) | ~v1_relat_1(k6_relat_1(A_324)))), inference(superposition, [status(thm), theory('equality')], [c_22237, c_24951])).
% 19.03/11.65  tff(c_63338, plain, (![A_600, A_601]: (k5_relat_1(k7_relat_1(k6_relat_1(A_600), k3_xboole_0(A_601, A_600)), k6_relat_1(A_601))=k7_relat_1(k6_relat_1(A_601), A_600))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_7867, c_22237, c_22237, c_302, c_25043])).
% 19.03/11.65  tff(c_63664, plain, (![A_601, A_78]: (k5_relat_1(k6_relat_1(k3_xboole_0(A_601, A_78)), k6_relat_1(A_601))=k7_relat_1(k6_relat_1(A_601), A_78) | ~r1_tarski(k3_xboole_0(A_601, A_78), A_78))), inference(superposition, [status(thm), theory('equality')], [c_622, c_63338])).
% 19.03/11.65  tff(c_63782, plain, (![A_602, A_603]: (k7_relat_1(k6_relat_1(A_602), k3_xboole_0(A_602, A_603))=k7_relat_1(k6_relat_1(A_602), A_603))), inference(demodulation, [status(thm), theory('equality')], [c_71, c_22237, c_63664])).
% 19.03/11.65  tff(c_63958, plain, (![A_602, A_603]: (k7_relat_1(k6_relat_1(A_602), A_603)=k6_relat_1(k3_xboole_0(A_602, A_603)) | ~r1_tarski(k3_xboole_0(A_602, A_603), A_602))), inference(superposition, [status(thm), theory('equality')], [c_63782, c_622])).
% 19.03/11.65  tff(c_64220, plain, (![A_602, A_603]: (k7_relat_1(k6_relat_1(A_602), A_603)=k6_relat_1(k3_xboole_0(A_602, A_603)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_63958])).
% 19.03/11.65  tff(c_176, plain, (![A_50, B_51]: (k5_relat_1(k6_relat_1(A_50), B_51)=k7_relat_1(B_51, A_50) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_77])).
% 19.03/11.65  tff(c_34, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 19.03/11.65  tff(c_197, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_176, c_34])).
% 19.03/11.65  tff(c_219, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_197])).
% 19.03/11.65  tff(c_64296, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64220, c_219])).
% 19.03/11.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.03/11.65  
% 19.03/11.65  Inference rules
% 19.03/11.65  ----------------------
% 19.03/11.65  #Ref     : 0
% 19.03/11.65  #Sup     : 16008
% 19.03/11.65  #Fact    : 0
% 19.03/11.65  #Define  : 0
% 19.03/11.65  #Split   : 1
% 19.03/11.65  #Chain   : 0
% 19.03/11.65  #Close   : 0
% 19.03/11.65  
% 19.03/11.65  Ordering : KBO
% 19.03/11.65  
% 19.03/11.65  Simplification rules
% 19.03/11.65  ----------------------
% 19.03/11.65  #Subsume      : 2491
% 19.03/11.65  #Demod        : 18097
% 19.03/11.65  #Tautology    : 3891
% 19.03/11.65  #SimpNegUnit  : 0
% 19.03/11.65  #BackRed      : 39
% 19.03/11.65  
% 19.03/11.65  #Partial instantiations: 0
% 19.03/11.65  #Strategies tried      : 1
% 19.03/11.65  
% 19.03/11.65  Timing (in seconds)
% 19.03/11.65  ----------------------
% 19.03/11.65  Preprocessing        : 0.31
% 19.03/11.65  Parsing              : 0.16
% 19.03/11.65  CNF conversion       : 0.02
% 19.03/11.65  Main loop            : 10.59
% 19.03/11.65  Inferencing          : 1.70
% 19.03/11.65  Reduction            : 5.92
% 19.03/11.65  Demodulation         : 5.38
% 19.03/11.65  BG Simplification    : 0.29
% 19.03/11.65  Subsumption          : 2.24
% 19.03/11.65  Abstraction          : 0.50
% 19.03/11.65  MUC search           : 0.00
% 19.03/11.65  Cooper               : 0.00
% 19.03/11.66  Total                : 10.94
% 19.03/11.66  Index Insertion      : 0.00
% 19.03/11.66  Index Deletion       : 0.00
% 19.03/11.66  Index Matching       : 0.00
% 19.03/11.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
