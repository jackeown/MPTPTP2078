%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:00 EST 2020

% Result     : Theorem 13.33s
% Output     : CNFRefutation 13.44s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 342 expanded)
%              Number of leaves         :   30 ( 126 expanded)
%              Depth                    :   12
%              Number of atoms          :  173 ( 611 expanded)
%              Number of equality atoms :   30 ( 176 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_52,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_40,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_relat_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_44,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_32,plain,(
    ! [A_21,B_22] :
      ( v1_relat_1(k7_relat_1(A_21,B_22))
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10182,plain,(
    ! [A_537,B_538,C_539] :
      ( r2_hidden('#skF_1'(A_537,B_538,C_539),B_538)
      | r2_hidden('#skF_2'(A_537,B_538,C_539),C_539)
      | k3_xboole_0(A_537,B_538) = C_539 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10219,plain,(
    ! [A_537,B_538] :
      ( r2_hidden('#skF_2'(A_537,B_538,B_538),B_538)
      | k3_xboole_0(A_537,B_538) = B_538 ) ),
    inference(resolution,[status(thm)],[c_10182,c_14])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10262,plain,(
    ! [A_546,B_547,C_548] :
      ( r2_hidden('#skF_1'(A_546,B_547,C_548),B_547)
      | ~ r2_hidden('#skF_2'(A_546,B_547,C_548),B_547)
      | ~ r2_hidden('#skF_2'(A_546,B_547,C_548),A_546)
      | k3_xboole_0(A_546,B_547) = C_548 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10437,plain,(
    ! [C_555,B_556] :
      ( ~ r2_hidden('#skF_2'(C_555,B_556,C_555),B_556)
      | r2_hidden('#skF_1'(C_555,B_556,C_555),B_556)
      | k3_xboole_0(C_555,B_556) = C_555 ) ),
    inference(resolution,[status(thm)],[c_16,c_10262])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10467,plain,(
    ! [B_557] :
      ( ~ r2_hidden('#skF_2'(B_557,B_557,B_557),B_557)
      | k3_xboole_0(B_557,B_557) = B_557 ) ),
    inference(resolution,[status(thm)],[c_10437,c_8])).

tff(c_10505,plain,(
    ! [B_561] : k3_xboole_0(B_561,B_561) = B_561 ),
    inference(resolution,[status(thm)],[c_10219,c_10467])).

tff(c_26,plain,(
    ! [B_16,A_15] : k2_tarski(B_16,A_15) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_89,plain,(
    ! [A_39,B_40] : k1_setfam_1(k2_tarski(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_104,plain,(
    ! [B_41,A_42] : k1_setfam_1(k2_tarski(B_41,A_42)) = k3_xboole_0(A_42,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_89])).

tff(c_30,plain,(
    ! [A_19,B_20] : k1_setfam_1(k2_tarski(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_127,plain,(
    ! [B_43,A_44] : k3_xboole_0(B_43,A_44) = k3_xboole_0(A_44,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_30])).

tff(c_22,plain,(
    ! [A_10,B_11] : r1_tarski(k3_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_142,plain,(
    ! [B_43,A_44] : r1_tarski(k3_xboole_0(B_43,A_44),A_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_22])).

tff(c_10555,plain,(
    ! [B_561] : r1_tarski(B_561,B_561) ),
    inference(superposition,[status(thm),theory(equality)],[c_10505,c_142])).

tff(c_110,plain,(
    ! [B_41,A_42] : k3_xboole_0(B_41,A_42) = k3_xboole_0(A_42,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_30])).

tff(c_249,plain,(
    ! [C_71,A_72,B_73] :
      ( k3_xboole_0(k7_relat_1(C_71,A_72),k7_relat_1(C_71,B_73)) = k7_relat_1(C_71,k3_xboole_0(A_72,B_73))
      | ~ v1_relat_1(C_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_20,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_tarski(k3_xboole_0(A_7,C_9),B_8)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10054,plain,(
    ! [C_521,A_522,B_523,B_524] :
      ( r1_tarski(k7_relat_1(C_521,k3_xboole_0(A_522,B_523)),B_524)
      | ~ r1_tarski(k7_relat_1(C_521,A_522),B_524)
      | ~ v1_relat_1(C_521) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_20])).

tff(c_10060,plain,(
    ! [C_521,B_41,A_42,B_524] :
      ( r1_tarski(k7_relat_1(C_521,k3_xboole_0(B_41,A_42)),B_524)
      | ~ r1_tarski(k7_relat_1(C_521,A_42),B_524)
      | ~ v1_relat_1(C_521) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_10054])).

tff(c_36,plain,(
    ! [B_27,A_26] :
      ( k2_relat_1(k7_relat_1(B_27,A_26)) = k9_relat_1(B_27,A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_241,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(k2_relat_1(A_67),k2_relat_1(B_68))
      | ~ r1_tarski(A_67,B_68)
      | ~ v1_relat_1(B_68)
      | ~ v1_relat_1(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_11084,plain,(
    ! [A_598,B_599,A_600] :
      ( r1_tarski(k2_relat_1(A_598),k9_relat_1(B_599,A_600))
      | ~ r1_tarski(A_598,k7_relat_1(B_599,A_600))
      | ~ v1_relat_1(k7_relat_1(B_599,A_600))
      | ~ v1_relat_1(A_598)
      | ~ v1_relat_1(B_599) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_241])).

tff(c_19481,plain,(
    ! [B_932,A_933,B_934,A_935] :
      ( r1_tarski(k9_relat_1(B_932,A_933),k9_relat_1(B_934,A_935))
      | ~ r1_tarski(k7_relat_1(B_932,A_933),k7_relat_1(B_934,A_935))
      | ~ v1_relat_1(k7_relat_1(B_934,A_935))
      | ~ v1_relat_1(k7_relat_1(B_932,A_933))
      | ~ v1_relat_1(B_934)
      | ~ v1_relat_1(B_932) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_11084])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_506,plain,(
    ! [A_105,B_106,C_107] :
      ( ~ r2_hidden('#skF_1'(A_105,B_106,C_107),C_107)
      | r2_hidden('#skF_2'(A_105,B_106,C_107),C_107)
      | k3_xboole_0(A_105,B_106) = C_107 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_520,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_2'(A_1,B_2,A_1),A_1)
      | k3_xboole_0(A_1,B_2) = A_1 ) ),
    inference(resolution,[status(thm)],[c_18,c_506])).

tff(c_709,plain,(
    ! [A_115,B_116,C_117] :
      ( r2_hidden('#skF_1'(A_115,B_116,C_117),B_116)
      | ~ r2_hidden('#skF_2'(A_115,B_116,C_117),B_116)
      | ~ r2_hidden('#skF_2'(A_115,B_116,C_117),A_115)
      | k3_xboole_0(A_115,B_116) = C_117 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_724,plain,(
    ! [C_3,B_2] :
      ( ~ r2_hidden('#skF_2'(C_3,B_2,C_3),B_2)
      | r2_hidden('#skF_1'(C_3,B_2,C_3),B_2)
      | k3_xboole_0(C_3,B_2) = C_3 ) ),
    inference(resolution,[status(thm)],[c_16,c_709])).

tff(c_752,plain,(
    ! [A_120,B_121,C_122] :
      ( ~ r2_hidden('#skF_1'(A_120,B_121,C_122),C_122)
      | ~ r2_hidden('#skF_2'(A_120,B_121,C_122),B_121)
      | ~ r2_hidden('#skF_2'(A_120,B_121,C_122),A_120)
      | k3_xboole_0(A_120,B_121) = C_122 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_769,plain,(
    ! [B_123] :
      ( ~ r2_hidden('#skF_2'(B_123,B_123,B_123),B_123)
      | k3_xboole_0(B_123,B_123) = B_123 ) ),
    inference(resolution,[status(thm)],[c_724,c_752])).

tff(c_790,plain,(
    ! [B_124] : k3_xboole_0(B_124,B_124) = B_124 ),
    inference(resolution,[status(thm)],[c_520,c_769])).

tff(c_840,plain,(
    ! [B_124] : r1_tarski(B_124,B_124) ),
    inference(superposition,[status(thm),theory(equality)],[c_790,c_142])).

tff(c_270,plain,(
    ! [C_71,A_72,B_73,B_8] :
      ( r1_tarski(k7_relat_1(C_71,k3_xboole_0(A_72,B_73)),B_8)
      | ~ r1_tarski(k7_relat_1(C_71,A_72),B_8)
      | ~ v1_relat_1(C_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_20])).

tff(c_916,plain,(
    ! [B_131,A_132,B_133] :
      ( r1_tarski(k9_relat_1(B_131,A_132),k2_relat_1(B_133))
      | ~ r1_tarski(k7_relat_1(B_131,A_132),B_133)
      | ~ v1_relat_1(B_133)
      | ~ v1_relat_1(k7_relat_1(B_131,A_132))
      | ~ v1_relat_1(B_131) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_241])).

tff(c_9956,plain,(
    ! [B_510,A_511,B_512,A_513] :
      ( r1_tarski(k9_relat_1(B_510,A_511),k9_relat_1(B_512,A_513))
      | ~ r1_tarski(k7_relat_1(B_510,A_511),k7_relat_1(B_512,A_513))
      | ~ v1_relat_1(k7_relat_1(B_512,A_513))
      | ~ v1_relat_1(k7_relat_1(B_510,A_511))
      | ~ v1_relat_1(B_510)
      | ~ v1_relat_1(B_512) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_916])).

tff(c_230,plain,(
    ! [A_64,B_65,C_66] :
      ( r1_tarski(A_64,k3_xboole_0(B_65,C_66))
      | ~ r1_tarski(A_64,C_66)
      | ~ r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_42,plain,(
    ~ r1_tarski(k9_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')),k3_xboole_0(k9_relat_1('#skF_5','#skF_3'),k9_relat_1('#skF_5','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_175,plain,(
    ~ r1_tarski(k9_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')),k3_xboole_0(k9_relat_1('#skF_5','#skF_4'),k9_relat_1('#skF_5','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_110,c_42])).

tff(c_240,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')),k9_relat_1('#skF_5','#skF_3'))
    | ~ r1_tarski(k9_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')),k9_relat_1('#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_230,c_175])).

tff(c_314,plain,(
    ~ r1_tarski(k9_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')),k9_relat_1('#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_240])).

tff(c_9959,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')),k7_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_9956,c_314])).

tff(c_9974,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')),k7_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_9959])).

tff(c_9975,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_9974])).

tff(c_9978,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_9975])).

tff(c_9982,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_9978])).

tff(c_9983,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_5','#skF_4'))
    | ~ r1_tarski(k7_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')),k7_relat_1('#skF_5','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_9974])).

tff(c_9985,plain,(
    ~ r1_tarski(k7_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')),k7_relat_1('#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_9983])).

tff(c_9991,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_5','#skF_4'),k7_relat_1('#skF_5','#skF_4'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_270,c_9985])).

tff(c_10001,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_840,c_9991])).

tff(c_10002,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_5','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_9983])).

tff(c_10006,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_10002])).

tff(c_10010,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_10006])).

tff(c_10011,plain,(
    ~ r1_tarski(k9_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')),k9_relat_1('#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_240])).

tff(c_19484,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')),k7_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_19481,c_10011])).

tff(c_19499,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')),k7_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1(k7_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_19484])).

tff(c_19500,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_19499])).

tff(c_19503,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_19500])).

tff(c_19507,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_19503])).

tff(c_19508,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_5','#skF_3'))
    | ~ r1_tarski(k7_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')),k7_relat_1('#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_19499])).

tff(c_19510,plain,(
    ~ r1_tarski(k7_relat_1('#skF_5',k3_xboole_0('#skF_4','#skF_3')),k7_relat_1('#skF_5','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_19508])).

tff(c_19513,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_5','#skF_3'),k7_relat_1('#skF_5','#skF_3'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10060,c_19510])).

tff(c_19523,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_10555,c_19513])).

tff(c_19524,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_5','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_19508])).

tff(c_19528,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_19524])).

tff(c_19532,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_19528])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:32:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.33/4.98  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.33/4.99  
% 13.33/4.99  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.33/4.99  %$ r2_hidden > r1_tarski > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 13.33/4.99  
% 13.33/4.99  %Foreground sorts:
% 13.33/4.99  
% 13.33/4.99  
% 13.33/4.99  %Background operators:
% 13.33/4.99  
% 13.33/4.99  
% 13.33/4.99  %Foreground operators:
% 13.33/4.99  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 13.33/4.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.33/4.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.33/4.99  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 13.33/4.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.33/4.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.33/4.99  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.33/4.99  tff('#skF_5', type, '#skF_5': $i).
% 13.33/4.99  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.33/4.99  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 13.33/4.99  tff('#skF_3', type, '#skF_3': $i).
% 13.33/4.99  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 13.33/4.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.33/4.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.33/4.99  tff('#skF_4', type, '#skF_4': $i).
% 13.33/4.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.33/4.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.33/4.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.33/4.99  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 13.33/4.99  
% 13.44/5.01  tff(f_80, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_relat_1)).
% 13.44/5.01  tff(f_56, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 13.44/5.01  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 13.44/5.01  tff(f_48, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 13.44/5.01  tff(f_52, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 13.44/5.01  tff(f_40, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 13.44/5.01  tff(f_60, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_relat_1)).
% 13.44/5.01  tff(f_38, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 13.44/5.01  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 13.44/5.01  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 13.44/5.01  tff(f_46, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 13.44/5.01  tff(c_44, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 13.44/5.01  tff(c_32, plain, (![A_21, B_22]: (v1_relat_1(k7_relat_1(A_21, B_22)) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_56])).
% 13.44/5.01  tff(c_10182, plain, (![A_537, B_538, C_539]: (r2_hidden('#skF_1'(A_537, B_538, C_539), B_538) | r2_hidden('#skF_2'(A_537, B_538, C_539), C_539) | k3_xboole_0(A_537, B_538)=C_539)), inference(cnfTransformation, [status(thm)], [f_34])).
% 13.44/5.01  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 13.44/5.01  tff(c_10219, plain, (![A_537, B_538]: (r2_hidden('#skF_2'(A_537, B_538, B_538), B_538) | k3_xboole_0(A_537, B_538)=B_538)), inference(resolution, [status(thm)], [c_10182, c_14])).
% 13.44/5.01  tff(c_16, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 13.44/5.01  tff(c_10262, plain, (![A_546, B_547, C_548]: (r2_hidden('#skF_1'(A_546, B_547, C_548), B_547) | ~r2_hidden('#skF_2'(A_546, B_547, C_548), B_547) | ~r2_hidden('#skF_2'(A_546, B_547, C_548), A_546) | k3_xboole_0(A_546, B_547)=C_548)), inference(cnfTransformation, [status(thm)], [f_34])).
% 13.44/5.01  tff(c_10437, plain, (![C_555, B_556]: (~r2_hidden('#skF_2'(C_555, B_556, C_555), B_556) | r2_hidden('#skF_1'(C_555, B_556, C_555), B_556) | k3_xboole_0(C_555, B_556)=C_555)), inference(resolution, [status(thm)], [c_16, c_10262])).
% 13.44/5.01  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 13.44/5.01  tff(c_10467, plain, (![B_557]: (~r2_hidden('#skF_2'(B_557, B_557, B_557), B_557) | k3_xboole_0(B_557, B_557)=B_557)), inference(resolution, [status(thm)], [c_10437, c_8])).
% 13.44/5.01  tff(c_10505, plain, (![B_561]: (k3_xboole_0(B_561, B_561)=B_561)), inference(resolution, [status(thm)], [c_10219, c_10467])).
% 13.44/5.01  tff(c_26, plain, (![B_16, A_15]: (k2_tarski(B_16, A_15)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_48])).
% 13.44/5.01  tff(c_89, plain, (![A_39, B_40]: (k1_setfam_1(k2_tarski(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_52])).
% 13.44/5.01  tff(c_104, plain, (![B_41, A_42]: (k1_setfam_1(k2_tarski(B_41, A_42))=k3_xboole_0(A_42, B_41))), inference(superposition, [status(thm), theory('equality')], [c_26, c_89])).
% 13.44/5.01  tff(c_30, plain, (![A_19, B_20]: (k1_setfam_1(k2_tarski(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_52])).
% 13.44/5.01  tff(c_127, plain, (![B_43, A_44]: (k3_xboole_0(B_43, A_44)=k3_xboole_0(A_44, B_43))), inference(superposition, [status(thm), theory('equality')], [c_104, c_30])).
% 13.44/5.01  tff(c_22, plain, (![A_10, B_11]: (r1_tarski(k3_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 13.44/5.01  tff(c_142, plain, (![B_43, A_44]: (r1_tarski(k3_xboole_0(B_43, A_44), A_44))), inference(superposition, [status(thm), theory('equality')], [c_127, c_22])).
% 13.44/5.01  tff(c_10555, plain, (![B_561]: (r1_tarski(B_561, B_561))), inference(superposition, [status(thm), theory('equality')], [c_10505, c_142])).
% 13.44/5.01  tff(c_110, plain, (![B_41, A_42]: (k3_xboole_0(B_41, A_42)=k3_xboole_0(A_42, B_41))), inference(superposition, [status(thm), theory('equality')], [c_104, c_30])).
% 13.44/5.01  tff(c_249, plain, (![C_71, A_72, B_73]: (k3_xboole_0(k7_relat_1(C_71, A_72), k7_relat_1(C_71, B_73))=k7_relat_1(C_71, k3_xboole_0(A_72, B_73)) | ~v1_relat_1(C_71))), inference(cnfTransformation, [status(thm)], [f_60])).
% 13.44/5.01  tff(c_20, plain, (![A_7, C_9, B_8]: (r1_tarski(k3_xboole_0(A_7, C_9), B_8) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.44/5.01  tff(c_10054, plain, (![C_521, A_522, B_523, B_524]: (r1_tarski(k7_relat_1(C_521, k3_xboole_0(A_522, B_523)), B_524) | ~r1_tarski(k7_relat_1(C_521, A_522), B_524) | ~v1_relat_1(C_521))), inference(superposition, [status(thm), theory('equality')], [c_249, c_20])).
% 13.44/5.01  tff(c_10060, plain, (![C_521, B_41, A_42, B_524]: (r1_tarski(k7_relat_1(C_521, k3_xboole_0(B_41, A_42)), B_524) | ~r1_tarski(k7_relat_1(C_521, A_42), B_524) | ~v1_relat_1(C_521))), inference(superposition, [status(thm), theory('equality')], [c_110, c_10054])).
% 13.44/5.01  tff(c_36, plain, (![B_27, A_26]: (k2_relat_1(k7_relat_1(B_27, A_26))=k9_relat_1(B_27, A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.44/5.01  tff(c_241, plain, (![A_67, B_68]: (r1_tarski(k2_relat_1(A_67), k2_relat_1(B_68)) | ~r1_tarski(A_67, B_68) | ~v1_relat_1(B_68) | ~v1_relat_1(A_67))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.44/5.01  tff(c_11084, plain, (![A_598, B_599, A_600]: (r1_tarski(k2_relat_1(A_598), k9_relat_1(B_599, A_600)) | ~r1_tarski(A_598, k7_relat_1(B_599, A_600)) | ~v1_relat_1(k7_relat_1(B_599, A_600)) | ~v1_relat_1(A_598) | ~v1_relat_1(B_599))), inference(superposition, [status(thm), theory('equality')], [c_36, c_241])).
% 13.44/5.01  tff(c_19481, plain, (![B_932, A_933, B_934, A_935]: (r1_tarski(k9_relat_1(B_932, A_933), k9_relat_1(B_934, A_935)) | ~r1_tarski(k7_relat_1(B_932, A_933), k7_relat_1(B_934, A_935)) | ~v1_relat_1(k7_relat_1(B_934, A_935)) | ~v1_relat_1(k7_relat_1(B_932, A_933)) | ~v1_relat_1(B_934) | ~v1_relat_1(B_932))), inference(superposition, [status(thm), theory('equality')], [c_36, c_11084])).
% 13.44/5.01  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 13.44/5.01  tff(c_506, plain, (![A_105, B_106, C_107]: (~r2_hidden('#skF_1'(A_105, B_106, C_107), C_107) | r2_hidden('#skF_2'(A_105, B_106, C_107), C_107) | k3_xboole_0(A_105, B_106)=C_107)), inference(cnfTransformation, [status(thm)], [f_34])).
% 13.44/5.01  tff(c_520, plain, (![A_1, B_2]: (r2_hidden('#skF_2'(A_1, B_2, A_1), A_1) | k3_xboole_0(A_1, B_2)=A_1)), inference(resolution, [status(thm)], [c_18, c_506])).
% 13.44/5.01  tff(c_709, plain, (![A_115, B_116, C_117]: (r2_hidden('#skF_1'(A_115, B_116, C_117), B_116) | ~r2_hidden('#skF_2'(A_115, B_116, C_117), B_116) | ~r2_hidden('#skF_2'(A_115, B_116, C_117), A_115) | k3_xboole_0(A_115, B_116)=C_117)), inference(cnfTransformation, [status(thm)], [f_34])).
% 13.44/5.01  tff(c_724, plain, (![C_3, B_2]: (~r2_hidden('#skF_2'(C_3, B_2, C_3), B_2) | r2_hidden('#skF_1'(C_3, B_2, C_3), B_2) | k3_xboole_0(C_3, B_2)=C_3)), inference(resolution, [status(thm)], [c_16, c_709])).
% 13.44/5.01  tff(c_752, plain, (![A_120, B_121, C_122]: (~r2_hidden('#skF_1'(A_120, B_121, C_122), C_122) | ~r2_hidden('#skF_2'(A_120, B_121, C_122), B_121) | ~r2_hidden('#skF_2'(A_120, B_121, C_122), A_120) | k3_xboole_0(A_120, B_121)=C_122)), inference(cnfTransformation, [status(thm)], [f_34])).
% 13.44/5.01  tff(c_769, plain, (![B_123]: (~r2_hidden('#skF_2'(B_123, B_123, B_123), B_123) | k3_xboole_0(B_123, B_123)=B_123)), inference(resolution, [status(thm)], [c_724, c_752])).
% 13.44/5.01  tff(c_790, plain, (![B_124]: (k3_xboole_0(B_124, B_124)=B_124)), inference(resolution, [status(thm)], [c_520, c_769])).
% 13.44/5.01  tff(c_840, plain, (![B_124]: (r1_tarski(B_124, B_124))), inference(superposition, [status(thm), theory('equality')], [c_790, c_142])).
% 13.44/5.01  tff(c_270, plain, (![C_71, A_72, B_73, B_8]: (r1_tarski(k7_relat_1(C_71, k3_xboole_0(A_72, B_73)), B_8) | ~r1_tarski(k7_relat_1(C_71, A_72), B_8) | ~v1_relat_1(C_71))), inference(superposition, [status(thm), theory('equality')], [c_249, c_20])).
% 13.44/5.01  tff(c_916, plain, (![B_131, A_132, B_133]: (r1_tarski(k9_relat_1(B_131, A_132), k2_relat_1(B_133)) | ~r1_tarski(k7_relat_1(B_131, A_132), B_133) | ~v1_relat_1(B_133) | ~v1_relat_1(k7_relat_1(B_131, A_132)) | ~v1_relat_1(B_131))), inference(superposition, [status(thm), theory('equality')], [c_36, c_241])).
% 13.44/5.01  tff(c_9956, plain, (![B_510, A_511, B_512, A_513]: (r1_tarski(k9_relat_1(B_510, A_511), k9_relat_1(B_512, A_513)) | ~r1_tarski(k7_relat_1(B_510, A_511), k7_relat_1(B_512, A_513)) | ~v1_relat_1(k7_relat_1(B_512, A_513)) | ~v1_relat_1(k7_relat_1(B_510, A_511)) | ~v1_relat_1(B_510) | ~v1_relat_1(B_512))), inference(superposition, [status(thm), theory('equality')], [c_36, c_916])).
% 13.44/5.01  tff(c_230, plain, (![A_64, B_65, C_66]: (r1_tarski(A_64, k3_xboole_0(B_65, C_66)) | ~r1_tarski(A_64, C_66) | ~r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_46])).
% 13.44/5.01  tff(c_42, plain, (~r1_tarski(k9_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4')), k3_xboole_0(k9_relat_1('#skF_5', '#skF_3'), k9_relat_1('#skF_5', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 13.44/5.01  tff(c_175, plain, (~r1_tarski(k9_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3')), k3_xboole_0(k9_relat_1('#skF_5', '#skF_4'), k9_relat_1('#skF_5', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_110, c_42])).
% 13.44/5.01  tff(c_240, plain, (~r1_tarski(k9_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3')), k9_relat_1('#skF_5', '#skF_3')) | ~r1_tarski(k9_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3')), k9_relat_1('#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_230, c_175])).
% 13.44/5.01  tff(c_314, plain, (~r1_tarski(k9_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3')), k9_relat_1('#skF_5', '#skF_4'))), inference(splitLeft, [status(thm)], [c_240])).
% 13.44/5.01  tff(c_9959, plain, (~r1_tarski(k7_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3')), k7_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3'))) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_9956, c_314])).
% 13.44/5.01  tff(c_9974, plain, (~r1_tarski(k7_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3')), k7_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_9959])).
% 13.44/5.01  tff(c_9975, plain, (~v1_relat_1(k7_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_9974])).
% 13.44/5.01  tff(c_9978, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_9975])).
% 13.44/5.01  tff(c_9982, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_9978])).
% 13.44/5.01  tff(c_9983, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_4')) | ~r1_tarski(k7_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3')), k7_relat_1('#skF_5', '#skF_4'))), inference(splitRight, [status(thm)], [c_9974])).
% 13.44/5.01  tff(c_9985, plain, (~r1_tarski(k7_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3')), k7_relat_1('#skF_5', '#skF_4'))), inference(splitLeft, [status(thm)], [c_9983])).
% 13.44/5.01  tff(c_9991, plain, (~r1_tarski(k7_relat_1('#skF_5', '#skF_4'), k7_relat_1('#skF_5', '#skF_4')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_270, c_9985])).
% 13.44/5.01  tff(c_10001, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_840, c_9991])).
% 13.44/5.01  tff(c_10002, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_4'))), inference(splitRight, [status(thm)], [c_9983])).
% 13.44/5.01  tff(c_10006, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_10002])).
% 13.44/5.01  tff(c_10010, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_10006])).
% 13.44/5.01  tff(c_10011, plain, (~r1_tarski(k9_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3')), k9_relat_1('#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_240])).
% 13.44/5.01  tff(c_19484, plain, (~r1_tarski(k7_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3')), k7_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3'))) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_19481, c_10011])).
% 13.44/5.01  tff(c_19499, plain, (~r1_tarski(k7_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3')), k7_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1(k7_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_19484])).
% 13.44/5.01  tff(c_19500, plain, (~v1_relat_1(k7_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3')))), inference(splitLeft, [status(thm)], [c_19499])).
% 13.44/5.01  tff(c_19503, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_19500])).
% 13.44/5.01  tff(c_19507, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_19503])).
% 13.44/5.01  tff(c_19508, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_3')) | ~r1_tarski(k7_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3')), k7_relat_1('#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_19499])).
% 13.44/5.01  tff(c_19510, plain, (~r1_tarski(k7_relat_1('#skF_5', k3_xboole_0('#skF_4', '#skF_3')), k7_relat_1('#skF_5', '#skF_3'))), inference(splitLeft, [status(thm)], [c_19508])).
% 13.44/5.01  tff(c_19513, plain, (~r1_tarski(k7_relat_1('#skF_5', '#skF_3'), k7_relat_1('#skF_5', '#skF_3')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_10060, c_19510])).
% 13.44/5.01  tff(c_19523, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_10555, c_19513])).
% 13.44/5.01  tff(c_19524, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_3'))), inference(splitRight, [status(thm)], [c_19508])).
% 13.44/5.01  tff(c_19528, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_19524])).
% 13.44/5.01  tff(c_19532, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_19528])).
% 13.44/5.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.44/5.01  
% 13.44/5.01  Inference rules
% 13.44/5.01  ----------------------
% 13.44/5.01  #Ref     : 0
% 13.44/5.01  #Sup     : 4602
% 13.44/5.01  #Fact    : 0
% 13.44/5.01  #Define  : 0
% 13.44/5.01  #Split   : 5
% 13.44/5.01  #Chain   : 0
% 13.44/5.01  #Close   : 0
% 13.44/5.01  
% 13.44/5.01  Ordering : KBO
% 13.44/5.01  
% 13.44/5.01  Simplification rules
% 13.44/5.01  ----------------------
% 13.44/5.01  #Subsume      : 1204
% 13.44/5.01  #Demod        : 1569
% 13.44/5.01  #Tautology    : 373
% 13.44/5.01  #SimpNegUnit  : 0
% 13.44/5.01  #BackRed      : 0
% 13.44/5.01  
% 13.44/5.01  #Partial instantiations: 0
% 13.44/5.01  #Strategies tried      : 1
% 13.44/5.01  
% 13.44/5.01  Timing (in seconds)
% 13.44/5.01  ----------------------
% 13.44/5.02  Preprocessing        : 0.31
% 13.44/5.02  Parsing              : 0.17
% 13.44/5.02  CNF conversion       : 0.02
% 13.44/5.02  Main loop            : 3.92
% 13.44/5.02  Inferencing          : 1.05
% 13.44/5.02  Reduction            : 1.16
% 13.44/5.02  Demodulation         : 0.97
% 13.44/5.02  BG Simplification    : 0.14
% 13.44/5.02  Subsumption          : 1.35
% 13.44/5.02  Abstraction          : 0.21
% 13.44/5.02  MUC search           : 0.00
% 13.44/5.02  Cooper               : 0.00
% 13.44/5.02  Total                : 4.27
% 13.44/5.02  Index Insertion      : 0.00
% 13.44/5.02  Index Deletion       : 0.00
% 13.44/5.02  Index Matching       : 0.00
% 13.44/5.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
