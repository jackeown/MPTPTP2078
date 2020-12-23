%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:11 EST 2020

% Result     : Theorem 29.92s
% Output     : CNFRefutation 29.92s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 201 expanded)
%              Number of leaves         :   29 (  81 expanded)
%              Depth                    :   16
%              Number of atoms          :  109 ( 305 expanded)
%              Number of equality atoms :   46 ( 142 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B,C] :
            ( r1_tarski(B,C)
           => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_45,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_16,plain,(
    ! [A_13] : v1_relat_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    ! [A_23] : k1_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_329,plain,(
    ! [B_66,A_67] :
      ( k3_xboole_0(k1_relat_1(B_66),A_67) = k1_relat_1(k7_relat_1(B_66,A_67))
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_338,plain,(
    ! [A_23,A_67] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_23),A_67)) = k3_xboole_0(A_23,A_67)
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_329])).

tff(c_343,plain,(
    ! [A_68,A_69] : k1_relat_1(k7_relat_1(k6_relat_1(A_68),A_69)) = k3_xboole_0(A_68,A_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_338])).

tff(c_30,plain,(
    ! [B_25,A_24] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_25,A_24)),A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_359,plain,(
    ! [A_68,A_69] :
      ( r1_tarski(k3_xboole_0(A_68,A_69),A_69)
      | ~ v1_relat_1(k6_relat_1(A_68)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_30])).

tff(c_380,plain,(
    ! [A_68,A_69] : r1_tarski(k3_xboole_0(A_68,A_69),A_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_359])).

tff(c_247,plain,(
    ! [B_62,A_63] :
      ( k7_relat_1(B_62,A_63) = B_62
      | ~ r1_tarski(k1_relat_1(B_62),A_63)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_256,plain,(
    ! [A_23,A_63] :
      ( k7_relat_1(k6_relat_1(A_23),A_63) = k6_relat_1(A_23)
      | ~ r1_tarski(A_23,A_63)
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_247])).

tff(c_264,plain,(
    ! [A_23,A_63] :
      ( k7_relat_1(k6_relat_1(A_23),A_63) = k6_relat_1(A_23)
      | ~ r1_tarski(A_23,A_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_256])).

tff(c_368,plain,(
    ! [A_23,A_63] :
      ( k3_xboole_0(A_23,A_63) = k1_relat_1(k6_relat_1(A_23))
      | ~ r1_tarski(A_23,A_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_343])).

tff(c_478,plain,(
    ! [A_76,A_77] :
      ( k3_xboole_0(A_76,A_77) = A_76
      | ~ r1_tarski(A_76,A_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_368])).

tff(c_498,plain,(
    ! [A_68,A_69] : k3_xboole_0(k3_xboole_0(A_68,A_69),A_69) = k3_xboole_0(A_68,A_69) ),
    inference(resolution,[status(thm)],[c_380,c_478])).

tff(c_83,plain,(
    ! [A_43] :
      ( k7_relat_1(A_43,k1_relat_1(A_43)) = A_43
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_95,plain,(
    ! [A_23] :
      ( k7_relat_1(k6_relat_1(A_23),A_23) = k6_relat_1(A_23)
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_83])).

tff(c_99,plain,(
    ! [A_23] : k7_relat_1(k6_relat_1(A_23),A_23) = k6_relat_1(A_23) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_95])).

tff(c_371,plain,(
    ! [A_23] : k3_xboole_0(A_23,A_23) = k1_relat_1(k6_relat_1(A_23)) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_343])).

tff(c_383,plain,(
    ! [A_23] : k3_xboole_0(A_23,A_23) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_371])).

tff(c_342,plain,(
    ! [A_23,A_67] : k1_relat_1(k7_relat_1(k6_relat_1(A_23),A_67)) = k3_xboole_0(A_23,A_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_338])).

tff(c_40,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_503,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_40,c_478])).

tff(c_512,plain,(
    ! [C_78,A_79,B_80] :
      ( k7_relat_1(k7_relat_1(C_78,A_79),B_80) = k7_relat_1(C_78,k3_xboole_0(A_79,B_80))
      | ~ v1_relat_1(C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_564,plain,(
    ! [A_23,B_80] :
      ( k7_relat_1(k6_relat_1(A_23),k3_xboole_0(A_23,B_80)) = k7_relat_1(k6_relat_1(A_23),B_80)
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_512])).

tff(c_1361,plain,(
    ! [A_120,B_121] : k7_relat_1(k6_relat_1(A_120),k3_xboole_0(A_120,B_121)) = k7_relat_1(k6_relat_1(A_120),B_121) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_564])).

tff(c_1403,plain,(
    k7_relat_1(k6_relat_1('#skF_2'),'#skF_2') = k7_relat_1(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_503,c_1361])).

tff(c_1432,plain,(
    k7_relat_1(k6_relat_1('#skF_2'),'#skF_3') = k6_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_1403])).

tff(c_20,plain,(
    ! [C_18,A_16,B_17] :
      ( k7_relat_1(k7_relat_1(C_18,A_16),B_17) = k7_relat_1(C_18,k3_xboole_0(A_16,B_17))
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1458,plain,(
    ! [B_17] :
      ( k7_relat_1(k6_relat_1('#skF_2'),k3_xboole_0('#skF_3',B_17)) = k7_relat_1(k6_relat_1('#skF_2'),B_17)
      | ~ v1_relat_1(k6_relat_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1432,c_20])).

tff(c_2840,plain,(
    ! [B_163] : k7_relat_1(k6_relat_1('#skF_2'),k3_xboole_0('#skF_3',B_163)) = k7_relat_1(k6_relat_1('#skF_2'),B_163) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1458])).

tff(c_2879,plain,(
    ! [B_163] :
      ( r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1('#skF_2'),B_163)),k3_xboole_0('#skF_3',B_163))
      | ~ v1_relat_1(k6_relat_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2840,c_30])).

tff(c_2923,plain,(
    ! [B_164] : r1_tarski(k3_xboole_0('#skF_2',B_164),k3_xboole_0('#skF_3',B_164)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_342,c_2879])).

tff(c_2960,plain,(
    r1_tarski('#skF_2',k3_xboole_0('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_2923])).

tff(c_124,plain,(
    ! [B_47,A_48] :
      ( B_47 = A_48
      | ~ r1_tarski(B_47,A_48)
      | ~ r1_tarski(A_48,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1503,plain,(
    ! [B_124,A_125] :
      ( k1_relat_1(k7_relat_1(B_124,A_125)) = A_125
      | ~ r1_tarski(A_125,k1_relat_1(k7_relat_1(B_124,A_125)))
      | ~ v1_relat_1(B_124) ) ),
    inference(resolution,[status(thm)],[c_30,c_124])).

tff(c_1521,plain,(
    ! [A_23,A_63] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_23),A_63)) = A_63
      | ~ r1_tarski(A_63,k1_relat_1(k6_relat_1(A_23)))
      | ~ v1_relat_1(k6_relat_1(A_23))
      | ~ r1_tarski(A_23,A_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_1503])).

tff(c_1540,plain,(
    ! [A_23,A_63] :
      ( k3_xboole_0(A_23,A_63) = A_63
      | ~ r1_tarski(A_63,A_23)
      | ~ r1_tarski(A_23,A_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_26,c_342,c_1521])).

tff(c_2980,plain,
    ( k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),'#skF_2') = '#skF_2'
    | ~ r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_2960,c_1540])).

tff(c_3001,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_498,c_2980])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(k7_relat_1(A_14,B_15))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_24,plain,(
    ! [B_22,A_21] :
      ( k2_relat_1(k7_relat_1(B_22,A_21)) = k9_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3473,plain,(
    ! [C_172,A_173,B_174] :
      ( k2_relat_1(k7_relat_1(C_172,k3_xboole_0(A_173,B_174))) = k9_relat_1(k7_relat_1(C_172,A_173),B_174)
      | ~ v1_relat_1(k7_relat_1(C_172,A_173))
      | ~ v1_relat_1(C_172) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_512,c_24])).

tff(c_18866,plain,(
    ! [C_385,A_386,B_387] :
      ( k9_relat_1(k7_relat_1(C_385,A_386),B_387) = k9_relat_1(C_385,k3_xboole_0(A_386,B_387))
      | ~ v1_relat_1(C_385)
      | ~ v1_relat_1(k7_relat_1(C_385,A_386))
      | ~ v1_relat_1(C_385) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3473,c_24])).

tff(c_111461,plain,(
    ! [A_1007,B_1008,B_1009] :
      ( k9_relat_1(k7_relat_1(A_1007,B_1008),B_1009) = k9_relat_1(A_1007,k3_xboole_0(B_1008,B_1009))
      | ~ v1_relat_1(A_1007) ) ),
    inference(resolution,[status(thm)],[c_18,c_18866])).

tff(c_38,plain,(
    k9_relat_1(k7_relat_1('#skF_1','#skF_3'),'#skF_2') != k9_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_111510,plain,
    ( k9_relat_1('#skF_1',k3_xboole_0('#skF_3','#skF_2')) != k9_relat_1('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_111461,c_38])).

tff(c_111723,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3001,c_111510])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:33:38 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 29.92/20.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 29.92/20.26  
% 29.92/20.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 29.92/20.26  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 29.92/20.26  
% 29.92/20.26  %Foreground sorts:
% 29.92/20.26  
% 29.92/20.26  
% 29.92/20.26  %Background operators:
% 29.92/20.26  
% 29.92/20.26  
% 29.92/20.26  %Foreground operators:
% 29.92/20.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 29.92/20.26  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 29.92/20.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 29.92/20.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 29.92/20.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 29.92/20.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 29.92/20.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 29.92/20.26  tff('#skF_2', type, '#skF_2': $i).
% 29.92/20.26  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 29.92/20.26  tff('#skF_3', type, '#skF_3': $i).
% 29.92/20.26  tff('#skF_1', type, '#skF_1': $i).
% 29.92/20.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 29.92/20.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 29.92/20.26  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 29.92/20.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 29.92/20.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 29.92/20.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 29.92/20.26  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 29.92/20.26  
% 29.92/20.28  tff(f_91, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 29.92/20.28  tff(f_45, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 29.92/20.28  tff(f_65, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 29.92/20.28  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 29.92/20.28  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 29.92/20.28  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 29.92/20.28  tff(f_83, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 29.92/20.28  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 29.92/20.28  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 29.92/20.28  tff(f_49, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 29.92/20.28  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 29.92/20.28  tff(c_42, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 29.92/20.28  tff(c_16, plain, (![A_13]: (v1_relat_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 29.92/20.28  tff(c_26, plain, (![A_23]: (k1_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_65])).
% 29.92/20.28  tff(c_329, plain, (![B_66, A_67]: (k3_xboole_0(k1_relat_1(B_66), A_67)=k1_relat_1(k7_relat_1(B_66, A_67)) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_73])).
% 29.92/20.28  tff(c_338, plain, (![A_23, A_67]: (k1_relat_1(k7_relat_1(k6_relat_1(A_23), A_67))=k3_xboole_0(A_23, A_67) | ~v1_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_329])).
% 29.92/20.28  tff(c_343, plain, (![A_68, A_69]: (k1_relat_1(k7_relat_1(k6_relat_1(A_68), A_69))=k3_xboole_0(A_68, A_69))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_338])).
% 29.92/20.28  tff(c_30, plain, (![B_25, A_24]: (r1_tarski(k1_relat_1(k7_relat_1(B_25, A_24)), A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_69])).
% 29.92/20.28  tff(c_359, plain, (![A_68, A_69]: (r1_tarski(k3_xboole_0(A_68, A_69), A_69) | ~v1_relat_1(k6_relat_1(A_68)))), inference(superposition, [status(thm), theory('equality')], [c_343, c_30])).
% 29.92/20.28  tff(c_380, plain, (![A_68, A_69]: (r1_tarski(k3_xboole_0(A_68, A_69), A_69))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_359])).
% 29.92/20.28  tff(c_247, plain, (![B_62, A_63]: (k7_relat_1(B_62, A_63)=B_62 | ~r1_tarski(k1_relat_1(B_62), A_63) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_79])).
% 29.92/20.28  tff(c_256, plain, (![A_23, A_63]: (k7_relat_1(k6_relat_1(A_23), A_63)=k6_relat_1(A_23) | ~r1_tarski(A_23, A_63) | ~v1_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_247])).
% 29.92/20.28  tff(c_264, plain, (![A_23, A_63]: (k7_relat_1(k6_relat_1(A_23), A_63)=k6_relat_1(A_23) | ~r1_tarski(A_23, A_63))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_256])).
% 29.92/20.28  tff(c_368, plain, (![A_23, A_63]: (k3_xboole_0(A_23, A_63)=k1_relat_1(k6_relat_1(A_23)) | ~r1_tarski(A_23, A_63))), inference(superposition, [status(thm), theory('equality')], [c_264, c_343])).
% 29.92/20.28  tff(c_478, plain, (![A_76, A_77]: (k3_xboole_0(A_76, A_77)=A_76 | ~r1_tarski(A_76, A_77))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_368])).
% 29.92/20.28  tff(c_498, plain, (![A_68, A_69]: (k3_xboole_0(k3_xboole_0(A_68, A_69), A_69)=k3_xboole_0(A_68, A_69))), inference(resolution, [status(thm)], [c_380, c_478])).
% 29.92/20.28  tff(c_83, plain, (![A_43]: (k7_relat_1(A_43, k1_relat_1(A_43))=A_43 | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_83])).
% 29.92/20.28  tff(c_95, plain, (![A_23]: (k7_relat_1(k6_relat_1(A_23), A_23)=k6_relat_1(A_23) | ~v1_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_83])).
% 29.92/20.28  tff(c_99, plain, (![A_23]: (k7_relat_1(k6_relat_1(A_23), A_23)=k6_relat_1(A_23))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_95])).
% 29.92/20.28  tff(c_371, plain, (![A_23]: (k3_xboole_0(A_23, A_23)=k1_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_99, c_343])).
% 29.92/20.28  tff(c_383, plain, (![A_23]: (k3_xboole_0(A_23, A_23)=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_371])).
% 29.92/20.28  tff(c_342, plain, (![A_23, A_67]: (k1_relat_1(k7_relat_1(k6_relat_1(A_23), A_67))=k3_xboole_0(A_23, A_67))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_338])).
% 29.92/20.28  tff(c_40, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 29.92/20.28  tff(c_503, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_40, c_478])).
% 29.92/20.28  tff(c_512, plain, (![C_78, A_79, B_80]: (k7_relat_1(k7_relat_1(C_78, A_79), B_80)=k7_relat_1(C_78, k3_xboole_0(A_79, B_80)) | ~v1_relat_1(C_78))), inference(cnfTransformation, [status(thm)], [f_53])).
% 29.92/20.28  tff(c_564, plain, (![A_23, B_80]: (k7_relat_1(k6_relat_1(A_23), k3_xboole_0(A_23, B_80))=k7_relat_1(k6_relat_1(A_23), B_80) | ~v1_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_99, c_512])).
% 29.92/20.28  tff(c_1361, plain, (![A_120, B_121]: (k7_relat_1(k6_relat_1(A_120), k3_xboole_0(A_120, B_121))=k7_relat_1(k6_relat_1(A_120), B_121))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_564])).
% 29.92/20.28  tff(c_1403, plain, (k7_relat_1(k6_relat_1('#skF_2'), '#skF_2')=k7_relat_1(k6_relat_1('#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_503, c_1361])).
% 29.92/20.28  tff(c_1432, plain, (k7_relat_1(k6_relat_1('#skF_2'), '#skF_3')=k6_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_1403])).
% 29.92/20.28  tff(c_20, plain, (![C_18, A_16, B_17]: (k7_relat_1(k7_relat_1(C_18, A_16), B_17)=k7_relat_1(C_18, k3_xboole_0(A_16, B_17)) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 29.92/20.28  tff(c_1458, plain, (![B_17]: (k7_relat_1(k6_relat_1('#skF_2'), k3_xboole_0('#skF_3', B_17))=k7_relat_1(k6_relat_1('#skF_2'), B_17) | ~v1_relat_1(k6_relat_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_1432, c_20])).
% 29.92/20.28  tff(c_2840, plain, (![B_163]: (k7_relat_1(k6_relat_1('#skF_2'), k3_xboole_0('#skF_3', B_163))=k7_relat_1(k6_relat_1('#skF_2'), B_163))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1458])).
% 29.92/20.28  tff(c_2879, plain, (![B_163]: (r1_tarski(k1_relat_1(k7_relat_1(k6_relat_1('#skF_2'), B_163)), k3_xboole_0('#skF_3', B_163)) | ~v1_relat_1(k6_relat_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_2840, c_30])).
% 29.92/20.28  tff(c_2923, plain, (![B_164]: (r1_tarski(k3_xboole_0('#skF_2', B_164), k3_xboole_0('#skF_3', B_164)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_342, c_2879])).
% 29.92/20.28  tff(c_2960, plain, (r1_tarski('#skF_2', k3_xboole_0('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_383, c_2923])).
% 29.92/20.28  tff(c_124, plain, (![B_47, A_48]: (B_47=A_48 | ~r1_tarski(B_47, A_48) | ~r1_tarski(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_31])).
% 29.92/20.28  tff(c_1503, plain, (![B_124, A_125]: (k1_relat_1(k7_relat_1(B_124, A_125))=A_125 | ~r1_tarski(A_125, k1_relat_1(k7_relat_1(B_124, A_125))) | ~v1_relat_1(B_124))), inference(resolution, [status(thm)], [c_30, c_124])).
% 29.92/20.28  tff(c_1521, plain, (![A_23, A_63]: (k1_relat_1(k7_relat_1(k6_relat_1(A_23), A_63))=A_63 | ~r1_tarski(A_63, k1_relat_1(k6_relat_1(A_23))) | ~v1_relat_1(k6_relat_1(A_23)) | ~r1_tarski(A_23, A_63))), inference(superposition, [status(thm), theory('equality')], [c_264, c_1503])).
% 29.92/20.28  tff(c_1540, plain, (![A_23, A_63]: (k3_xboole_0(A_23, A_63)=A_63 | ~r1_tarski(A_63, A_23) | ~r1_tarski(A_23, A_63))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_26, c_342, c_1521])).
% 29.92/20.28  tff(c_2980, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), '#skF_2')='#skF_2' | ~r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_2960, c_1540])).
% 29.92/20.28  tff(c_3001, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_380, c_498, c_2980])).
% 29.92/20.28  tff(c_18, plain, (![A_14, B_15]: (v1_relat_1(k7_relat_1(A_14, B_15)) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 29.92/20.28  tff(c_24, plain, (![B_22, A_21]: (k2_relat_1(k7_relat_1(B_22, A_21))=k9_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_61])).
% 29.92/20.28  tff(c_3473, plain, (![C_172, A_173, B_174]: (k2_relat_1(k7_relat_1(C_172, k3_xboole_0(A_173, B_174)))=k9_relat_1(k7_relat_1(C_172, A_173), B_174) | ~v1_relat_1(k7_relat_1(C_172, A_173)) | ~v1_relat_1(C_172))), inference(superposition, [status(thm), theory('equality')], [c_512, c_24])).
% 29.92/20.28  tff(c_18866, plain, (![C_385, A_386, B_387]: (k9_relat_1(k7_relat_1(C_385, A_386), B_387)=k9_relat_1(C_385, k3_xboole_0(A_386, B_387)) | ~v1_relat_1(C_385) | ~v1_relat_1(k7_relat_1(C_385, A_386)) | ~v1_relat_1(C_385))), inference(superposition, [status(thm), theory('equality')], [c_3473, c_24])).
% 29.92/20.28  tff(c_111461, plain, (![A_1007, B_1008, B_1009]: (k9_relat_1(k7_relat_1(A_1007, B_1008), B_1009)=k9_relat_1(A_1007, k3_xboole_0(B_1008, B_1009)) | ~v1_relat_1(A_1007))), inference(resolution, [status(thm)], [c_18, c_18866])).
% 29.92/20.28  tff(c_38, plain, (k9_relat_1(k7_relat_1('#skF_1', '#skF_3'), '#skF_2')!=k9_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 29.92/20.28  tff(c_111510, plain, (k9_relat_1('#skF_1', k3_xboole_0('#skF_3', '#skF_2'))!=k9_relat_1('#skF_1', '#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_111461, c_38])).
% 29.92/20.28  tff(c_111723, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_3001, c_111510])).
% 29.92/20.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 29.92/20.28  
% 29.92/20.28  Inference rules
% 29.92/20.28  ----------------------
% 29.92/20.28  #Ref     : 0
% 29.92/20.28  #Sup     : 26103
% 29.92/20.28  #Fact    : 0
% 29.92/20.28  #Define  : 0
% 29.92/20.28  #Split   : 1
% 29.92/20.28  #Chain   : 0
% 29.92/20.28  #Close   : 0
% 29.92/20.28  
% 29.92/20.28  Ordering : KBO
% 29.92/20.28  
% 29.92/20.28  Simplification rules
% 29.92/20.28  ----------------------
% 29.92/20.28  #Subsume      : 9052
% 29.92/20.28  #Demod        : 28696
% 29.92/20.28  #Tautology    : 5594
% 29.92/20.28  #SimpNegUnit  : 18
% 29.92/20.28  #BackRed      : 40
% 29.92/20.28  
% 29.92/20.28  #Partial instantiations: 0
% 29.92/20.28  #Strategies tried      : 1
% 29.92/20.28  
% 29.92/20.28  Timing (in seconds)
% 29.92/20.28  ----------------------
% 29.92/20.28  Preprocessing        : 0.32
% 29.92/20.28  Parsing              : 0.17
% 29.92/20.28  CNF conversion       : 0.02
% 29.92/20.28  Main loop            : 19.20
% 29.92/20.28  Inferencing          : 2.54
% 29.92/20.28  Reduction            : 7.39
% 30.09/20.28  Demodulation         : 6.26
% 30.09/20.28  BG Simplification    : 0.37
% 30.09/20.28  Subsumption          : 8.17
% 30.09/20.28  Abstraction          : 0.61
% 30.09/20.28  MUC search           : 0.00
% 30.09/20.28  Cooper               : 0.00
% 30.09/20.28  Total                : 19.55
% 30.09/20.28  Index Insertion      : 0.00
% 30.09/20.28  Index Deletion       : 0.00
% 30.09/20.28  Index Matching       : 0.00
% 30.09/20.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
