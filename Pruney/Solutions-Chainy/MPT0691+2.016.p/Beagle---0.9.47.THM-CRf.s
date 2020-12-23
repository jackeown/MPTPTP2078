%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:41 EST 2020

% Result     : Theorem 29.35s
% Output     : CNFRefutation 29.35s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 160 expanded)
%              Number of leaves         :   27 (  64 expanded)
%              Depth                    :   16
%              Number of atoms          :  115 ( 280 expanded)
%              Number of equality atoms :   33 (  74 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_30,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_34,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_20,plain,(
    ! [B_17,A_16] :
      ( k2_relat_1(k7_relat_1(B_17,A_16)) = k9_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(k7_relat_1(A_14,B_15))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_32,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_72,plain,(
    ! [A_33,B_34] :
      ( k3_xboole_0(A_33,B_34) = A_33
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_83,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_72])).

tff(c_24,plain,(
    ! [A_20] :
      ( k10_relat_1(A_20,k2_relat_1(A_20)) = k1_relat_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_592,plain,(
    ! [A_71,C_72,B_73] :
      ( k3_xboole_0(A_71,k10_relat_1(C_72,B_73)) = k10_relat_1(k7_relat_1(C_72,A_71),B_73)
      | ~ v1_relat_1(C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_3508,plain,(
    ! [A_135,A_136] :
      ( k10_relat_1(k7_relat_1(A_135,A_136),k2_relat_1(A_135)) = k3_xboole_0(A_136,k1_relat_1(A_135))
      | ~ v1_relat_1(A_135)
      | ~ v1_relat_1(A_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_592])).

tff(c_22,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k10_relat_1(B_19,A_18),k1_relat_1(B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_15970,plain,(
    ! [A_312,A_313] :
      ( r1_tarski(k3_xboole_0(A_312,k1_relat_1(A_313)),k1_relat_1(k7_relat_1(A_313,A_312)))
      | ~ v1_relat_1(k7_relat_1(A_313,A_312))
      | ~ v1_relat_1(A_313)
      | ~ v1_relat_1(A_313) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3508,c_22])).

tff(c_16031,plain,
    ( r1_tarski('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_15970])).

tff(c_16054,plain,
    ( r1_tarski('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_16031])).

tff(c_16055,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_16054])).

tff(c_16058,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_16055])).

tff(c_16062,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_16058])).

tff(c_16064,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_16054])).

tff(c_16063,plain,(
    r1_tarski('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_16054])).

tff(c_26,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_22,A_21)),A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_231,plain,(
    ! [B_49,A_50] :
      ( B_49 = A_50
      | ~ r1_tarski(B_49,A_50)
      | ~ r1_tarski(A_50,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_244,plain,(
    ! [B_22,A_21] :
      ( k1_relat_1(k7_relat_1(B_22,A_21)) = A_21
      | ~ r1_tarski(A_21,k1_relat_1(k7_relat_1(B_22,A_21)))
      | ~ v1_relat_1(B_22) ) ),
    inference(resolution,[status(thm)],[c_26,c_231])).

tff(c_16323,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16063,c_244])).

tff(c_16338,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_16323])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_84,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_72])).

tff(c_652,plain,(
    ! [A_20,A_71] :
      ( k10_relat_1(k7_relat_1(A_20,A_71),k2_relat_1(A_20)) = k3_xboole_0(A_71,k1_relat_1(A_20))
      | ~ v1_relat_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_592])).

tff(c_28,plain,(
    ! [A_23,C_25,B_24] :
      ( k3_xboole_0(A_23,k10_relat_1(C_25,B_24)) = k10_relat_1(k7_relat_1(C_25,A_23),B_24)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1483,plain,(
    ! [A_94,B_95] :
      ( k3_xboole_0(A_94,B_95) = A_94
      | ~ r1_tarski(A_94,k3_xboole_0(A_94,B_95)) ) ),
    inference(resolution,[status(thm)],[c_8,c_231])).

tff(c_12706,plain,(
    ! [A_281,C_282,B_283] :
      ( k3_xboole_0(A_281,k10_relat_1(C_282,B_283)) = A_281
      | ~ r1_tarski(A_281,k10_relat_1(k7_relat_1(C_282,A_281),B_283))
      | ~ v1_relat_1(C_282) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1483])).

tff(c_111694,plain,(
    ! [A_1072,A_1073] :
      ( k3_xboole_0(A_1072,k10_relat_1(A_1073,k2_relat_1(A_1073))) = A_1072
      | ~ r1_tarski(A_1072,k3_xboole_0(A_1072,k1_relat_1(A_1073)))
      | ~ v1_relat_1(A_1073)
      | ~ v1_relat_1(A_1073)
      | ~ v1_relat_1(A_1073) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_652,c_12706])).

tff(c_111778,plain,(
    ! [A_1073] :
      ( k3_xboole_0(k1_relat_1(A_1073),k10_relat_1(A_1073,k2_relat_1(A_1073))) = k1_relat_1(A_1073)
      | ~ r1_tarski(k1_relat_1(A_1073),k1_relat_1(A_1073))
      | ~ v1_relat_1(A_1073)
      | ~ v1_relat_1(A_1073)
      | ~ v1_relat_1(A_1073) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_111694])).

tff(c_111818,plain,(
    ! [A_1074] :
      ( k3_xboole_0(k1_relat_1(A_1074),k10_relat_1(A_1074,k2_relat_1(A_1074))) = k1_relat_1(A_1074)
      | ~ v1_relat_1(A_1074) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_111778])).

tff(c_14,plain,(
    ! [B_11,A_10] : k2_tarski(B_11,A_10) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_106,plain,(
    ! [A_36,B_37] : k1_setfam_1(k2_tarski(A_36,B_37)) = k3_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_121,plain,(
    ! [B_38,A_39] : k1_setfam_1(k2_tarski(B_38,A_39)) = k3_xboole_0(A_39,B_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_106])).

tff(c_16,plain,(
    ! [A_12,B_13] : k1_setfam_1(k2_tarski(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_144,plain,(
    ! [B_40,A_41] : k3_xboole_0(B_40,A_41) = k3_xboole_0(A_41,B_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_16])).

tff(c_159,plain,(
    ! [B_40,A_41] : r1_tarski(k3_xboole_0(B_40,A_41),A_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_8])).

tff(c_112730,plain,(
    ! [A_1075] :
      ( r1_tarski(k1_relat_1(A_1075),k10_relat_1(A_1075,k2_relat_1(A_1075)))
      | ~ v1_relat_1(A_1075) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111818,c_159])).

tff(c_112799,plain,
    ( r1_tarski('#skF_1',k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1'))))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_16338,c_112730])).

tff(c_112830,plain,(
    r1_tarski('#skF_1',k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16064,c_112799])).

tff(c_1498,plain,(
    ! [A_23,C_25,B_24] :
      ( k3_xboole_0(A_23,k10_relat_1(C_25,B_24)) = A_23
      | ~ r1_tarski(A_23,k10_relat_1(k7_relat_1(C_25,A_23),B_24))
      | ~ v1_relat_1(C_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1483])).

tff(c_112840,plain,
    ( k3_xboole_0('#skF_1',k10_relat_1('#skF_2',k2_relat_1(k7_relat_1('#skF_2','#skF_1')))) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_112830,c_1498])).

tff(c_112871,plain,(
    k3_xboole_0('#skF_1',k10_relat_1('#skF_2',k2_relat_1(k7_relat_1('#skF_2','#skF_1')))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_112840])).

tff(c_113533,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k2_relat_1(k7_relat_1('#skF_2','#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_112871,c_159])).

tff(c_113765,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_113533])).

tff(c_113776,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_113765])).

tff(c_113778,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_113776])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:27:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 29.35/21.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.35/21.36  
% 29.35/21.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.35/21.36  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 29.35/21.36  
% 29.35/21.36  %Foreground sorts:
% 29.35/21.36  
% 29.35/21.36  
% 29.35/21.36  %Background operators:
% 29.35/21.36  
% 29.35/21.36  
% 29.35/21.36  %Foreground operators:
% 29.35/21.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 29.35/21.36  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 29.35/21.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 29.35/21.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 29.35/21.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 29.35/21.36  tff('#skF_2', type, '#skF_2': $i).
% 29.35/21.36  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 29.35/21.36  tff('#skF_1', type, '#skF_1': $i).
% 29.35/21.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 29.35/21.36  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 29.35/21.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 29.35/21.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 29.35/21.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 29.35/21.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 29.35/21.36  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 29.35/21.36  
% 29.35/21.38  tff(f_78, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 29.35/21.38  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 29.35/21.38  tff(f_51, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 29.35/21.38  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 29.35/21.38  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 29.35/21.38  tff(f_71, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 29.35/21.38  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 29.35/21.38  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 29.35/21.38  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 29.35/21.38  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 29.35/21.38  tff(f_45, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 29.35/21.38  tff(f_47, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 29.35/21.38  tff(c_30, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 29.35/21.38  tff(c_34, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 29.35/21.38  tff(c_20, plain, (![B_17, A_16]: (k2_relat_1(k7_relat_1(B_17, A_16))=k9_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 29.35/21.38  tff(c_18, plain, (![A_14, B_15]: (v1_relat_1(k7_relat_1(A_14, B_15)) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 29.35/21.38  tff(c_32, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 29.35/21.38  tff(c_72, plain, (![A_33, B_34]: (k3_xboole_0(A_33, B_34)=A_33 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_43])).
% 29.35/21.38  tff(c_83, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))='#skF_1'), inference(resolution, [status(thm)], [c_32, c_72])).
% 29.35/21.38  tff(c_24, plain, (![A_20]: (k10_relat_1(A_20, k2_relat_1(A_20))=k1_relat_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_63])).
% 29.35/21.38  tff(c_592, plain, (![A_71, C_72, B_73]: (k3_xboole_0(A_71, k10_relat_1(C_72, B_73))=k10_relat_1(k7_relat_1(C_72, A_71), B_73) | ~v1_relat_1(C_72))), inference(cnfTransformation, [status(thm)], [f_71])).
% 29.35/21.38  tff(c_3508, plain, (![A_135, A_136]: (k10_relat_1(k7_relat_1(A_135, A_136), k2_relat_1(A_135))=k3_xboole_0(A_136, k1_relat_1(A_135)) | ~v1_relat_1(A_135) | ~v1_relat_1(A_135))), inference(superposition, [status(thm), theory('equality')], [c_24, c_592])).
% 29.35/21.38  tff(c_22, plain, (![B_19, A_18]: (r1_tarski(k10_relat_1(B_19, A_18), k1_relat_1(B_19)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 29.35/21.38  tff(c_15970, plain, (![A_312, A_313]: (r1_tarski(k3_xboole_0(A_312, k1_relat_1(A_313)), k1_relat_1(k7_relat_1(A_313, A_312))) | ~v1_relat_1(k7_relat_1(A_313, A_312)) | ~v1_relat_1(A_313) | ~v1_relat_1(A_313))), inference(superposition, [status(thm), theory('equality')], [c_3508, c_22])).
% 29.35/21.38  tff(c_16031, plain, (r1_tarski('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_83, c_15970])).
% 29.35/21.38  tff(c_16054, plain, (r1_tarski('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_16031])).
% 29.35/21.38  tff(c_16055, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_16054])).
% 29.35/21.38  tff(c_16058, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_18, c_16055])).
% 29.35/21.38  tff(c_16062, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_16058])).
% 29.35/21.38  tff(c_16064, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_16054])).
% 29.35/21.38  tff(c_16063, plain, (r1_tarski('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_16054])).
% 29.35/21.38  tff(c_26, plain, (![B_22, A_21]: (r1_tarski(k1_relat_1(k7_relat_1(B_22, A_21)), A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_67])).
% 29.35/21.38  tff(c_231, plain, (![B_49, A_50]: (B_49=A_50 | ~r1_tarski(B_49, A_50) | ~r1_tarski(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_31])).
% 29.35/21.38  tff(c_244, plain, (![B_22, A_21]: (k1_relat_1(k7_relat_1(B_22, A_21))=A_21 | ~r1_tarski(A_21, k1_relat_1(k7_relat_1(B_22, A_21))) | ~v1_relat_1(B_22))), inference(resolution, [status(thm)], [c_26, c_231])).
% 29.35/21.38  tff(c_16323, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_16063, c_244])).
% 29.35/21.38  tff(c_16338, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_16323])).
% 29.35/21.38  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 29.35/21.38  tff(c_84, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_72])).
% 29.35/21.38  tff(c_652, plain, (![A_20, A_71]: (k10_relat_1(k7_relat_1(A_20, A_71), k2_relat_1(A_20))=k3_xboole_0(A_71, k1_relat_1(A_20)) | ~v1_relat_1(A_20) | ~v1_relat_1(A_20))), inference(superposition, [status(thm), theory('equality')], [c_24, c_592])).
% 29.35/21.38  tff(c_28, plain, (![A_23, C_25, B_24]: (k3_xboole_0(A_23, k10_relat_1(C_25, B_24))=k10_relat_1(k7_relat_1(C_25, A_23), B_24) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_71])).
% 29.35/21.38  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 29.35/21.38  tff(c_1483, plain, (![A_94, B_95]: (k3_xboole_0(A_94, B_95)=A_94 | ~r1_tarski(A_94, k3_xboole_0(A_94, B_95)))), inference(resolution, [status(thm)], [c_8, c_231])).
% 29.35/21.38  tff(c_12706, plain, (![A_281, C_282, B_283]: (k3_xboole_0(A_281, k10_relat_1(C_282, B_283))=A_281 | ~r1_tarski(A_281, k10_relat_1(k7_relat_1(C_282, A_281), B_283)) | ~v1_relat_1(C_282))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1483])).
% 29.35/21.38  tff(c_111694, plain, (![A_1072, A_1073]: (k3_xboole_0(A_1072, k10_relat_1(A_1073, k2_relat_1(A_1073)))=A_1072 | ~r1_tarski(A_1072, k3_xboole_0(A_1072, k1_relat_1(A_1073))) | ~v1_relat_1(A_1073) | ~v1_relat_1(A_1073) | ~v1_relat_1(A_1073))), inference(superposition, [status(thm), theory('equality')], [c_652, c_12706])).
% 29.35/21.38  tff(c_111778, plain, (![A_1073]: (k3_xboole_0(k1_relat_1(A_1073), k10_relat_1(A_1073, k2_relat_1(A_1073)))=k1_relat_1(A_1073) | ~r1_tarski(k1_relat_1(A_1073), k1_relat_1(A_1073)) | ~v1_relat_1(A_1073) | ~v1_relat_1(A_1073) | ~v1_relat_1(A_1073))), inference(superposition, [status(thm), theory('equality')], [c_84, c_111694])).
% 29.35/21.38  tff(c_111818, plain, (![A_1074]: (k3_xboole_0(k1_relat_1(A_1074), k10_relat_1(A_1074, k2_relat_1(A_1074)))=k1_relat_1(A_1074) | ~v1_relat_1(A_1074))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_111778])).
% 29.35/21.38  tff(c_14, plain, (![B_11, A_10]: (k2_tarski(B_11, A_10)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 29.35/21.38  tff(c_106, plain, (![A_36, B_37]: (k1_setfam_1(k2_tarski(A_36, B_37))=k3_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_47])).
% 29.35/21.38  tff(c_121, plain, (![B_38, A_39]: (k1_setfam_1(k2_tarski(B_38, A_39))=k3_xboole_0(A_39, B_38))), inference(superposition, [status(thm), theory('equality')], [c_14, c_106])).
% 29.35/21.38  tff(c_16, plain, (![A_12, B_13]: (k1_setfam_1(k2_tarski(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 29.35/21.38  tff(c_144, plain, (![B_40, A_41]: (k3_xboole_0(B_40, A_41)=k3_xboole_0(A_41, B_40))), inference(superposition, [status(thm), theory('equality')], [c_121, c_16])).
% 29.35/21.38  tff(c_159, plain, (![B_40, A_41]: (r1_tarski(k3_xboole_0(B_40, A_41), A_41))), inference(superposition, [status(thm), theory('equality')], [c_144, c_8])).
% 29.35/21.38  tff(c_112730, plain, (![A_1075]: (r1_tarski(k1_relat_1(A_1075), k10_relat_1(A_1075, k2_relat_1(A_1075))) | ~v1_relat_1(A_1075))), inference(superposition, [status(thm), theory('equality')], [c_111818, c_159])).
% 29.35/21.38  tff(c_112799, plain, (r1_tarski('#skF_1', k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_16338, c_112730])).
% 29.35/21.38  tff(c_112830, plain, (r1_tarski('#skF_1', k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_16064, c_112799])).
% 29.35/21.38  tff(c_1498, plain, (![A_23, C_25, B_24]: (k3_xboole_0(A_23, k10_relat_1(C_25, B_24))=A_23 | ~r1_tarski(A_23, k10_relat_1(k7_relat_1(C_25, A_23), B_24)) | ~v1_relat_1(C_25))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1483])).
% 29.35/21.38  tff(c_112840, plain, (k3_xboole_0('#skF_1', k10_relat_1('#skF_2', k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_112830, c_1498])).
% 29.35/21.38  tff(c_112871, plain, (k3_xboole_0('#skF_1', k10_relat_1('#skF_2', k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_112840])).
% 29.35/21.38  tff(c_113533, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_112871, c_159])).
% 29.35/21.38  tff(c_113765, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_20, c_113533])).
% 29.35/21.38  tff(c_113776, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_113765])).
% 29.35/21.38  tff(c_113778, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_113776])).
% 29.35/21.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 29.35/21.38  
% 29.35/21.38  Inference rules
% 29.35/21.38  ----------------------
% 29.35/21.38  #Ref     : 0
% 29.35/21.38  #Sup     : 27914
% 29.35/21.38  #Fact    : 0
% 29.35/21.38  #Define  : 0
% 29.35/21.38  #Split   : 3
% 29.35/21.38  #Chain   : 0
% 29.35/21.38  #Close   : 0
% 29.35/21.38  
% 29.35/21.38  Ordering : KBO
% 29.35/21.38  
% 29.35/21.38  Simplification rules
% 29.35/21.38  ----------------------
% 29.35/21.38  #Subsume      : 7802
% 29.35/21.38  #Demod        : 16443
% 29.35/21.38  #Tautology    : 9237
% 29.35/21.38  #SimpNegUnit  : 1
% 29.35/21.38  #BackRed      : 1
% 29.35/21.38  
% 29.35/21.38  #Partial instantiations: 0
% 29.35/21.38  #Strategies tried      : 1
% 29.35/21.38  
% 29.35/21.38  Timing (in seconds)
% 29.35/21.38  ----------------------
% 29.35/21.38  Preprocessing        : 0.31
% 29.35/21.38  Parsing              : 0.17
% 29.35/21.38  CNF conversion       : 0.02
% 29.35/21.38  Main loop            : 20.25
% 29.35/21.38  Inferencing          : 2.24
% 29.35/21.38  Reduction            : 10.97
% 29.35/21.38  Demodulation         : 10.08
% 29.35/21.38  BG Simplification    : 0.24
% 29.35/21.38  Subsumption          : 6.05
% 29.35/21.38  Abstraction          : 0.37
% 29.35/21.38  MUC search           : 0.00
% 29.35/21.38  Cooper               : 0.00
% 29.35/21.38  Total                : 20.60
% 29.35/21.38  Index Insertion      : 0.00
% 29.35/21.38  Index Deletion       : 0.00
% 29.35/21.38  Index Matching       : 0.00
% 29.35/21.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
