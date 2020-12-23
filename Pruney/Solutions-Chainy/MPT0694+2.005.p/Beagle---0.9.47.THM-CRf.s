%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:53 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 143 expanded)
%              Number of leaves         :   29 (  59 expanded)
%              Depth                    :   13
%              Number of atoms          :  113 ( 245 expanded)
%              Number of equality atoms :   16 (  42 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,k10_relat_1(C,B))),k3_xboole_0(k9_relat_1(C,A),B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k7_relat_1(A_12,B_13))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_16,C_20,B_19] :
      ( k9_relat_1(k7_relat_1(A_16,C_20),B_19) = k9_relat_1(A_16,B_19)
      | ~ r1_tarski(B_19,C_20)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14,plain,(
    ! [B_15,A_14] :
      ( k2_relat_1(k7_relat_1(B_15,A_14)) = k9_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_168,plain,(
    ! [B_50,A_51] :
      ( k2_relat_1(k7_relat_1(B_50,A_51)) = k9_relat_1(B_50,A_51)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_22,A_21)),k2_relat_1(B_22))
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_183,plain,(
    ! [B_52,A_53] :
      ( r1_tarski(k9_relat_1(B_52,A_53),k2_relat_1(B_52))
      | ~ v1_relat_1(B_52)
      | ~ v1_relat_1(B_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_18])).

tff(c_620,plain,(
    ! [B_111,A_112,A_113] :
      ( r1_tarski(k9_relat_1(k7_relat_1(B_111,A_112),A_113),k9_relat_1(B_111,A_112))
      | ~ v1_relat_1(k7_relat_1(B_111,A_112))
      | ~ v1_relat_1(k7_relat_1(B_111,A_112))
      | ~ v1_relat_1(B_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_183])).

tff(c_647,plain,(
    ! [A_120,B_121,C_122] :
      ( r1_tarski(k9_relat_1(A_120,B_121),k9_relat_1(A_120,C_122))
      | ~ v1_relat_1(k7_relat_1(A_120,C_122))
      | ~ v1_relat_1(k7_relat_1(A_120,C_122))
      | ~ v1_relat_1(A_120)
      | ~ r1_tarski(B_121,C_122)
      | ~ v1_relat_1(A_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_620])).

tff(c_30,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_20,plain,(
    ! [A_23,B_24] :
      ( v1_funct_1(k7_relat_1(A_23,B_24))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_199,plain,(
    ! [A_59,C_60,B_61] :
      ( k3_xboole_0(A_59,k10_relat_1(C_60,B_61)) = k10_relat_1(k7_relat_1(C_60,A_59),B_61)
      | ~ v1_relat_1(C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_220,plain,(
    ! [C_60,A_59,B_61] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_60,A_59),B_61),A_59)
      | ~ v1_relat_1(C_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_2])).

tff(c_278,plain,(
    ! [A_71,C_72,B_73] :
      ( k9_relat_1(k7_relat_1(A_71,C_72),B_73) = k9_relat_1(A_71,B_73)
      | ~ r1_tarski(B_73,C_72)
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_26,plain,(
    ! [B_29,A_28] :
      ( r1_tarski(k9_relat_1(B_29,k10_relat_1(B_29,A_28)),A_28)
      | ~ v1_funct_1(B_29)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_313,plain,(
    ! [A_81,C_82,A_83] :
      ( r1_tarski(k9_relat_1(A_81,k10_relat_1(k7_relat_1(A_81,C_82),A_83)),A_83)
      | ~ v1_funct_1(k7_relat_1(A_81,C_82))
      | ~ v1_relat_1(k7_relat_1(A_81,C_82))
      | ~ r1_tarski(k10_relat_1(k7_relat_1(A_81,C_82),A_83),C_82)
      | ~ v1_relat_1(A_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_278,c_26])).

tff(c_439,plain,(
    ! [C_91,A_92,B_93] :
      ( r1_tarski(k9_relat_1(C_91,k10_relat_1(k7_relat_1(C_91,A_92),B_93)),B_93)
      | ~ v1_funct_1(k7_relat_1(C_91,A_92))
      | ~ v1_relat_1(k7_relat_1(C_91,A_92))
      | ~ v1_relat_1(C_91) ) ),
    inference(resolution,[status(thm)],[c_220,c_313])).

tff(c_24,plain,(
    ! [A_25,C_27,B_26] :
      ( k3_xboole_0(A_25,k10_relat_1(C_27,B_26)) = k10_relat_1(k7_relat_1(C_27,A_25),B_26)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_188,plain,(
    ! [A_56,B_57,C_58] :
      ( r1_tarski(A_56,k3_xboole_0(B_57,C_58))
      | ~ r1_tarski(A_56,C_58)
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_68,plain,(
    ! [A_36,B_37] : k1_setfam_1(k2_tarski(A_36,B_37)) = k3_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_92,plain,(
    ! [B_40,A_41] : k1_setfam_1(k2_tarski(B_40,A_41)) = k3_xboole_0(A_41,B_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_68])).

tff(c_10,plain,(
    ! [A_10,B_11] : k1_setfam_1(k2_tarski(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_98,plain,(
    ! [B_40,A_41] : k3_xboole_0(B_40,A_41) = k3_xboole_0(A_41,B_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_10])).

tff(c_28,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_154,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0('#skF_2',k9_relat_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_28])).

tff(c_198,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(resolution,[status(thm)],[c_188,c_154])).

tff(c_298,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_198])).

tff(c_301,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k10_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2')),'#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_298])).

tff(c_303,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k10_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_301])).

tff(c_442,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_439,c_303])).

tff(c_455,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_442])).

tff(c_456,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_455])).

tff(c_459,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_456])).

tff(c_463,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_459])).

tff(c_464,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_455])).

tff(c_475,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_464])).

tff(c_479,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_475])).

tff(c_480,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_653,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2')),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_647,c_480])).

tff(c_665,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_2,c_653])).

tff(c_668,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_665])).

tff(c_672,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_668])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:40:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.44  
% 2.81/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.45  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 2.81/1.45  
% 2.81/1.45  %Foreground sorts:
% 2.81/1.45  
% 2.81/1.45  
% 2.81/1.45  %Background operators:
% 2.81/1.45  
% 2.81/1.45  
% 2.81/1.45  %Foreground operators:
% 2.81/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.81/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.45  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.81/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.81/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.81/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.81/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.81/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.81/1.45  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.81/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.81/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.81/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.45  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.81/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.81/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.81/1.45  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.81/1.45  
% 2.81/1.46  tff(f_83, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, k10_relat_1(C, B))), k3_xboole_0(k9_relat_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_funct_1)).
% 2.81/1.46  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.81/1.46  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.81/1.46  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 2.81/1.46  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.81/1.46  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_relat_1)).
% 2.81/1.46  tff(f_66, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_funct_1)).
% 2.81/1.46  tff(f_70, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 2.81/1.46  tff(f_76, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 2.81/1.46  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.81/1.46  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.81/1.46  tff(f_39, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.81/1.46  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.81/1.46  tff(c_12, plain, (![A_12, B_13]: (v1_relat_1(k7_relat_1(A_12, B_13)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.81/1.46  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.81/1.46  tff(c_16, plain, (![A_16, C_20, B_19]: (k9_relat_1(k7_relat_1(A_16, C_20), B_19)=k9_relat_1(A_16, B_19) | ~r1_tarski(B_19, C_20) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.81/1.46  tff(c_14, plain, (![B_15, A_14]: (k2_relat_1(k7_relat_1(B_15, A_14))=k9_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.81/1.46  tff(c_168, plain, (![B_50, A_51]: (k2_relat_1(k7_relat_1(B_50, A_51))=k9_relat_1(B_50, A_51) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.81/1.46  tff(c_18, plain, (![B_22, A_21]: (r1_tarski(k2_relat_1(k7_relat_1(B_22, A_21)), k2_relat_1(B_22)) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.81/1.46  tff(c_183, plain, (![B_52, A_53]: (r1_tarski(k9_relat_1(B_52, A_53), k2_relat_1(B_52)) | ~v1_relat_1(B_52) | ~v1_relat_1(B_52))), inference(superposition, [status(thm), theory('equality')], [c_168, c_18])).
% 2.81/1.46  tff(c_620, plain, (![B_111, A_112, A_113]: (r1_tarski(k9_relat_1(k7_relat_1(B_111, A_112), A_113), k9_relat_1(B_111, A_112)) | ~v1_relat_1(k7_relat_1(B_111, A_112)) | ~v1_relat_1(k7_relat_1(B_111, A_112)) | ~v1_relat_1(B_111))), inference(superposition, [status(thm), theory('equality')], [c_14, c_183])).
% 2.81/1.46  tff(c_647, plain, (![A_120, B_121, C_122]: (r1_tarski(k9_relat_1(A_120, B_121), k9_relat_1(A_120, C_122)) | ~v1_relat_1(k7_relat_1(A_120, C_122)) | ~v1_relat_1(k7_relat_1(A_120, C_122)) | ~v1_relat_1(A_120) | ~r1_tarski(B_121, C_122) | ~v1_relat_1(A_120))), inference(superposition, [status(thm), theory('equality')], [c_16, c_620])).
% 2.81/1.46  tff(c_30, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.81/1.46  tff(c_20, plain, (![A_23, B_24]: (v1_funct_1(k7_relat_1(A_23, B_24)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.81/1.46  tff(c_199, plain, (![A_59, C_60, B_61]: (k3_xboole_0(A_59, k10_relat_1(C_60, B_61))=k10_relat_1(k7_relat_1(C_60, A_59), B_61) | ~v1_relat_1(C_60))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.81/1.46  tff(c_220, plain, (![C_60, A_59, B_61]: (r1_tarski(k10_relat_1(k7_relat_1(C_60, A_59), B_61), A_59) | ~v1_relat_1(C_60))), inference(superposition, [status(thm), theory('equality')], [c_199, c_2])).
% 2.81/1.46  tff(c_278, plain, (![A_71, C_72, B_73]: (k9_relat_1(k7_relat_1(A_71, C_72), B_73)=k9_relat_1(A_71, B_73) | ~r1_tarski(B_73, C_72) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.81/1.46  tff(c_26, plain, (![B_29, A_28]: (r1_tarski(k9_relat_1(B_29, k10_relat_1(B_29, A_28)), A_28) | ~v1_funct_1(B_29) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.81/1.46  tff(c_313, plain, (![A_81, C_82, A_83]: (r1_tarski(k9_relat_1(A_81, k10_relat_1(k7_relat_1(A_81, C_82), A_83)), A_83) | ~v1_funct_1(k7_relat_1(A_81, C_82)) | ~v1_relat_1(k7_relat_1(A_81, C_82)) | ~r1_tarski(k10_relat_1(k7_relat_1(A_81, C_82), A_83), C_82) | ~v1_relat_1(A_81))), inference(superposition, [status(thm), theory('equality')], [c_278, c_26])).
% 2.81/1.46  tff(c_439, plain, (![C_91, A_92, B_93]: (r1_tarski(k9_relat_1(C_91, k10_relat_1(k7_relat_1(C_91, A_92), B_93)), B_93) | ~v1_funct_1(k7_relat_1(C_91, A_92)) | ~v1_relat_1(k7_relat_1(C_91, A_92)) | ~v1_relat_1(C_91))), inference(resolution, [status(thm)], [c_220, c_313])).
% 2.81/1.46  tff(c_24, plain, (![A_25, C_27, B_26]: (k3_xboole_0(A_25, k10_relat_1(C_27, B_26))=k10_relat_1(k7_relat_1(C_27, A_25), B_26) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.81/1.46  tff(c_188, plain, (![A_56, B_57, C_58]: (r1_tarski(A_56, k3_xboole_0(B_57, C_58)) | ~r1_tarski(A_56, C_58) | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.81/1.46  tff(c_6, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.81/1.46  tff(c_68, plain, (![A_36, B_37]: (k1_setfam_1(k2_tarski(A_36, B_37))=k3_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.81/1.46  tff(c_92, plain, (![B_40, A_41]: (k1_setfam_1(k2_tarski(B_40, A_41))=k3_xboole_0(A_41, B_40))), inference(superposition, [status(thm), theory('equality')], [c_6, c_68])).
% 2.81/1.46  tff(c_10, plain, (![A_10, B_11]: (k1_setfam_1(k2_tarski(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.81/1.46  tff(c_98, plain, (![B_40, A_41]: (k3_xboole_0(B_40, A_41)=k3_xboole_0(A_41, B_40))), inference(superposition, [status(thm), theory('equality')], [c_92, c_10])).
% 2.81/1.46  tff(c_28, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.81/1.46  tff(c_154, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0('#skF_2', k9_relat_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_28])).
% 2.81/1.46  tff(c_198, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(resolution, [status(thm)], [c_188, c_154])).
% 2.81/1.46  tff(c_298, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(splitLeft, [status(thm)], [c_198])).
% 2.81/1.46  tff(c_301, plain, (~r1_tarski(k9_relat_1('#skF_3', k10_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')), '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_298])).
% 2.81/1.46  tff(c_303, plain, (~r1_tarski(k9_relat_1('#skF_3', k10_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_301])).
% 2.81/1.46  tff(c_442, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_439, c_303])).
% 2.81/1.46  tff(c_455, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_442])).
% 2.81/1.46  tff(c_456, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_455])).
% 2.81/1.46  tff(c_459, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_456])).
% 2.81/1.46  tff(c_463, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_459])).
% 2.81/1.46  tff(c_464, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_455])).
% 2.81/1.46  tff(c_475, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_464])).
% 2.81/1.46  tff(c_479, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_475])).
% 2.81/1.46  tff(c_480, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_198])).
% 2.81/1.46  tff(c_653, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2')), '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_647, c_480])).
% 2.81/1.46  tff(c_665, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_2, c_653])).
% 2.81/1.46  tff(c_668, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_665])).
% 2.81/1.46  tff(c_672, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_668])).
% 2.81/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.46  
% 2.81/1.46  Inference rules
% 2.81/1.46  ----------------------
% 2.81/1.46  #Ref     : 0
% 2.81/1.46  #Sup     : 167
% 2.81/1.46  #Fact    : 0
% 2.81/1.46  #Define  : 0
% 2.81/1.46  #Split   : 2
% 2.81/1.46  #Chain   : 0
% 2.81/1.46  #Close   : 0
% 2.81/1.46  
% 2.81/1.46  Ordering : KBO
% 2.81/1.46  
% 2.81/1.46  Simplification rules
% 2.81/1.46  ----------------------
% 2.81/1.46  #Subsume      : 35
% 2.81/1.46  #Demod        : 20
% 2.81/1.46  #Tautology    : 52
% 2.81/1.46  #SimpNegUnit  : 0
% 2.81/1.46  #BackRed      : 0
% 2.81/1.46  
% 2.81/1.46  #Partial instantiations: 0
% 2.81/1.46  #Strategies tried      : 1
% 2.81/1.46  
% 2.81/1.46  Timing (in seconds)
% 2.81/1.46  ----------------------
% 3.13/1.47  Preprocessing        : 0.31
% 3.13/1.47  Parsing              : 0.16
% 3.13/1.47  CNF conversion       : 0.02
% 3.13/1.47  Main loop            : 0.38
% 3.13/1.47  Inferencing          : 0.16
% 3.13/1.47  Reduction            : 0.10
% 3.13/1.47  Demodulation         : 0.08
% 3.13/1.47  BG Simplification    : 0.02
% 3.13/1.47  Subsumption          : 0.07
% 3.13/1.47  Abstraction          : 0.02
% 3.13/1.47  MUC search           : 0.00
% 3.13/1.47  Cooper               : 0.00
% 3.13/1.47  Total                : 0.72
% 3.13/1.47  Index Insertion      : 0.00
% 3.13/1.47  Index Deletion       : 0.00
% 3.13/1.47  Index Matching       : 0.00
% 3.13/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
