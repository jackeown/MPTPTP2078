%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:53 EST 2020

% Result     : Theorem 5.27s
% Output     : CNFRefutation 5.67s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 128 expanded)
%              Number of leaves         :   28 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :   93 ( 210 expanded)
%              Number of equality atoms :   12 (  36 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_3731,plain,(
    ! [C_384,A_385,B_386] :
      ( r1_tarski(k9_relat_1(C_384,k3_xboole_0(A_385,B_386)),k3_xboole_0(k9_relat_1(C_384,A_385),k9_relat_1(C_384,B_386)))
      | ~ v1_relat_1(C_384) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_tarski(A_3,B_4)
      | ~ r1_tarski(A_3,k3_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3816,plain,(
    ! [C_391,A_392,B_393] :
      ( r1_tarski(k9_relat_1(C_391,k3_xboole_0(A_392,B_393)),k9_relat_1(C_391,A_392))
      | ~ v1_relat_1(C_391) ) ),
    inference(resolution,[status(thm)],[c_3731,c_4])).

tff(c_30,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_20,plain,(
    ! [A_25,B_26] :
      ( v1_funct_1(k7_relat_1(A_25,B_26))
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_14,plain,(
    ! [A_15,B_16] :
      ( v1_relat_1(k7_relat_1(A_15,B_16))
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_486,plain,(
    ! [A_89,C_90,B_91] :
      ( k3_xboole_0(A_89,k10_relat_1(C_90,B_91)) = k10_relat_1(k7_relat_1(C_90,A_89),B_91)
      | ~ v1_relat_1(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_569,plain,(
    ! [C_90,A_89,B_91] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_90,A_89),B_91),A_89)
      | ~ v1_relat_1(C_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_486,c_2])).

tff(c_690,plain,(
    ! [A_103,C_104,B_105] :
      ( k9_relat_1(k7_relat_1(A_103,C_104),B_105) = k9_relat_1(A_103,B_105)
      | ~ r1_tarski(B_105,C_104)
      | ~ v1_relat_1(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_26,plain,(
    ! [B_31,A_30] :
      ( r1_tarski(k9_relat_1(B_31,k10_relat_1(B_31,A_30)),A_30)
      | ~ v1_funct_1(B_31)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1861,plain,(
    ! [A_217,C_218,A_219] :
      ( r1_tarski(k9_relat_1(A_217,k10_relat_1(k7_relat_1(A_217,C_218),A_219)),A_219)
      | ~ v1_funct_1(k7_relat_1(A_217,C_218))
      | ~ v1_relat_1(k7_relat_1(A_217,C_218))
      | ~ r1_tarski(k10_relat_1(k7_relat_1(A_217,C_218),A_219),C_218)
      | ~ v1_relat_1(A_217) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_690,c_26])).

tff(c_3273,plain,(
    ! [C_344,A_345,B_346] :
      ( r1_tarski(k9_relat_1(C_344,k10_relat_1(k7_relat_1(C_344,A_345),B_346)),B_346)
      | ~ v1_funct_1(k7_relat_1(C_344,A_345))
      | ~ v1_relat_1(k7_relat_1(C_344,A_345))
      | ~ v1_relat_1(C_344) ) ),
    inference(resolution,[status(thm)],[c_569,c_1861])).

tff(c_24,plain,(
    ! [A_27,C_29,B_28] :
      ( k3_xboole_0(A_27,k10_relat_1(C_29,B_28)) = k10_relat_1(k7_relat_1(C_29,A_27),B_28)
      | ~ v1_relat_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_282,plain,(
    ! [A_67,B_68,C_69] :
      ( r1_tarski(A_67,k3_xboole_0(B_68,C_69))
      | ~ r1_tarski(A_67,C_69)
      | ~ r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [B_10,A_9] : k2_tarski(B_10,A_9) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_68,plain,(
    ! [A_38,B_39] : k1_setfam_1(k2_tarski(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_92,plain,(
    ! [B_42,A_43] : k1_setfam_1(k2_tarski(B_42,A_43)) = k3_xboole_0(A_43,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_68])).

tff(c_12,plain,(
    ! [A_13,B_14] : k1_setfam_1(k2_tarski(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_98,plain,(
    ! [B_42,A_43] : k3_xboole_0(B_42,A_43) = k3_xboole_0(A_43,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_12])).

tff(c_28,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_154,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0('#skF_2',k9_relat_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_28])).

tff(c_296,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(resolution,[status(thm)],[c_282,c_154])).

tff(c_347,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_296])).

tff(c_600,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k10_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2')),'#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_347])).

tff(c_602,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k10_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_600])).

tff(c_3280,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3273,c_602])).

tff(c_3296,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3280])).

tff(c_3299,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_3296])).

tff(c_3302,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_3299])).

tff(c_3306,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3302])).

tff(c_3307,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_3296])).

tff(c_3311,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_3307])).

tff(c_3315,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_3311])).

tff(c_3316,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_296])).

tff(c_3819,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3816,c_3316])).

tff(c_3839,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_3819])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n001.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 13:04:59 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.27/2.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.58/2.08  
% 5.58/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.58/2.08  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 5.58/2.08  
% 5.58/2.08  %Foreground sorts:
% 5.58/2.08  
% 5.58/2.08  
% 5.58/2.08  %Background operators:
% 5.58/2.08  
% 5.58/2.08  
% 5.58/2.08  %Foreground operators:
% 5.58/2.08  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.58/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.58/2.08  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.58/2.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.58/2.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.58/2.08  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.58/2.08  tff('#skF_2', type, '#skF_2': $i).
% 5.58/2.08  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.58/2.08  tff('#skF_3', type, '#skF_3': $i).
% 5.58/2.08  tff('#skF_1', type, '#skF_1': $i).
% 5.58/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.58/2.08  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.58/2.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.58/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.58/2.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.58/2.08  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.58/2.08  
% 5.67/2.10  tff(f_83, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, k10_relat_1(C, B))), k3_xboole_0(k9_relat_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_funct_1)).
% 5.67/2.10  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_relat_1)).
% 5.67/2.10  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 5.67/2.10  tff(f_66, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_funct_1)).
% 5.67/2.10  tff(f_47, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 5.67/2.10  tff(f_70, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 5.67/2.10  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.67/2.10  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 5.67/2.10  tff(f_76, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 5.67/2.10  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 5.67/2.10  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.67/2.10  tff(f_43, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.67/2.10  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.67/2.10  tff(c_3731, plain, (![C_384, A_385, B_386]: (r1_tarski(k9_relat_1(C_384, k3_xboole_0(A_385, B_386)), k3_xboole_0(k9_relat_1(C_384, A_385), k9_relat_1(C_384, B_386))) | ~v1_relat_1(C_384))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.67/2.10  tff(c_4, plain, (![A_3, B_4, C_5]: (r1_tarski(A_3, B_4) | ~r1_tarski(A_3, k3_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.67/2.10  tff(c_3816, plain, (![C_391, A_392, B_393]: (r1_tarski(k9_relat_1(C_391, k3_xboole_0(A_392, B_393)), k9_relat_1(C_391, A_392)) | ~v1_relat_1(C_391))), inference(resolution, [status(thm)], [c_3731, c_4])).
% 5.67/2.10  tff(c_30, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.67/2.10  tff(c_20, plain, (![A_25, B_26]: (v1_funct_1(k7_relat_1(A_25, B_26)) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.67/2.10  tff(c_14, plain, (![A_15, B_16]: (v1_relat_1(k7_relat_1(A_15, B_16)) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.67/2.10  tff(c_486, plain, (![A_89, C_90, B_91]: (k3_xboole_0(A_89, k10_relat_1(C_90, B_91))=k10_relat_1(k7_relat_1(C_90, A_89), B_91) | ~v1_relat_1(C_90))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.67/2.10  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.67/2.10  tff(c_569, plain, (![C_90, A_89, B_91]: (r1_tarski(k10_relat_1(k7_relat_1(C_90, A_89), B_91), A_89) | ~v1_relat_1(C_90))), inference(superposition, [status(thm), theory('equality')], [c_486, c_2])).
% 5.67/2.10  tff(c_690, plain, (![A_103, C_104, B_105]: (k9_relat_1(k7_relat_1(A_103, C_104), B_105)=k9_relat_1(A_103, B_105) | ~r1_tarski(B_105, C_104) | ~v1_relat_1(A_103))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.67/2.10  tff(c_26, plain, (![B_31, A_30]: (r1_tarski(k9_relat_1(B_31, k10_relat_1(B_31, A_30)), A_30) | ~v1_funct_1(B_31) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.67/2.10  tff(c_1861, plain, (![A_217, C_218, A_219]: (r1_tarski(k9_relat_1(A_217, k10_relat_1(k7_relat_1(A_217, C_218), A_219)), A_219) | ~v1_funct_1(k7_relat_1(A_217, C_218)) | ~v1_relat_1(k7_relat_1(A_217, C_218)) | ~r1_tarski(k10_relat_1(k7_relat_1(A_217, C_218), A_219), C_218) | ~v1_relat_1(A_217))), inference(superposition, [status(thm), theory('equality')], [c_690, c_26])).
% 5.67/2.10  tff(c_3273, plain, (![C_344, A_345, B_346]: (r1_tarski(k9_relat_1(C_344, k10_relat_1(k7_relat_1(C_344, A_345), B_346)), B_346) | ~v1_funct_1(k7_relat_1(C_344, A_345)) | ~v1_relat_1(k7_relat_1(C_344, A_345)) | ~v1_relat_1(C_344))), inference(resolution, [status(thm)], [c_569, c_1861])).
% 5.67/2.10  tff(c_24, plain, (![A_27, C_29, B_28]: (k3_xboole_0(A_27, k10_relat_1(C_29, B_28))=k10_relat_1(k7_relat_1(C_29, A_27), B_28) | ~v1_relat_1(C_29))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.67/2.10  tff(c_282, plain, (![A_67, B_68, C_69]: (r1_tarski(A_67, k3_xboole_0(B_68, C_69)) | ~r1_tarski(A_67, C_69) | ~r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.67/2.10  tff(c_8, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.67/2.10  tff(c_68, plain, (![A_38, B_39]: (k1_setfam_1(k2_tarski(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.67/2.10  tff(c_92, plain, (![B_42, A_43]: (k1_setfam_1(k2_tarski(B_42, A_43))=k3_xboole_0(A_43, B_42))), inference(superposition, [status(thm), theory('equality')], [c_8, c_68])).
% 5.67/2.10  tff(c_12, plain, (![A_13, B_14]: (k1_setfam_1(k2_tarski(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.67/2.10  tff(c_98, plain, (![B_42, A_43]: (k3_xboole_0(B_42, A_43)=k3_xboole_0(A_43, B_42))), inference(superposition, [status(thm), theory('equality')], [c_92, c_12])).
% 5.67/2.10  tff(c_28, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.67/2.10  tff(c_154, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0('#skF_2', k9_relat_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_28])).
% 5.67/2.10  tff(c_296, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(resolution, [status(thm)], [c_282, c_154])).
% 5.67/2.10  tff(c_347, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(splitLeft, [status(thm)], [c_296])).
% 5.67/2.10  tff(c_600, plain, (~r1_tarski(k9_relat_1('#skF_3', k10_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')), '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_24, c_347])).
% 5.67/2.10  tff(c_602, plain, (~r1_tarski(k9_relat_1('#skF_3', k10_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_600])).
% 5.67/2.10  tff(c_3280, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3273, c_602])).
% 5.67/2.10  tff(c_3296, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_3280])).
% 5.67/2.10  tff(c_3299, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_3296])).
% 5.67/2.10  tff(c_3302, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_3299])).
% 5.67/2.10  tff(c_3306, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_3302])).
% 5.67/2.10  tff(c_3307, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_3296])).
% 5.67/2.10  tff(c_3311, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_3307])).
% 5.67/2.10  tff(c_3315, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_3311])).
% 5.67/2.10  tff(c_3316, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_296])).
% 5.67/2.10  tff(c_3819, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3816, c_3316])).
% 5.67/2.10  tff(c_3839, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_3819])).
% 5.67/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.67/2.10  
% 5.67/2.10  Inference rules
% 5.67/2.10  ----------------------
% 5.67/2.10  #Ref     : 0
% 5.67/2.10  #Sup     : 888
% 5.67/2.10  #Fact    : 0
% 5.67/2.10  #Define  : 0
% 5.67/2.10  #Split   : 3
% 5.67/2.10  #Chain   : 0
% 5.67/2.10  #Close   : 0
% 5.67/2.10  
% 5.67/2.10  Ordering : KBO
% 5.67/2.10  
% 5.67/2.10  Simplification rules
% 5.67/2.10  ----------------------
% 5.67/2.10  #Subsume      : 93
% 5.67/2.10  #Demod        : 251
% 5.67/2.10  #Tautology    : 274
% 5.67/2.10  #SimpNegUnit  : 0
% 5.67/2.10  #BackRed      : 0
% 5.67/2.10  
% 5.67/2.10  #Partial instantiations: 0
% 5.67/2.10  #Strategies tried      : 1
% 5.67/2.10  
% 5.67/2.10  Timing (in seconds)
% 5.67/2.10  ----------------------
% 5.67/2.10  Preprocessing        : 0.30
% 5.67/2.10  Parsing              : 0.16
% 5.67/2.10  CNF conversion       : 0.02
% 5.67/2.10  Main loop            : 1.04
% 5.67/2.10  Inferencing          : 0.32
% 5.67/2.10  Reduction            : 0.40
% 5.67/2.10  Demodulation         : 0.33
% 5.67/2.10  BG Simplification    : 0.03
% 5.67/2.10  Subsumption          : 0.22
% 5.67/2.10  Abstraction          : 0.03
% 5.67/2.10  MUC search           : 0.00
% 5.67/2.10  Cooper               : 0.00
% 5.67/2.10  Total                : 1.38
% 5.67/2.10  Index Insertion      : 0.00
% 5.67/2.10  Index Deletion       : 0.00
% 5.67/2.10  Index Matching       : 0.00
% 5.67/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
