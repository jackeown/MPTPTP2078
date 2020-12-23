%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:51 EST 2020

% Result     : Theorem 4.24s
% Output     : CNFRefutation 4.24s
% Verified   : 
% Statistics : Number of formulae       :   55 (  80 expanded)
%              Number of leaves         :   28 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :   49 (  87 expanded)
%              Number of equality atoms :   24 (  39 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_44,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_50,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_62,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

tff(c_48,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_26,plain,(
    ! [A_12] : k2_xboole_0(A_12,A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_34,plain,(
    ! [A_20,B_21] : r1_tarski(A_20,k2_xboole_0(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_317,plain,(
    ! [A_70,B_71,C_72] :
      ( r1_tarski(k4_xboole_0(A_70,B_71),C_72)
      | ~ r1_tarski(A_70,k2_xboole_0(B_71,C_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_30,plain,(
    ! [A_16] :
      ( k1_xboole_0 = A_16
      | ~ r1_tarski(A_16,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_337,plain,(
    ! [A_74,B_75] :
      ( k4_xboole_0(A_74,B_75) = k1_xboole_0
      | ~ r1_tarski(A_74,k2_xboole_0(B_75,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_317,c_30])).

tff(c_393,plain,(
    ! [A_76] : k4_xboole_0(A_76,A_76) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_337])).

tff(c_28,plain,(
    ! [A_14,B_15] : k2_xboole_0(A_14,k4_xboole_0(B_15,A_14)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_407,plain,(
    ! [A_76] : k2_xboole_0(A_76,k1_xboole_0) = k2_xboole_0(A_76,A_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_28])).

tff(c_421,plain,(
    ! [A_76] : k2_xboole_0(A_76,k1_xboole_0) = A_76 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_407])).

tff(c_36,plain,(
    ! [B_23,A_22] : k2_tarski(B_23,A_22) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_112,plain,(
    ! [A_40,B_41] : k3_tarski(k2_tarski(A_40,B_41)) = k2_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_127,plain,(
    ! [B_42,A_43] : k3_tarski(k2_tarski(B_42,A_43)) = k2_xboole_0(A_43,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_112])).

tff(c_40,plain,(
    ! [A_26,B_27] : k3_tarski(k2_tarski(A_26,B_27)) = k2_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_133,plain,(
    ! [B_42,A_43] : k2_xboole_0(B_42,A_43) = k2_xboole_0(A_43,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_40])).

tff(c_46,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_325,plain,(
    ! [A_70,B_71] :
      ( k4_xboole_0(A_70,B_71) = k1_xboole_0
      | ~ r1_tarski(A_70,k2_xboole_0(B_71,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_317,c_30])).

tff(c_847,plain,(
    ! [A_105,B_106] :
      ( k4_xboole_0(A_105,B_106) = k1_xboole_0
      | ~ r1_tarski(A_105,B_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_325])).

tff(c_881,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_847])).

tff(c_897,plain,(
    k2_xboole_0('#skF_5',k1_xboole_0) = k2_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_881,c_28])).

tff(c_909,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_133,c_897])).

tff(c_605,plain,(
    ! [C_83,A_84,B_85] :
      ( k2_xboole_0(k10_relat_1(C_83,A_84),k10_relat_1(C_83,B_85)) = k10_relat_1(C_83,k2_xboole_0(A_84,B_85))
      | ~ v1_relat_1(C_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2693,plain,(
    ! [C_153,A_154,B_155] :
      ( r1_tarski(k10_relat_1(C_153,A_154),k10_relat_1(C_153,k2_xboole_0(A_154,B_155)))
      | ~ v1_relat_1(C_153) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_605,c_34])).

tff(c_3992,plain,(
    ! [C_180] :
      ( r1_tarski(k10_relat_1(C_180,'#skF_4'),k10_relat_1(C_180,'#skF_5'))
      | ~ v1_relat_1(C_180) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_909,c_2693])).

tff(c_44,plain,(
    ~ r1_tarski(k10_relat_1('#skF_6','#skF_4'),k10_relat_1('#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3998,plain,(
    ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_3992,c_44])).

tff(c_4003,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3998])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:41:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.24/1.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.24/1.82  
% 4.24/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.24/1.82  %$ r2_hidden > r1_tarski > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 4.24/1.82  
% 4.24/1.82  %Foreground sorts:
% 4.24/1.82  
% 4.24/1.82  
% 4.24/1.82  %Background operators:
% 4.24/1.82  
% 4.24/1.82  
% 4.24/1.82  %Foreground operators:
% 4.24/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.24/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.24/1.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.24/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.24/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.24/1.82  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.24/1.82  tff('#skF_5', type, '#skF_5': $i).
% 4.24/1.82  tff('#skF_6', type, '#skF_6': $i).
% 4.24/1.82  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.24/1.82  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.24/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.24/1.82  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.24/1.82  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.24/1.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.24/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.24/1.82  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.24/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.24/1.82  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.24/1.82  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.24/1.82  
% 4.24/1.83  tff(f_73, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_relat_1)).
% 4.24/1.83  tff(f_44, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 4.24/1.83  tff(f_56, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.24/1.83  tff(f_54, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 4.24/1.83  tff(f_50, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 4.24/1.83  tff(f_46, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.24/1.83  tff(f_58, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.24/1.83  tff(f_62, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.24/1.83  tff(f_66, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 4.24/1.83  tff(c_48, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.24/1.83  tff(c_26, plain, (![A_12]: (k2_xboole_0(A_12, A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.24/1.83  tff(c_34, plain, (![A_20, B_21]: (r1_tarski(A_20, k2_xboole_0(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.24/1.83  tff(c_317, plain, (![A_70, B_71, C_72]: (r1_tarski(k4_xboole_0(A_70, B_71), C_72) | ~r1_tarski(A_70, k2_xboole_0(B_71, C_72)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.24/1.83  tff(c_30, plain, (![A_16]: (k1_xboole_0=A_16 | ~r1_tarski(A_16, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.24/1.83  tff(c_337, plain, (![A_74, B_75]: (k4_xboole_0(A_74, B_75)=k1_xboole_0 | ~r1_tarski(A_74, k2_xboole_0(B_75, k1_xboole_0)))), inference(resolution, [status(thm)], [c_317, c_30])).
% 4.24/1.83  tff(c_393, plain, (![A_76]: (k4_xboole_0(A_76, A_76)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_337])).
% 4.24/1.83  tff(c_28, plain, (![A_14, B_15]: (k2_xboole_0(A_14, k4_xboole_0(B_15, A_14))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.24/1.83  tff(c_407, plain, (![A_76]: (k2_xboole_0(A_76, k1_xboole_0)=k2_xboole_0(A_76, A_76))), inference(superposition, [status(thm), theory('equality')], [c_393, c_28])).
% 4.24/1.83  tff(c_421, plain, (![A_76]: (k2_xboole_0(A_76, k1_xboole_0)=A_76)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_407])).
% 4.24/1.83  tff(c_36, plain, (![B_23, A_22]: (k2_tarski(B_23, A_22)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.24/1.83  tff(c_112, plain, (![A_40, B_41]: (k3_tarski(k2_tarski(A_40, B_41))=k2_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.24/1.83  tff(c_127, plain, (![B_42, A_43]: (k3_tarski(k2_tarski(B_42, A_43))=k2_xboole_0(A_43, B_42))), inference(superposition, [status(thm), theory('equality')], [c_36, c_112])).
% 4.24/1.83  tff(c_40, plain, (![A_26, B_27]: (k3_tarski(k2_tarski(A_26, B_27))=k2_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.24/1.83  tff(c_133, plain, (![B_42, A_43]: (k2_xboole_0(B_42, A_43)=k2_xboole_0(A_43, B_42))), inference(superposition, [status(thm), theory('equality')], [c_127, c_40])).
% 4.24/1.83  tff(c_46, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.24/1.83  tff(c_325, plain, (![A_70, B_71]: (k4_xboole_0(A_70, B_71)=k1_xboole_0 | ~r1_tarski(A_70, k2_xboole_0(B_71, k1_xboole_0)))), inference(resolution, [status(thm)], [c_317, c_30])).
% 4.24/1.83  tff(c_847, plain, (![A_105, B_106]: (k4_xboole_0(A_105, B_106)=k1_xboole_0 | ~r1_tarski(A_105, B_106))), inference(demodulation, [status(thm), theory('equality')], [c_421, c_325])).
% 4.24/1.83  tff(c_881, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_847])).
% 4.24/1.83  tff(c_897, plain, (k2_xboole_0('#skF_5', k1_xboole_0)=k2_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_881, c_28])).
% 4.24/1.83  tff(c_909, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_421, c_133, c_897])).
% 4.24/1.83  tff(c_605, plain, (![C_83, A_84, B_85]: (k2_xboole_0(k10_relat_1(C_83, A_84), k10_relat_1(C_83, B_85))=k10_relat_1(C_83, k2_xboole_0(A_84, B_85)) | ~v1_relat_1(C_83))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.24/1.83  tff(c_2693, plain, (![C_153, A_154, B_155]: (r1_tarski(k10_relat_1(C_153, A_154), k10_relat_1(C_153, k2_xboole_0(A_154, B_155))) | ~v1_relat_1(C_153))), inference(superposition, [status(thm), theory('equality')], [c_605, c_34])).
% 4.24/1.83  tff(c_3992, plain, (![C_180]: (r1_tarski(k10_relat_1(C_180, '#skF_4'), k10_relat_1(C_180, '#skF_5')) | ~v1_relat_1(C_180))), inference(superposition, [status(thm), theory('equality')], [c_909, c_2693])).
% 4.24/1.83  tff(c_44, plain, (~r1_tarski(k10_relat_1('#skF_6', '#skF_4'), k10_relat_1('#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.24/1.83  tff(c_3998, plain, (~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_3992, c_44])).
% 4.24/1.83  tff(c_4003, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_3998])).
% 4.24/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.24/1.83  
% 4.24/1.83  Inference rules
% 4.24/1.83  ----------------------
% 4.24/1.83  #Ref     : 0
% 4.24/1.83  #Sup     : 965
% 4.24/1.83  #Fact    : 2
% 4.24/1.83  #Define  : 0
% 4.24/1.83  #Split   : 0
% 4.24/1.83  #Chain   : 0
% 4.24/1.83  #Close   : 0
% 4.24/1.83  
% 4.24/1.83  Ordering : KBO
% 4.24/1.83  
% 4.24/1.83  Simplification rules
% 4.24/1.83  ----------------------
% 4.24/1.83  #Subsume      : 76
% 4.24/1.83  #Demod        : 971
% 4.24/1.83  #Tautology    : 668
% 4.24/1.83  #SimpNegUnit  : 0
% 4.24/1.83  #BackRed      : 2
% 4.24/1.83  
% 4.24/1.83  #Partial instantiations: 0
% 4.24/1.83  #Strategies tried      : 1
% 4.24/1.83  
% 4.24/1.83  Timing (in seconds)
% 4.24/1.83  ----------------------
% 4.24/1.83  Preprocessing        : 0.32
% 4.24/1.83  Parsing              : 0.17
% 4.24/1.83  CNF conversion       : 0.02
% 4.24/1.83  Main loop            : 0.69
% 4.24/1.83  Inferencing          : 0.22
% 4.24/1.83  Reduction            : 0.29
% 4.24/1.83  Demodulation         : 0.24
% 4.24/1.83  BG Simplification    : 0.03
% 4.24/1.83  Subsumption          : 0.11
% 4.24/1.83  Abstraction          : 0.04
% 4.24/1.83  MUC search           : 0.00
% 4.24/1.83  Cooper               : 0.00
% 4.24/1.83  Total                : 1.04
% 4.24/1.83  Index Insertion      : 0.00
% 4.24/1.83  Index Deletion       : 0.00
% 4.24/1.83  Index Matching       : 0.00
% 4.24/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
