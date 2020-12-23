%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:35 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   47 (  61 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   36 (  53 expanded)
%              Number of equality atoms :   25 (  38 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C,D] : v1_relat_1(k2_tarski(k4_tarski(A,B),k4_tarski(C,D))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k2_tarski(A,B),k1_tarski(C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D,E] :
      ( v1_relat_1(E)
     => ( E = k2_tarski(k4_tarski(A,B),k4_tarski(C,D))
       => ( k1_relat_1(E) = k2_tarski(A,C)
          & k2_relat_1(E) = k2_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] : k3_relat_1(k1_tarski(k4_tarski(A,B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_relat_1)).

tff(c_6,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_76,plain,(
    ! [A_34,B_35,C_36,D_37] : v1_relat_1(k2_tarski(k4_tarski(A_34,B_35),k4_tarski(C_36,D_37))) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_80,plain,(
    ! [A_34,B_35] : v1_relat_1(k1_tarski(k4_tarski(A_34,B_35))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_76])).

tff(c_8,plain,(
    ! [A_7,B_8] : k1_enumset1(A_7,A_7,B_8) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_109,plain,(
    ! [A_46,B_47,C_48] : k2_xboole_0(k2_tarski(A_46,B_47),k1_tarski(C_48)) = k1_enumset1(A_46,B_47,C_48) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_118,plain,(
    ! [A_6,C_48] : k2_xboole_0(k1_tarski(A_6),k1_tarski(C_48)) = k1_enumset1(A_6,A_6,C_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_109])).

tff(c_121,plain,(
    ! [A_6,C_48] : k2_xboole_0(k1_tarski(A_6),k1_tarski(C_48)) = k2_tarski(A_6,C_48) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_118])).

tff(c_18,plain,(
    ! [A_19,B_20,C_21,D_22] : v1_relat_1(k2_tarski(k4_tarski(A_19,B_20),k4_tarski(C_21,D_22))) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ! [A_23,B_24,C_25,D_26] :
      ( k1_relat_1(k2_tarski(k4_tarski(A_23,B_24),k4_tarski(C_25,D_26))) = k2_tarski(A_23,C_25)
      | ~ v1_relat_1(k2_tarski(k4_tarski(A_23,B_24),k4_tarski(C_25,D_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_151,plain,(
    ! [A_52,B_53,C_54,D_55] : k1_relat_1(k2_tarski(k4_tarski(A_52,B_53),k4_tarski(C_54,D_55))) = k2_tarski(A_52,C_54) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_22])).

tff(c_164,plain,(
    ! [A_52,B_53] : k2_tarski(A_52,A_52) = k1_relat_1(k1_tarski(k4_tarski(A_52,B_53))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_151])).

tff(c_169,plain,(
    ! [A_52,B_53] : k1_relat_1(k1_tarski(k4_tarski(A_52,B_53))) = k1_tarski(A_52) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_164])).

tff(c_20,plain,(
    ! [A_23,B_24,C_25,D_26] :
      ( k2_relat_1(k2_tarski(k4_tarski(A_23,B_24),k4_tarski(C_25,D_26))) = k2_tarski(B_24,D_26)
      | ~ v1_relat_1(k2_tarski(k4_tarski(A_23,B_24),k4_tarski(C_25,D_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_193,plain,(
    ! [A_62,B_63,C_64,D_65] : k2_relat_1(k2_tarski(k4_tarski(A_62,B_63),k4_tarski(C_64,D_65))) = k2_tarski(B_63,D_65) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20])).

tff(c_206,plain,(
    ! [B_63,A_62] : k2_tarski(B_63,B_63) = k2_relat_1(k1_tarski(k4_tarski(A_62,B_63))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_193])).

tff(c_212,plain,(
    ! [A_66,B_67] : k2_relat_1(k1_tarski(k4_tarski(A_66,B_67))) = k1_tarski(B_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_206])).

tff(c_16,plain,(
    ! [A_18] :
      ( k2_xboole_0(k1_relat_1(A_18),k2_relat_1(A_18)) = k3_relat_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_218,plain,(
    ! [A_66,B_67] :
      ( k2_xboole_0(k1_relat_1(k1_tarski(k4_tarski(A_66,B_67))),k1_tarski(B_67)) = k3_relat_1(k1_tarski(k4_tarski(A_66,B_67)))
      | ~ v1_relat_1(k1_tarski(k4_tarski(A_66,B_67))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_16])).

tff(c_224,plain,(
    ! [A_66,B_67] : k3_relat_1(k1_tarski(k4_tarski(A_66,B_67))) = k2_tarski(A_66,B_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_121,c_169,c_218])).

tff(c_24,plain,(
    k3_relat_1(k1_tarski(k4_tarski('#skF_1','#skF_2'))) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_228,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:05:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.18  
% 1.90/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.18  %$ v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > #skF_2 > #skF_1
% 1.90/1.18  
% 1.90/1.18  %Foreground sorts:
% 1.90/1.18  
% 1.90/1.18  
% 1.90/1.18  %Background operators:
% 1.90/1.18  
% 1.90/1.18  
% 1.90/1.18  %Foreground operators:
% 1.90/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.90/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.90/1.18  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.90/1.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.90/1.18  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.90/1.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.90/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.90/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.90/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.90/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.90/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.90/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.90/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.18  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.90/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.90/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.90/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.90/1.18  
% 1.90/1.19  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.90/1.19  tff(f_45, axiom, (![A, B, C, D]: v1_relat_1(k2_tarski(k4_tarski(A, B), k4_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_relat_1)).
% 1.90/1.19  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.90/1.19  tff(f_29, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k2_tarski(A, B), k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_enumset1)).
% 1.90/1.19  tff(f_53, axiom, (![A, B, C, D, E]: (v1_relat_1(E) => ((E = k2_tarski(k4_tarski(A, B), k4_tarski(C, D))) => ((k1_relat_1(E) = k2_tarski(A, C)) & (k2_relat_1(E) = k2_tarski(B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_relat_1)).
% 1.90/1.19  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 1.90/1.19  tff(f_56, negated_conjecture, ~(![A, B]: (k3_relat_1(k1_tarski(k4_tarski(A, B))) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_relat_1)).
% 1.90/1.19  tff(c_6, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.90/1.19  tff(c_76, plain, (![A_34, B_35, C_36, D_37]: (v1_relat_1(k2_tarski(k4_tarski(A_34, B_35), k4_tarski(C_36, D_37))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.90/1.19  tff(c_80, plain, (![A_34, B_35]: (v1_relat_1(k1_tarski(k4_tarski(A_34, B_35))))), inference(superposition, [status(thm), theory('equality')], [c_6, c_76])).
% 1.90/1.19  tff(c_8, plain, (![A_7, B_8]: (k1_enumset1(A_7, A_7, B_8)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.90/1.19  tff(c_109, plain, (![A_46, B_47, C_48]: (k2_xboole_0(k2_tarski(A_46, B_47), k1_tarski(C_48))=k1_enumset1(A_46, B_47, C_48))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.90/1.19  tff(c_118, plain, (![A_6, C_48]: (k2_xboole_0(k1_tarski(A_6), k1_tarski(C_48))=k1_enumset1(A_6, A_6, C_48))), inference(superposition, [status(thm), theory('equality')], [c_6, c_109])).
% 1.90/1.19  tff(c_121, plain, (![A_6, C_48]: (k2_xboole_0(k1_tarski(A_6), k1_tarski(C_48))=k2_tarski(A_6, C_48))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_118])).
% 1.90/1.19  tff(c_18, plain, (![A_19, B_20, C_21, D_22]: (v1_relat_1(k2_tarski(k4_tarski(A_19, B_20), k4_tarski(C_21, D_22))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.90/1.19  tff(c_22, plain, (![A_23, B_24, C_25, D_26]: (k1_relat_1(k2_tarski(k4_tarski(A_23, B_24), k4_tarski(C_25, D_26)))=k2_tarski(A_23, C_25) | ~v1_relat_1(k2_tarski(k4_tarski(A_23, B_24), k4_tarski(C_25, D_26))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.90/1.19  tff(c_151, plain, (![A_52, B_53, C_54, D_55]: (k1_relat_1(k2_tarski(k4_tarski(A_52, B_53), k4_tarski(C_54, D_55)))=k2_tarski(A_52, C_54))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_22])).
% 1.90/1.19  tff(c_164, plain, (![A_52, B_53]: (k2_tarski(A_52, A_52)=k1_relat_1(k1_tarski(k4_tarski(A_52, B_53))))), inference(superposition, [status(thm), theory('equality')], [c_6, c_151])).
% 1.90/1.19  tff(c_169, plain, (![A_52, B_53]: (k1_relat_1(k1_tarski(k4_tarski(A_52, B_53)))=k1_tarski(A_52))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_164])).
% 1.90/1.19  tff(c_20, plain, (![A_23, B_24, C_25, D_26]: (k2_relat_1(k2_tarski(k4_tarski(A_23, B_24), k4_tarski(C_25, D_26)))=k2_tarski(B_24, D_26) | ~v1_relat_1(k2_tarski(k4_tarski(A_23, B_24), k4_tarski(C_25, D_26))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.90/1.19  tff(c_193, plain, (![A_62, B_63, C_64, D_65]: (k2_relat_1(k2_tarski(k4_tarski(A_62, B_63), k4_tarski(C_64, D_65)))=k2_tarski(B_63, D_65))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20])).
% 1.90/1.19  tff(c_206, plain, (![B_63, A_62]: (k2_tarski(B_63, B_63)=k2_relat_1(k1_tarski(k4_tarski(A_62, B_63))))), inference(superposition, [status(thm), theory('equality')], [c_6, c_193])).
% 1.90/1.19  tff(c_212, plain, (![A_66, B_67]: (k2_relat_1(k1_tarski(k4_tarski(A_66, B_67)))=k1_tarski(B_67))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_206])).
% 1.90/1.19  tff(c_16, plain, (![A_18]: (k2_xboole_0(k1_relat_1(A_18), k2_relat_1(A_18))=k3_relat_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.90/1.19  tff(c_218, plain, (![A_66, B_67]: (k2_xboole_0(k1_relat_1(k1_tarski(k4_tarski(A_66, B_67))), k1_tarski(B_67))=k3_relat_1(k1_tarski(k4_tarski(A_66, B_67))) | ~v1_relat_1(k1_tarski(k4_tarski(A_66, B_67))))), inference(superposition, [status(thm), theory('equality')], [c_212, c_16])).
% 1.90/1.19  tff(c_224, plain, (![A_66, B_67]: (k3_relat_1(k1_tarski(k4_tarski(A_66, B_67)))=k2_tarski(A_66, B_67))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_121, c_169, c_218])).
% 1.90/1.19  tff(c_24, plain, (k3_relat_1(k1_tarski(k4_tarski('#skF_1', '#skF_2')))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.90/1.19  tff(c_228, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_224, c_24])).
% 1.90/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.19  
% 1.90/1.19  Inference rules
% 1.90/1.19  ----------------------
% 1.90/1.19  #Ref     : 0
% 1.90/1.19  #Sup     : 43
% 1.90/1.19  #Fact    : 0
% 1.90/1.19  #Define  : 0
% 1.90/1.19  #Split   : 0
% 1.90/1.19  #Chain   : 0
% 1.90/1.19  #Close   : 0
% 1.90/1.19  
% 1.90/1.19  Ordering : KBO
% 1.90/1.19  
% 1.90/1.19  Simplification rules
% 1.90/1.19  ----------------------
% 1.90/1.19  #Subsume      : 0
% 1.90/1.19  #Demod        : 16
% 1.90/1.19  #Tautology    : 33
% 1.90/1.19  #SimpNegUnit  : 0
% 1.90/1.19  #BackRed      : 1
% 1.90/1.19  
% 1.90/1.19  #Partial instantiations: 0
% 1.90/1.19  #Strategies tried      : 1
% 1.90/1.19  
% 1.90/1.19  Timing (in seconds)
% 1.90/1.19  ----------------------
% 1.90/1.20  Preprocessing        : 0.30
% 1.90/1.20  Parsing              : 0.16
% 1.90/1.20  CNF conversion       : 0.02
% 1.90/1.20  Main loop            : 0.14
% 1.90/1.20  Inferencing          : 0.05
% 1.90/1.20  Reduction            : 0.05
% 1.90/1.20  Demodulation         : 0.04
% 1.90/1.20  BG Simplification    : 0.01
% 1.90/1.20  Subsumption          : 0.02
% 1.90/1.20  Abstraction          : 0.01
% 1.90/1.20  MUC search           : 0.00
% 1.90/1.20  Cooper               : 0.00
% 1.90/1.20  Total                : 0.47
% 1.90/1.20  Index Insertion      : 0.00
% 1.90/1.20  Index Deletion       : 0.00
% 1.90/1.20  Index Matching       : 0.00
% 1.90/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
