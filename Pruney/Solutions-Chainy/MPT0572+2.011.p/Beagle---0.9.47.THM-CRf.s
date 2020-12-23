%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:49 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   55 (  76 expanded)
%              Number of leaves         :   24 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 (  89 expanded)
%              Number of equality atoms :   17 (  26 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k10_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_78,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k4_xboole_0(A_34,B_35)) = k3_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_87,plain,(
    ! [A_34,B_35] : r1_tarski(k3_xboole_0(A_34,B_35),A_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_6])).

tff(c_10,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_208,plain,(
    ! [A_52,B_53] : k4_xboole_0(A_52,k3_xboole_0(A_52,B_53)) = k3_xboole_0(A_52,k4_xboole_0(A_52,B_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_10])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( k2_xboole_0(A_8,k4_xboole_0(B_9,A_8)) = B_9
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_220,plain,(
    ! [A_52,B_53] :
      ( k2_xboole_0(k3_xboole_0(A_52,B_53),k3_xboole_0(A_52,k4_xboole_0(A_52,B_53))) = A_52
      | ~ r1_tarski(k3_xboole_0(A_52,B_53),A_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_8])).

tff(c_239,plain,(
    ! [A_52,B_53] : k2_xboole_0(k3_xboole_0(A_52,B_53),k3_xboole_0(A_52,k4_xboole_0(A_52,B_53))) = A_52 ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_220])).

tff(c_423,plain,(
    ! [C_72,A_73,B_74] :
      ( k2_xboole_0(k10_relat_1(C_72,A_73),k10_relat_1(C_72,B_74)) = k10_relat_1(C_72,k2_xboole_0(A_73,B_74))
      | ~ v1_relat_1(C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_557,plain,(
    ! [C_81,A_82,B_83] :
      ( r1_tarski(k10_relat_1(C_81,A_82),k10_relat_1(C_81,k2_xboole_0(A_82,B_83)))
      | ~ v1_relat_1(C_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_12])).

tff(c_586,plain,(
    ! [C_87,A_88,B_89] :
      ( r1_tarski(k10_relat_1(C_87,k3_xboole_0(A_88,B_89)),k10_relat_1(C_87,A_88))
      | ~ v1_relat_1(C_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_557])).

tff(c_593,plain,(
    ! [C_90,B_91,A_92] :
      ( r1_tarski(k10_relat_1(C_90,k3_xboole_0(B_91,A_92)),k10_relat_1(C_90,A_92))
      | ~ v1_relat_1(C_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_586])).

tff(c_122,plain,(
    ! [A_43,B_44] :
      ( k2_xboole_0(A_43,k4_xboole_0(B_44,A_43)) = B_44
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_134,plain,(
    ! [A_10,B_11] :
      ( k2_xboole_0(k4_xboole_0(A_10,B_11),k3_xboole_0(A_10,B_11)) = A_10
      | ~ r1_tarski(k4_xboole_0(A_10,B_11),A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_122])).

tff(c_139,plain,(
    ! [A_45,B_46] : k2_xboole_0(k4_xboole_0(A_45,B_46),k3_xboole_0(A_45,B_46)) = A_45 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_134])).

tff(c_151,plain,(
    ! [A_10,B_11] : k2_xboole_0(k3_xboole_0(A_10,B_11),k3_xboole_0(A_10,k4_xboole_0(A_10,B_11))) = A_10 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_139])).

tff(c_320,plain,(
    ! [C_58,A_59,B_60] :
      ( k2_xboole_0(k10_relat_1(C_58,A_59),k10_relat_1(C_58,B_60)) = k10_relat_1(C_58,k2_xboole_0(A_59,B_60))
      | ~ v1_relat_1(C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_378,plain,(
    ! [C_63,A_64,B_65] :
      ( r1_tarski(k10_relat_1(C_63,A_64),k10_relat_1(C_63,k2_xboole_0(A_64,B_65)))
      | ~ v1_relat_1(C_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_12])).

tff(c_407,plain,(
    ! [C_69,A_70,B_71] :
      ( r1_tarski(k10_relat_1(C_69,k3_xboole_0(A_70,B_71)),k10_relat_1(C_69,A_70))
      | ~ v1_relat_1(C_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_378])).

tff(c_196,plain,(
    ! [A_49,B_50,C_51] :
      ( r1_tarski(A_49,k3_xboole_0(B_50,C_51))
      | ~ r1_tarski(A_49,C_51)
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_206,plain,
    ( ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_196,c_22])).

tff(c_243,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_206])).

tff(c_410,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_407,c_243])).

tff(c_420,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_410])).

tff(c_421,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_206])).

tff(c_596,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_593,c_421])).

tff(c_606,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_596])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:44:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.34  
% 2.41/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.34  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 2.41/1.34  
% 2.41/1.34  %Foreground sorts:
% 2.41/1.34  
% 2.41/1.34  
% 2.41/1.34  %Background operators:
% 2.41/1.34  
% 2.41/1.34  
% 2.41/1.34  %Foreground operators:
% 2.41/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.41/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.41/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.41/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.41/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.41/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.41/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.41/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.41/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.34  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.41/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.41/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.41/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.41/1.34  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.41/1.34  
% 2.41/1.35  tff(f_58, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k10_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_relat_1)).
% 2.41/1.35  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.41/1.35  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.41/1.35  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.41/1.35  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 2.41/1.35  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_relat_1)).
% 2.41/1.35  tff(f_43, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.41/1.35  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.41/1.35  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.41/1.35  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.41/1.35  tff(c_78, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k4_xboole_0(A_34, B_35))=k3_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.41/1.35  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.41/1.35  tff(c_87, plain, (![A_34, B_35]: (r1_tarski(k3_xboole_0(A_34, B_35), A_34))), inference(superposition, [status(thm), theory('equality')], [c_78, c_6])).
% 2.41/1.35  tff(c_10, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.41/1.35  tff(c_208, plain, (![A_52, B_53]: (k4_xboole_0(A_52, k3_xboole_0(A_52, B_53))=k3_xboole_0(A_52, k4_xboole_0(A_52, B_53)))), inference(superposition, [status(thm), theory('equality')], [c_78, c_10])).
% 2.41/1.35  tff(c_8, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k4_xboole_0(B_9, A_8))=B_9 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.41/1.35  tff(c_220, plain, (![A_52, B_53]: (k2_xboole_0(k3_xboole_0(A_52, B_53), k3_xboole_0(A_52, k4_xboole_0(A_52, B_53)))=A_52 | ~r1_tarski(k3_xboole_0(A_52, B_53), A_52))), inference(superposition, [status(thm), theory('equality')], [c_208, c_8])).
% 2.41/1.35  tff(c_239, plain, (![A_52, B_53]: (k2_xboole_0(k3_xboole_0(A_52, B_53), k3_xboole_0(A_52, k4_xboole_0(A_52, B_53)))=A_52)), inference(demodulation, [status(thm), theory('equality')], [c_87, c_220])).
% 2.41/1.35  tff(c_423, plain, (![C_72, A_73, B_74]: (k2_xboole_0(k10_relat_1(C_72, A_73), k10_relat_1(C_72, B_74))=k10_relat_1(C_72, k2_xboole_0(A_73, B_74)) | ~v1_relat_1(C_72))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.41/1.35  tff(c_12, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.41/1.35  tff(c_557, plain, (![C_81, A_82, B_83]: (r1_tarski(k10_relat_1(C_81, A_82), k10_relat_1(C_81, k2_xboole_0(A_82, B_83))) | ~v1_relat_1(C_81))), inference(superposition, [status(thm), theory('equality')], [c_423, c_12])).
% 2.41/1.35  tff(c_586, plain, (![C_87, A_88, B_89]: (r1_tarski(k10_relat_1(C_87, k3_xboole_0(A_88, B_89)), k10_relat_1(C_87, A_88)) | ~v1_relat_1(C_87))), inference(superposition, [status(thm), theory('equality')], [c_239, c_557])).
% 2.41/1.35  tff(c_593, plain, (![C_90, B_91, A_92]: (r1_tarski(k10_relat_1(C_90, k3_xboole_0(B_91, A_92)), k10_relat_1(C_90, A_92)) | ~v1_relat_1(C_90))), inference(superposition, [status(thm), theory('equality')], [c_2, c_586])).
% 2.41/1.35  tff(c_122, plain, (![A_43, B_44]: (k2_xboole_0(A_43, k4_xboole_0(B_44, A_43))=B_44 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.41/1.35  tff(c_134, plain, (![A_10, B_11]: (k2_xboole_0(k4_xboole_0(A_10, B_11), k3_xboole_0(A_10, B_11))=A_10 | ~r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(superposition, [status(thm), theory('equality')], [c_10, c_122])).
% 2.41/1.35  tff(c_139, plain, (![A_45, B_46]: (k2_xboole_0(k4_xboole_0(A_45, B_46), k3_xboole_0(A_45, B_46))=A_45)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_134])).
% 2.41/1.35  tff(c_151, plain, (![A_10, B_11]: (k2_xboole_0(k3_xboole_0(A_10, B_11), k3_xboole_0(A_10, k4_xboole_0(A_10, B_11)))=A_10)), inference(superposition, [status(thm), theory('equality')], [c_10, c_139])).
% 2.41/1.35  tff(c_320, plain, (![C_58, A_59, B_60]: (k2_xboole_0(k10_relat_1(C_58, A_59), k10_relat_1(C_58, B_60))=k10_relat_1(C_58, k2_xboole_0(A_59, B_60)) | ~v1_relat_1(C_58))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.41/1.35  tff(c_378, plain, (![C_63, A_64, B_65]: (r1_tarski(k10_relat_1(C_63, A_64), k10_relat_1(C_63, k2_xboole_0(A_64, B_65))) | ~v1_relat_1(C_63))), inference(superposition, [status(thm), theory('equality')], [c_320, c_12])).
% 2.41/1.35  tff(c_407, plain, (![C_69, A_70, B_71]: (r1_tarski(k10_relat_1(C_69, k3_xboole_0(A_70, B_71)), k10_relat_1(C_69, A_70)) | ~v1_relat_1(C_69))), inference(superposition, [status(thm), theory('equality')], [c_151, c_378])).
% 2.41/1.35  tff(c_196, plain, (![A_49, B_50, C_51]: (r1_tarski(A_49, k3_xboole_0(B_50, C_51)) | ~r1_tarski(A_49, C_51) | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.41/1.35  tff(c_22, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.41/1.35  tff(c_206, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_196, c_22])).
% 2.41/1.35  tff(c_243, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_206])).
% 2.41/1.35  tff(c_410, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_407, c_243])).
% 2.41/1.35  tff(c_420, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_410])).
% 2.41/1.35  tff(c_421, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_206])).
% 2.41/1.35  tff(c_596, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_593, c_421])).
% 2.41/1.35  tff(c_606, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_596])).
% 2.41/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.35  
% 2.41/1.35  Inference rules
% 2.41/1.35  ----------------------
% 2.41/1.35  #Ref     : 0
% 2.41/1.35  #Sup     : 143
% 2.41/1.35  #Fact    : 0
% 2.41/1.35  #Define  : 0
% 2.41/1.35  #Split   : 1
% 2.41/1.35  #Chain   : 0
% 2.41/1.35  #Close   : 0
% 2.41/1.35  
% 2.41/1.35  Ordering : KBO
% 2.41/1.35  
% 2.41/1.35  Simplification rules
% 2.41/1.35  ----------------------
% 2.41/1.35  #Subsume      : 4
% 2.41/1.35  #Demod        : 50
% 2.41/1.35  #Tautology    : 85
% 2.41/1.35  #SimpNegUnit  : 0
% 2.41/1.35  #BackRed      : 0
% 2.41/1.35  
% 2.41/1.35  #Partial instantiations: 0
% 2.41/1.35  #Strategies tried      : 1
% 2.41/1.35  
% 2.41/1.35  Timing (in seconds)
% 2.41/1.35  ----------------------
% 2.41/1.36  Preprocessing        : 0.30
% 2.41/1.36  Parsing              : 0.16
% 2.41/1.36  CNF conversion       : 0.02
% 2.41/1.36  Main loop            : 0.29
% 2.41/1.36  Inferencing          : 0.11
% 2.41/1.36  Reduction            : 0.10
% 2.41/1.36  Demodulation         : 0.08
% 2.41/1.36  BG Simplification    : 0.01
% 2.41/1.36  Subsumption          : 0.05
% 2.41/1.36  Abstraction          : 0.02
% 2.41/1.36  MUC search           : 0.00
% 2.41/1.36  Cooper               : 0.00
% 2.41/1.36  Total                : 0.61
% 2.41/1.36  Index Insertion      : 0.00
% 2.41/1.36  Index Deletion       : 0.00
% 2.41/1.36  Index Matching       : 0.00
% 2.41/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
