%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:35 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   47 (  62 expanded)
%              Number of leaves         :   25 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   53 (  72 expanded)
%              Number of equality atoms :   26 (  32 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_35,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_10] : v1_relat_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_14] : k2_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_95,plain,(
    ! [A_34,B_35] :
      ( k5_relat_1(k6_relat_1(A_34),B_35) = k7_relat_1(B_35,A_34)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20,plain,(
    ! [A_17] :
      ( k5_relat_1(A_17,k6_relat_1(k2_relat_1(A_17))) = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_109,plain,(
    ! [A_34] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_34))),A_34) = k6_relat_1(A_34)
      | ~ v1_relat_1(k6_relat_1(A_34))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_34)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_20])).

tff(c_126,plain,(
    ! [A_34] : k7_relat_1(k6_relat_1(A_34),A_34) = k6_relat_1(A_34) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_16,c_109])).

tff(c_218,plain,(
    ! [C_43,A_44,B_45] :
      ( k7_relat_1(k7_relat_1(C_43,A_44),B_45) = k7_relat_1(C_43,k3_xboole_0(A_44,B_45))
      | ~ v1_relat_1(C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_236,plain,(
    ! [A_34,B_45] :
      ( k7_relat_1(k6_relat_1(A_34),k3_xboole_0(A_34,B_45)) = k7_relat_1(k6_relat_1(A_34),B_45)
      | ~ v1_relat_1(k6_relat_1(A_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_218])).

tff(c_243,plain,(
    ! [A_46,B_47] : k7_relat_1(k6_relat_1(A_46),k3_xboole_0(A_46,B_47)) = k7_relat_1(k6_relat_1(A_46),B_47) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_236])).

tff(c_144,plain,(
    ! [B_37,A_38] :
      ( k5_relat_1(B_37,k6_relat_1(A_38)) = B_37
      | ~ r1_tarski(k2_relat_1(B_37),A_38)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_147,plain,(
    ! [A_14,A_38] :
      ( k5_relat_1(k6_relat_1(A_14),k6_relat_1(A_38)) = k6_relat_1(A_14)
      | ~ r1_tarski(A_14,A_38)
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_144])).

tff(c_150,plain,(
    ! [A_39,A_40] :
      ( k5_relat_1(k6_relat_1(A_39),k6_relat_1(A_40)) = k6_relat_1(A_39)
      | ~ r1_tarski(A_39,A_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_147])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( k5_relat_1(k6_relat_1(A_18),B_19) = k7_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_156,plain,(
    ! [A_40,A_39] :
      ( k7_relat_1(k6_relat_1(A_40),A_39) = k6_relat_1(A_39)
      | ~ v1_relat_1(k6_relat_1(A_40))
      | ~ r1_tarski(A_39,A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_22])).

tff(c_184,plain,(
    ! [A_40,A_39] :
      ( k7_relat_1(k6_relat_1(A_40),A_39) = k6_relat_1(A_39)
      | ~ r1_tarski(A_39,A_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_156])).

tff(c_252,plain,(
    ! [A_46,B_47] :
      ( k7_relat_1(k6_relat_1(A_46),B_47) = k6_relat_1(k3_xboole_0(A_46,B_47))
      | ~ r1_tarski(k3_xboole_0(A_46,B_47),A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_184])).

tff(c_264,plain,(
    ! [A_46,B_47] : k7_relat_1(k6_relat_1(A_46),B_47) = k6_relat_1(k3_xboole_0(A_46,B_47)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_252])).

tff(c_24,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_101,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_24])).

tff(c_122,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_101])).

tff(c_320,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_122])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:14:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.21  
% 2.00/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.21  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.00/1.21  
% 2.00/1.21  %Foreground sorts:
% 2.00/1.21  
% 2.00/1.21  
% 2.00/1.21  %Background operators:
% 2.00/1.21  
% 2.00/1.21  
% 2.00/1.21  %Foreground operators:
% 2.00/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.21  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.00/1.21  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.00/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.00/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.00/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.00/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.00/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.00/1.21  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.21  tff('#skF_1', type, '#skF_1': $i).
% 2.00/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.00/1.21  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.00/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.00/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.00/1.21  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.00/1.21  
% 2.11/1.22  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.11/1.22  tff(f_35, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.11/1.22  tff(f_43, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.11/1.22  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.11/1.22  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 2.11/1.22  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 2.11/1.22  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 2.11/1.22  tff(f_60, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 2.11/1.22  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.11/1.22  tff(c_10, plain, (![A_10]: (v1_relat_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.11/1.22  tff(c_16, plain, (![A_14]: (k2_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.11/1.22  tff(c_95, plain, (![A_34, B_35]: (k5_relat_1(k6_relat_1(A_34), B_35)=k7_relat_1(B_35, A_34) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.11/1.22  tff(c_20, plain, (![A_17]: (k5_relat_1(A_17, k6_relat_1(k2_relat_1(A_17)))=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.11/1.22  tff(c_109, plain, (![A_34]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_34))), A_34)=k6_relat_1(A_34) | ~v1_relat_1(k6_relat_1(A_34)) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_34)))))), inference(superposition, [status(thm), theory('equality')], [c_95, c_20])).
% 2.11/1.22  tff(c_126, plain, (![A_34]: (k7_relat_1(k6_relat_1(A_34), A_34)=k6_relat_1(A_34))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_16, c_109])).
% 2.11/1.22  tff(c_218, plain, (![C_43, A_44, B_45]: (k7_relat_1(k7_relat_1(C_43, A_44), B_45)=k7_relat_1(C_43, k3_xboole_0(A_44, B_45)) | ~v1_relat_1(C_43))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.11/1.22  tff(c_236, plain, (![A_34, B_45]: (k7_relat_1(k6_relat_1(A_34), k3_xboole_0(A_34, B_45))=k7_relat_1(k6_relat_1(A_34), B_45) | ~v1_relat_1(k6_relat_1(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_126, c_218])).
% 2.11/1.22  tff(c_243, plain, (![A_46, B_47]: (k7_relat_1(k6_relat_1(A_46), k3_xboole_0(A_46, B_47))=k7_relat_1(k6_relat_1(A_46), B_47))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_236])).
% 2.11/1.22  tff(c_144, plain, (![B_37, A_38]: (k5_relat_1(B_37, k6_relat_1(A_38))=B_37 | ~r1_tarski(k2_relat_1(B_37), A_38) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.11/1.22  tff(c_147, plain, (![A_14, A_38]: (k5_relat_1(k6_relat_1(A_14), k6_relat_1(A_38))=k6_relat_1(A_14) | ~r1_tarski(A_14, A_38) | ~v1_relat_1(k6_relat_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_144])).
% 2.11/1.22  tff(c_150, plain, (![A_39, A_40]: (k5_relat_1(k6_relat_1(A_39), k6_relat_1(A_40))=k6_relat_1(A_39) | ~r1_tarski(A_39, A_40))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_147])).
% 2.11/1.22  tff(c_22, plain, (![A_18, B_19]: (k5_relat_1(k6_relat_1(A_18), B_19)=k7_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.11/1.22  tff(c_156, plain, (![A_40, A_39]: (k7_relat_1(k6_relat_1(A_40), A_39)=k6_relat_1(A_39) | ~v1_relat_1(k6_relat_1(A_40)) | ~r1_tarski(A_39, A_40))), inference(superposition, [status(thm), theory('equality')], [c_150, c_22])).
% 2.11/1.22  tff(c_184, plain, (![A_40, A_39]: (k7_relat_1(k6_relat_1(A_40), A_39)=k6_relat_1(A_39) | ~r1_tarski(A_39, A_40))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_156])).
% 2.11/1.22  tff(c_252, plain, (![A_46, B_47]: (k7_relat_1(k6_relat_1(A_46), B_47)=k6_relat_1(k3_xboole_0(A_46, B_47)) | ~r1_tarski(k3_xboole_0(A_46, B_47), A_46))), inference(superposition, [status(thm), theory('equality')], [c_243, c_184])).
% 2.11/1.22  tff(c_264, plain, (![A_46, B_47]: (k7_relat_1(k6_relat_1(A_46), B_47)=k6_relat_1(k3_xboole_0(A_46, B_47)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_252])).
% 2.11/1.22  tff(c_24, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.11/1.22  tff(c_101, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_95, c_24])).
% 2.11/1.22  tff(c_122, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_101])).
% 2.11/1.22  tff(c_320, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_264, c_122])).
% 2.11/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.22  
% 2.11/1.22  Inference rules
% 2.11/1.22  ----------------------
% 2.11/1.22  #Ref     : 0
% 2.11/1.22  #Sup     : 61
% 2.11/1.22  #Fact    : 0
% 2.11/1.22  #Define  : 0
% 2.11/1.22  #Split   : 1
% 2.11/1.22  #Chain   : 0
% 2.11/1.22  #Close   : 0
% 2.11/1.22  
% 2.11/1.22  Ordering : KBO
% 2.11/1.22  
% 2.11/1.22  Simplification rules
% 2.11/1.22  ----------------------
% 2.11/1.22  #Subsume      : 2
% 2.11/1.22  #Demod        : 34
% 2.11/1.22  #Tautology    : 37
% 2.11/1.22  #SimpNegUnit  : 0
% 2.11/1.22  #BackRed      : 3
% 2.11/1.22  
% 2.11/1.22  #Partial instantiations: 0
% 2.11/1.22  #Strategies tried      : 1
% 2.11/1.22  
% 2.11/1.22  Timing (in seconds)
% 2.11/1.22  ----------------------
% 2.11/1.22  Preprocessing        : 0.29
% 2.11/1.22  Parsing              : 0.15
% 2.11/1.22  CNF conversion       : 0.02
% 2.11/1.22  Main loop            : 0.18
% 2.11/1.22  Inferencing          : 0.08
% 2.11/1.22  Reduction            : 0.06
% 2.11/1.23  Demodulation         : 0.05
% 2.11/1.23  BG Simplification    : 0.01
% 2.11/1.23  Subsumption          : 0.02
% 2.11/1.23  Abstraction          : 0.02
% 2.11/1.23  MUC search           : 0.00
% 2.11/1.23  Cooper               : 0.00
% 2.11/1.23  Total                : 0.50
% 2.11/1.23  Index Insertion      : 0.00
% 2.11/1.23  Index Deletion       : 0.00
% 2.11/1.23  Index Matching       : 0.00
% 2.11/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
