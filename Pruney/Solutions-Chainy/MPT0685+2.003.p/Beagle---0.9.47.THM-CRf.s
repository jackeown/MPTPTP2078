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
% DateTime   : Thu Dec  3 10:04:30 EST 2020

% Result     : Theorem 12.49s
% Output     : CNFRefutation 12.49s
% Verified   : 
% Statistics : Number of formulae       :   50 (  63 expanded)
%              Number of leaves         :   27 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :   73 ( 113 expanded)
%              Number of equality atoms :   24 (  39 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k1_funct_1 > k10_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_102,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_85,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_26,plain,(
    ! [A_27] : v1_relat_1('#skF_1'(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k5_relat_1(A_7,B_8))
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( v1_relat_1(k7_relat_1(A_9,B_10))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [B_12,C_14,A_11] :
      ( k7_relat_1(k5_relat_1(B_12,C_14),A_11) = k5_relat_1(k7_relat_1(B_12,A_11),C_14)
      | ~ v1_relat_1(C_14)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_22,plain,(
    ! [A_27] : k1_relat_1('#skF_1'(A_27)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_214,plain,(
    ! [A_66,B_67] :
      ( k10_relat_1(A_66,k1_relat_1(B_67)) = k1_relat_1(k5_relat_1(A_66,B_67))
      | ~ v1_relat_1(B_67)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_232,plain,(
    ! [A_66,A_27] :
      ( k1_relat_1(k5_relat_1(A_66,'#skF_1'(A_27))) = k10_relat_1(A_66,A_27)
      | ~ v1_relat_1('#skF_1'(A_27))
      | ~ v1_relat_1(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_214])).

tff(c_360,plain,(
    ! [A_71,A_72] :
      ( k1_relat_1(k5_relat_1(A_71,'#skF_1'(A_72))) = k10_relat_1(A_71,A_72)
      | ~ v1_relat_1(A_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_232])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_136,plain,(
    ! [B_58,A_59] :
      ( k3_xboole_0(k1_relat_1(B_58),A_59) = k1_relat_1(k7_relat_1(B_58,A_59))
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_156,plain,(
    ! [B_2,B_58] :
      ( k3_xboole_0(B_2,k1_relat_1(B_58)) = k1_relat_1(k7_relat_1(B_58,B_2))
      | ~ v1_relat_1(B_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_136])).

tff(c_2641,plain,(
    ! [A_134,A_135,B_136] :
      ( k1_relat_1(k7_relat_1(k5_relat_1(A_134,'#skF_1'(A_135)),B_136)) = k3_xboole_0(B_136,k10_relat_1(A_134,A_135))
      | ~ v1_relat_1(k5_relat_1(A_134,'#skF_1'(A_135)))
      | ~ v1_relat_1(A_134) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_156])).

tff(c_2702,plain,(
    ! [B_12,A_11,A_135] :
      ( k1_relat_1(k5_relat_1(k7_relat_1(B_12,A_11),'#skF_1'(A_135))) = k3_xboole_0(A_11,k10_relat_1(B_12,A_135))
      | ~ v1_relat_1(k5_relat_1(B_12,'#skF_1'(A_135)))
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1('#skF_1'(A_135))
      | ~ v1_relat_1(B_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_2641])).

tff(c_3353,plain,(
    ! [B_159,A_160,A_161] :
      ( k1_relat_1(k5_relat_1(k7_relat_1(B_159,A_160),'#skF_1'(A_161))) = k3_xboole_0(A_160,k10_relat_1(B_159,A_161))
      | ~ v1_relat_1(k5_relat_1(B_159,'#skF_1'(A_161)))
      | ~ v1_relat_1(B_159) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2702])).

tff(c_238,plain,(
    ! [A_66,A_27] :
      ( k1_relat_1(k5_relat_1(A_66,'#skF_1'(A_27))) = k10_relat_1(A_66,A_27)
      | ~ v1_relat_1(A_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_232])).

tff(c_16586,plain,(
    ! [A_266,B_267,A_268] :
      ( k3_xboole_0(A_266,k10_relat_1(B_267,A_268)) = k10_relat_1(k7_relat_1(B_267,A_266),A_268)
      | ~ v1_relat_1(k7_relat_1(B_267,A_266))
      | ~ v1_relat_1(k5_relat_1(B_267,'#skF_1'(A_268)))
      | ~ v1_relat_1(B_267) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3353,c_238])).

tff(c_16592,plain,(
    ! [B_269,A_270,A_271] :
      ( k3_xboole_0(B_269,k10_relat_1(A_270,A_271)) = k10_relat_1(k7_relat_1(A_270,B_269),A_271)
      | ~ v1_relat_1(k5_relat_1(A_270,'#skF_1'(A_271)))
      | ~ v1_relat_1(A_270) ) ),
    inference(resolution,[status(thm)],[c_10,c_16586])).

tff(c_16598,plain,(
    ! [B_269,A_7,A_271] :
      ( k3_xboole_0(B_269,k10_relat_1(A_7,A_271)) = k10_relat_1(k7_relat_1(A_7,B_269),A_271)
      | ~ v1_relat_1('#skF_1'(A_271))
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_8,c_16592])).

tff(c_16605,plain,(
    ! [B_272,A_273,A_274] :
      ( k3_xboole_0(B_272,k10_relat_1(A_273,A_274)) = k10_relat_1(k7_relat_1(A_273,B_272),A_274)
      | ~ v1_relat_1(A_273) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_16598])).

tff(c_36,plain,(
    k3_xboole_0('#skF_3',k10_relat_1('#skF_5','#skF_4')) != k10_relat_1(k7_relat_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_16677,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_16605,c_36])).

tff(c_16733,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_16677])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:13:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.49/4.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.49/4.59  
% 12.49/4.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.49/4.59  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k1_funct_1 > k10_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 12.49/4.59  
% 12.49/4.59  %Foreground sorts:
% 12.49/4.59  
% 12.49/4.59  
% 12.49/4.59  %Background operators:
% 12.49/4.59  
% 12.49/4.59  
% 12.49/4.59  %Foreground operators:
% 12.49/4.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.49/4.59  tff('#skF_2', type, '#skF_2': $i > $i).
% 12.49/4.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.49/4.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.49/4.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.49/4.59  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 12.49/4.59  tff('#skF_1', type, '#skF_1': $i > $i).
% 12.49/4.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.49/4.59  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 12.49/4.59  tff('#skF_5', type, '#skF_5': $i).
% 12.49/4.59  tff('#skF_3', type, '#skF_3': $i).
% 12.49/4.59  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 12.49/4.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.49/4.59  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 12.49/4.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.49/4.59  tff('#skF_4', type, '#skF_4': $i).
% 12.49/4.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.49/4.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.49/4.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.49/4.59  
% 12.49/4.60  tff(f_102, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 12.49/4.60  tff(f_85, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 12.49/4.60  tff(f_39, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 12.49/4.60  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 12.49/4.60  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_relat_1)).
% 12.49/4.60  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 12.49/4.60  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 12.49/4.60  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 12.49/4.60  tff(c_38, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_102])).
% 12.49/4.60  tff(c_26, plain, (![A_27]: (v1_relat_1('#skF_1'(A_27)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.49/4.60  tff(c_8, plain, (![A_7, B_8]: (v1_relat_1(k5_relat_1(A_7, B_8)) | ~v1_relat_1(B_8) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.49/4.60  tff(c_10, plain, (![A_9, B_10]: (v1_relat_1(k7_relat_1(A_9, B_10)) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.49/4.60  tff(c_12, plain, (![B_12, C_14, A_11]: (k7_relat_1(k5_relat_1(B_12, C_14), A_11)=k5_relat_1(k7_relat_1(B_12, A_11), C_14) | ~v1_relat_1(C_14) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.49/4.60  tff(c_22, plain, (![A_27]: (k1_relat_1('#skF_1'(A_27))=A_27)), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.49/4.60  tff(c_214, plain, (![A_66, B_67]: (k10_relat_1(A_66, k1_relat_1(B_67))=k1_relat_1(k5_relat_1(A_66, B_67)) | ~v1_relat_1(B_67) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.49/4.60  tff(c_232, plain, (![A_66, A_27]: (k1_relat_1(k5_relat_1(A_66, '#skF_1'(A_27)))=k10_relat_1(A_66, A_27) | ~v1_relat_1('#skF_1'(A_27)) | ~v1_relat_1(A_66))), inference(superposition, [status(thm), theory('equality')], [c_22, c_214])).
% 12.49/4.60  tff(c_360, plain, (![A_71, A_72]: (k1_relat_1(k5_relat_1(A_71, '#skF_1'(A_72)))=k10_relat_1(A_71, A_72) | ~v1_relat_1(A_71))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_232])).
% 12.49/4.60  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.49/4.60  tff(c_136, plain, (![B_58, A_59]: (k3_xboole_0(k1_relat_1(B_58), A_59)=k1_relat_1(k7_relat_1(B_58, A_59)) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_73])).
% 12.49/4.60  tff(c_156, plain, (![B_2, B_58]: (k3_xboole_0(B_2, k1_relat_1(B_58))=k1_relat_1(k7_relat_1(B_58, B_2)) | ~v1_relat_1(B_58))), inference(superposition, [status(thm), theory('equality')], [c_2, c_136])).
% 12.49/4.60  tff(c_2641, plain, (![A_134, A_135, B_136]: (k1_relat_1(k7_relat_1(k5_relat_1(A_134, '#skF_1'(A_135)), B_136))=k3_xboole_0(B_136, k10_relat_1(A_134, A_135)) | ~v1_relat_1(k5_relat_1(A_134, '#skF_1'(A_135))) | ~v1_relat_1(A_134))), inference(superposition, [status(thm), theory('equality')], [c_360, c_156])).
% 12.49/4.60  tff(c_2702, plain, (![B_12, A_11, A_135]: (k1_relat_1(k5_relat_1(k7_relat_1(B_12, A_11), '#skF_1'(A_135)))=k3_xboole_0(A_11, k10_relat_1(B_12, A_135)) | ~v1_relat_1(k5_relat_1(B_12, '#skF_1'(A_135))) | ~v1_relat_1(B_12) | ~v1_relat_1('#skF_1'(A_135)) | ~v1_relat_1(B_12))), inference(superposition, [status(thm), theory('equality')], [c_12, c_2641])).
% 12.49/4.60  tff(c_3353, plain, (![B_159, A_160, A_161]: (k1_relat_1(k5_relat_1(k7_relat_1(B_159, A_160), '#skF_1'(A_161)))=k3_xboole_0(A_160, k10_relat_1(B_159, A_161)) | ~v1_relat_1(k5_relat_1(B_159, '#skF_1'(A_161))) | ~v1_relat_1(B_159))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2702])).
% 12.49/4.60  tff(c_238, plain, (![A_66, A_27]: (k1_relat_1(k5_relat_1(A_66, '#skF_1'(A_27)))=k10_relat_1(A_66, A_27) | ~v1_relat_1(A_66))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_232])).
% 12.49/4.60  tff(c_16586, plain, (![A_266, B_267, A_268]: (k3_xboole_0(A_266, k10_relat_1(B_267, A_268))=k10_relat_1(k7_relat_1(B_267, A_266), A_268) | ~v1_relat_1(k7_relat_1(B_267, A_266)) | ~v1_relat_1(k5_relat_1(B_267, '#skF_1'(A_268))) | ~v1_relat_1(B_267))), inference(superposition, [status(thm), theory('equality')], [c_3353, c_238])).
% 12.49/4.60  tff(c_16592, plain, (![B_269, A_270, A_271]: (k3_xboole_0(B_269, k10_relat_1(A_270, A_271))=k10_relat_1(k7_relat_1(A_270, B_269), A_271) | ~v1_relat_1(k5_relat_1(A_270, '#skF_1'(A_271))) | ~v1_relat_1(A_270))), inference(resolution, [status(thm)], [c_10, c_16586])).
% 12.49/4.60  tff(c_16598, plain, (![B_269, A_7, A_271]: (k3_xboole_0(B_269, k10_relat_1(A_7, A_271))=k10_relat_1(k7_relat_1(A_7, B_269), A_271) | ~v1_relat_1('#skF_1'(A_271)) | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_8, c_16592])).
% 12.49/4.60  tff(c_16605, plain, (![B_272, A_273, A_274]: (k3_xboole_0(B_272, k10_relat_1(A_273, A_274))=k10_relat_1(k7_relat_1(A_273, B_272), A_274) | ~v1_relat_1(A_273))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_16598])).
% 12.49/4.60  tff(c_36, plain, (k3_xboole_0('#skF_3', k10_relat_1('#skF_5', '#skF_4'))!=k10_relat_1(k7_relat_1('#skF_5', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_102])).
% 12.49/4.60  tff(c_16677, plain, (~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_16605, c_36])).
% 12.49/4.60  tff(c_16733, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_16677])).
% 12.49/4.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.49/4.60  
% 12.49/4.60  Inference rules
% 12.49/4.60  ----------------------
% 12.49/4.60  #Ref     : 5
% 12.49/4.60  #Sup     : 4579
% 12.49/4.60  #Fact    : 0
% 12.49/4.60  #Define  : 0
% 12.49/4.60  #Split   : 0
% 12.49/4.60  #Chain   : 0
% 12.49/4.60  #Close   : 0
% 12.49/4.61  
% 12.49/4.61  Ordering : KBO
% 12.49/4.61  
% 12.49/4.61  Simplification rules
% 12.49/4.61  ----------------------
% 12.49/4.61  #Subsume      : 602
% 12.49/4.61  #Demod        : 3850
% 12.49/4.61  #Tautology    : 590
% 12.49/4.61  #SimpNegUnit  : 0
% 12.49/4.61  #BackRed      : 0
% 12.49/4.61  
% 12.49/4.61  #Partial instantiations: 0
% 12.49/4.61  #Strategies tried      : 1
% 12.49/4.61  
% 12.49/4.61  Timing (in seconds)
% 12.49/4.61  ----------------------
% 12.49/4.61  Preprocessing        : 0.32
% 12.49/4.61  Parsing              : 0.18
% 12.49/4.61  CNF conversion       : 0.02
% 12.49/4.61  Main loop            : 3.47
% 12.49/4.61  Inferencing          : 0.99
% 12.49/4.61  Reduction            : 1.36
% 12.49/4.61  Demodulation         : 1.10
% 12.49/4.61  BG Simplification    : 0.20
% 12.49/4.61  Subsumption          : 0.78
% 12.49/4.61  Abstraction          : 0.29
% 12.49/4.61  MUC search           : 0.00
% 12.49/4.61  Cooper               : 0.00
% 12.49/4.61  Total                : 3.82
% 12.49/4.61  Index Insertion      : 0.00
% 12.49/4.61  Index Deletion       : 0.00
% 12.49/4.61  Index Matching       : 0.00
% 12.49/4.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
