%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:35 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   44 (  57 expanded)
%              Number of leaves         :   25 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 (  67 expanded)
%              Number of equality atoms :   23 (  30 expanded)
%              Maximal formula depth    :    7 (   4 average)
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

tff(f_35,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_43,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_10,plain,(
    ! [A_10] : v1_relat_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_14] : k1_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_19] :
      ( k7_relat_1(A_19,k1_relat_1(A_19)) = A_19
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_139,plain,(
    ! [C_40,A_41,B_42] :
      ( k7_relat_1(k7_relat_1(C_40,A_41),B_42) = k7_relat_1(C_40,k3_xboole_0(A_41,B_42))
      | ~ v1_relat_1(C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_208,plain,(
    ! [A_45,B_46] :
      ( k7_relat_1(A_45,k3_xboole_0(k1_relat_1(A_45),B_46)) = k7_relat_1(A_45,B_46)
      | ~ v1_relat_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_139])).

tff(c_16,plain,(
    ! [A_14] : k2_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_109,plain,(
    ! [B_36,A_37] :
      ( k5_relat_1(B_36,k6_relat_1(A_37)) = B_36
      | ~ r1_tarski(k2_relat_1(B_36),A_37)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_112,plain,(
    ! [A_14,A_37] :
      ( k5_relat_1(k6_relat_1(A_14),k6_relat_1(A_37)) = k6_relat_1(A_14)
      | ~ r1_tarski(A_14,A_37)
      | ~ v1_relat_1(k6_relat_1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_109])).

tff(c_115,plain,(
    ! [A_38,A_39] :
      ( k5_relat_1(k6_relat_1(A_38),k6_relat_1(A_39)) = k6_relat_1(A_38)
      | ~ r1_tarski(A_38,A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_112])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( k5_relat_1(k6_relat_1(A_17),B_18) = k7_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_124,plain,(
    ! [A_39,A_38] :
      ( k7_relat_1(k6_relat_1(A_39),A_38) = k6_relat_1(A_38)
      | ~ v1_relat_1(k6_relat_1(A_39))
      | ~ r1_tarski(A_38,A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_20])).

tff(c_134,plain,(
    ! [A_39,A_38] :
      ( k7_relat_1(k6_relat_1(A_39),A_38) = k6_relat_1(A_38)
      | ~ r1_tarski(A_38,A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_124])).

tff(c_215,plain,(
    ! [A_39,B_46] :
      ( k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_39)),B_46)) = k7_relat_1(k6_relat_1(A_39),B_46)
      | ~ r1_tarski(k3_xboole_0(k1_relat_1(k6_relat_1(A_39)),B_46),A_39)
      | ~ v1_relat_1(k6_relat_1(A_39))
      | ~ v1_relat_1(k6_relat_1(A_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_134])).

tff(c_239,plain,(
    ! [A_39,B_46] : k7_relat_1(k6_relat_1(A_39),B_46) = k6_relat_1(k3_xboole_0(A_39,B_46)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_2,c_14,c_14,c_215])).

tff(c_24,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_97,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_24])).

tff(c_99,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_97])).

tff(c_248,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_99])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:17:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.19  
% 1.91/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.19  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.91/1.19  
% 1.91/1.19  %Foreground sorts:
% 1.91/1.19  
% 1.91/1.19  
% 1.91/1.19  %Background operators:
% 1.91/1.19  
% 1.91/1.19  
% 1.91/1.19  %Foreground operators:
% 1.91/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.19  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.91/1.19  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.91/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.91/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.91/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.91/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.91/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.91/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.91/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.91/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.91/1.19  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.91/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.91/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.91/1.19  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.91/1.19  
% 1.91/1.20  tff(f_35, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.91/1.20  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.91/1.20  tff(f_43, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.91/1.20  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 1.91/1.20  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 1.91/1.20  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 1.91/1.20  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 1.91/1.20  tff(f_60, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 1.91/1.20  tff(c_10, plain, (![A_10]: (v1_relat_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.91/1.20  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.91/1.20  tff(c_14, plain, (![A_14]: (k1_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.91/1.20  tff(c_22, plain, (![A_19]: (k7_relat_1(A_19, k1_relat_1(A_19))=A_19 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.91/1.20  tff(c_139, plain, (![C_40, A_41, B_42]: (k7_relat_1(k7_relat_1(C_40, A_41), B_42)=k7_relat_1(C_40, k3_xboole_0(A_41, B_42)) | ~v1_relat_1(C_40))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.91/1.20  tff(c_208, plain, (![A_45, B_46]: (k7_relat_1(A_45, k3_xboole_0(k1_relat_1(A_45), B_46))=k7_relat_1(A_45, B_46) | ~v1_relat_1(A_45) | ~v1_relat_1(A_45))), inference(superposition, [status(thm), theory('equality')], [c_22, c_139])).
% 1.91/1.20  tff(c_16, plain, (![A_14]: (k2_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.91/1.20  tff(c_109, plain, (![B_36, A_37]: (k5_relat_1(B_36, k6_relat_1(A_37))=B_36 | ~r1_tarski(k2_relat_1(B_36), A_37) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.91/1.20  tff(c_112, plain, (![A_14, A_37]: (k5_relat_1(k6_relat_1(A_14), k6_relat_1(A_37))=k6_relat_1(A_14) | ~r1_tarski(A_14, A_37) | ~v1_relat_1(k6_relat_1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_109])).
% 1.91/1.20  tff(c_115, plain, (![A_38, A_39]: (k5_relat_1(k6_relat_1(A_38), k6_relat_1(A_39))=k6_relat_1(A_38) | ~r1_tarski(A_38, A_39))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_112])).
% 1.91/1.20  tff(c_20, plain, (![A_17, B_18]: (k5_relat_1(k6_relat_1(A_17), B_18)=k7_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.91/1.20  tff(c_124, plain, (![A_39, A_38]: (k7_relat_1(k6_relat_1(A_39), A_38)=k6_relat_1(A_38) | ~v1_relat_1(k6_relat_1(A_39)) | ~r1_tarski(A_38, A_39))), inference(superposition, [status(thm), theory('equality')], [c_115, c_20])).
% 1.91/1.20  tff(c_134, plain, (![A_39, A_38]: (k7_relat_1(k6_relat_1(A_39), A_38)=k6_relat_1(A_38) | ~r1_tarski(A_38, A_39))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_124])).
% 1.91/1.20  tff(c_215, plain, (![A_39, B_46]: (k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_39)), B_46))=k7_relat_1(k6_relat_1(A_39), B_46) | ~r1_tarski(k3_xboole_0(k1_relat_1(k6_relat_1(A_39)), B_46), A_39) | ~v1_relat_1(k6_relat_1(A_39)) | ~v1_relat_1(k6_relat_1(A_39)))), inference(superposition, [status(thm), theory('equality')], [c_208, c_134])).
% 1.91/1.20  tff(c_239, plain, (![A_39, B_46]: (k7_relat_1(k6_relat_1(A_39), B_46)=k6_relat_1(k3_xboole_0(A_39, B_46)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_2, c_14, c_14, c_215])).
% 1.91/1.20  tff(c_24, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.91/1.20  tff(c_97, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_20, c_24])).
% 1.91/1.20  tff(c_99, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_97])).
% 1.91/1.20  tff(c_248, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_239, c_99])).
% 1.91/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.20  
% 1.91/1.20  Inference rules
% 1.91/1.20  ----------------------
% 1.91/1.20  #Ref     : 0
% 1.91/1.20  #Sup     : 48
% 1.91/1.20  #Fact    : 0
% 1.91/1.20  #Define  : 0
% 1.91/1.20  #Split   : 1
% 1.91/1.20  #Chain   : 0
% 1.91/1.20  #Close   : 0
% 1.91/1.20  
% 1.91/1.20  Ordering : KBO
% 1.91/1.20  
% 1.91/1.20  Simplification rules
% 1.91/1.20  ----------------------
% 1.91/1.20  #Subsume      : 2
% 1.91/1.20  #Demod        : 27
% 1.91/1.20  #Tautology    : 28
% 1.91/1.20  #SimpNegUnit  : 0
% 1.91/1.20  #BackRed      : 2
% 1.91/1.20  
% 1.91/1.20  #Partial instantiations: 0
% 1.91/1.20  #Strategies tried      : 1
% 1.91/1.20  
% 1.91/1.20  Timing (in seconds)
% 1.91/1.20  ----------------------
% 1.91/1.20  Preprocessing        : 0.28
% 1.91/1.20  Parsing              : 0.15
% 1.91/1.20  CNF conversion       : 0.01
% 1.91/1.20  Main loop            : 0.15
% 1.91/1.20  Inferencing          : 0.06
% 1.91/1.20  Reduction            : 0.05
% 1.91/1.20  Demodulation         : 0.04
% 1.91/1.20  BG Simplification    : 0.01
% 1.91/1.20  Subsumption          : 0.02
% 1.91/1.20  Abstraction          : 0.01
% 1.91/1.20  MUC search           : 0.00
% 1.91/1.20  Cooper               : 0.00
% 1.91/1.20  Total                : 0.46
% 1.91/1.20  Index Insertion      : 0.00
% 1.91/1.21  Index Deletion       : 0.00
% 1.91/1.21  Index Matching       : 0.00
% 1.91/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
