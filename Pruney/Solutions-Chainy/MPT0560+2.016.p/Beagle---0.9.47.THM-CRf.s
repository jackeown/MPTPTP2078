%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:12 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   41 (  53 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :   58 (  77 expanded)
%              Number of equality atoms :   22 (  29 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B,C] :
            ( r1_tarski(B,C)
           => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_27,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).

tff(c_18,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_20,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [A_1] : v1_relat_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_8] : k2_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_58,plain,(
    ! [B_22,A_23] :
      ( k5_relat_1(B_22,k6_relat_1(A_23)) = B_22
      | ~ r1_tarski(k2_relat_1(B_22),A_23)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_64,plain,(
    ! [A_8,A_23] :
      ( k5_relat_1(k6_relat_1(A_8),k6_relat_1(A_23)) = k6_relat_1(A_8)
      | ~ r1_tarski(A_8,A_23)
      | ~ v1_relat_1(k6_relat_1(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_58])).

tff(c_81,plain,(
    ! [A_27,A_28] :
      ( k5_relat_1(k6_relat_1(A_27),k6_relat_1(A_28)) = k6_relat_1(A_27)
      | ~ r1_tarski(A_27,A_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_64])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k5_relat_1(k6_relat_1(A_11),B_12) = k7_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_90,plain,(
    ! [A_28,A_27] :
      ( k7_relat_1(k6_relat_1(A_28),A_27) = k6_relat_1(A_27)
      | ~ v1_relat_1(k6_relat_1(A_28))
      | ~ r1_tarski(A_27,A_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_14])).

tff(c_106,plain,(
    ! [A_29,A_30] :
      ( k7_relat_1(k6_relat_1(A_29),A_30) = k6_relat_1(A_30)
      | ~ r1_tarski(A_30,A_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_90])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( k2_relat_1(k7_relat_1(B_3,A_2)) = k9_relat_1(B_3,A_2)
      | ~ v1_relat_1(B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_112,plain,(
    ! [A_29,A_30] :
      ( k9_relat_1(k6_relat_1(A_29),A_30) = k2_relat_1(k6_relat_1(A_30))
      | ~ v1_relat_1(k6_relat_1(A_29))
      | ~ r1_tarski(A_30,A_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_4])).

tff(c_118,plain,(
    ! [A_29,A_30] :
      ( k9_relat_1(k6_relat_1(A_29),A_30) = A_30
      | ~ r1_tarski(A_30,A_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10,c_112])).

tff(c_67,plain,(
    ! [B_24,C_25,A_26] :
      ( k9_relat_1(k5_relat_1(B_24,C_25),A_26) = k9_relat_1(C_25,k9_relat_1(B_24,A_26))
      | ~ v1_relat_1(C_25)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_76,plain,(
    ! [B_12,A_11,A_26] :
      ( k9_relat_1(B_12,k9_relat_1(k6_relat_1(A_11),A_26)) = k9_relat_1(k7_relat_1(B_12,A_11),A_26)
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(k6_relat_1(A_11))
      | ~ v1_relat_1(B_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_67])).

tff(c_129,plain,(
    ! [B_33,A_34,A_35] :
      ( k9_relat_1(B_33,k9_relat_1(k6_relat_1(A_34),A_35)) = k9_relat_1(k7_relat_1(B_33,A_34),A_35)
      | ~ v1_relat_1(B_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_76])).

tff(c_192,plain,(
    ! [B_39,A_40,A_41] :
      ( k9_relat_1(k7_relat_1(B_39,A_40),A_41) = k9_relat_1(B_39,A_41)
      | ~ v1_relat_1(B_39)
      | ~ r1_tarski(A_41,A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_129])).

tff(c_16,plain,(
    k9_relat_1(k7_relat_1('#skF_1','#skF_3'),'#skF_2') != k9_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_202,plain,
    ( ~ v1_relat_1('#skF_1')
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_16])).

tff(c_217,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_202])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:11:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.19  
% 1.85/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.20  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.85/1.20  
% 1.85/1.20  %Foreground sorts:
% 1.85/1.20  
% 1.85/1.20  
% 1.85/1.20  %Background operators:
% 1.85/1.20  
% 1.85/1.20  
% 1.85/1.20  %Foreground operators:
% 1.85/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.20  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.85/1.20  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.85/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.85/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.85/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.85/1.20  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.85/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.85/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.85/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.85/1.20  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.85/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.85/1.20  
% 1.85/1.21  tff(f_60, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 1.85/1.21  tff(f_27, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.85/1.21  tff(f_42, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.85/1.21  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 1.85/1.21  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 1.85/1.21  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.85/1.21  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t159_relat_1)).
% 1.85/1.21  tff(c_18, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.85/1.21  tff(c_20, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.85/1.21  tff(c_2, plain, (![A_1]: (v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.85/1.21  tff(c_10, plain, (![A_8]: (k2_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.85/1.21  tff(c_58, plain, (![B_22, A_23]: (k5_relat_1(B_22, k6_relat_1(A_23))=B_22 | ~r1_tarski(k2_relat_1(B_22), A_23) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.85/1.21  tff(c_64, plain, (![A_8, A_23]: (k5_relat_1(k6_relat_1(A_8), k6_relat_1(A_23))=k6_relat_1(A_8) | ~r1_tarski(A_8, A_23) | ~v1_relat_1(k6_relat_1(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_58])).
% 1.85/1.21  tff(c_81, plain, (![A_27, A_28]: (k5_relat_1(k6_relat_1(A_27), k6_relat_1(A_28))=k6_relat_1(A_27) | ~r1_tarski(A_27, A_28))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_64])).
% 1.85/1.21  tff(c_14, plain, (![A_11, B_12]: (k5_relat_1(k6_relat_1(A_11), B_12)=k7_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.85/1.21  tff(c_90, plain, (![A_28, A_27]: (k7_relat_1(k6_relat_1(A_28), A_27)=k6_relat_1(A_27) | ~v1_relat_1(k6_relat_1(A_28)) | ~r1_tarski(A_27, A_28))), inference(superposition, [status(thm), theory('equality')], [c_81, c_14])).
% 1.85/1.21  tff(c_106, plain, (![A_29, A_30]: (k7_relat_1(k6_relat_1(A_29), A_30)=k6_relat_1(A_30) | ~r1_tarski(A_30, A_29))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_90])).
% 1.85/1.21  tff(c_4, plain, (![B_3, A_2]: (k2_relat_1(k7_relat_1(B_3, A_2))=k9_relat_1(B_3, A_2) | ~v1_relat_1(B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.85/1.21  tff(c_112, plain, (![A_29, A_30]: (k9_relat_1(k6_relat_1(A_29), A_30)=k2_relat_1(k6_relat_1(A_30)) | ~v1_relat_1(k6_relat_1(A_29)) | ~r1_tarski(A_30, A_29))), inference(superposition, [status(thm), theory('equality')], [c_106, c_4])).
% 1.85/1.21  tff(c_118, plain, (![A_29, A_30]: (k9_relat_1(k6_relat_1(A_29), A_30)=A_30 | ~r1_tarski(A_30, A_29))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_10, c_112])).
% 1.85/1.21  tff(c_67, plain, (![B_24, C_25, A_26]: (k9_relat_1(k5_relat_1(B_24, C_25), A_26)=k9_relat_1(C_25, k9_relat_1(B_24, A_26)) | ~v1_relat_1(C_25) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.85/1.21  tff(c_76, plain, (![B_12, A_11, A_26]: (k9_relat_1(B_12, k9_relat_1(k6_relat_1(A_11), A_26))=k9_relat_1(k7_relat_1(B_12, A_11), A_26) | ~v1_relat_1(B_12) | ~v1_relat_1(k6_relat_1(A_11)) | ~v1_relat_1(B_12))), inference(superposition, [status(thm), theory('equality')], [c_14, c_67])).
% 1.85/1.21  tff(c_129, plain, (![B_33, A_34, A_35]: (k9_relat_1(B_33, k9_relat_1(k6_relat_1(A_34), A_35))=k9_relat_1(k7_relat_1(B_33, A_34), A_35) | ~v1_relat_1(B_33))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_76])).
% 1.85/1.21  tff(c_192, plain, (![B_39, A_40, A_41]: (k9_relat_1(k7_relat_1(B_39, A_40), A_41)=k9_relat_1(B_39, A_41) | ~v1_relat_1(B_39) | ~r1_tarski(A_41, A_40))), inference(superposition, [status(thm), theory('equality')], [c_118, c_129])).
% 1.85/1.21  tff(c_16, plain, (k9_relat_1(k7_relat_1('#skF_1', '#skF_3'), '#skF_2')!=k9_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.85/1.21  tff(c_202, plain, (~v1_relat_1('#skF_1') | ~r1_tarski('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_192, c_16])).
% 1.85/1.21  tff(c_217, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_202])).
% 1.85/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.21  
% 1.85/1.21  Inference rules
% 1.85/1.21  ----------------------
% 1.85/1.21  #Ref     : 0
% 1.85/1.21  #Sup     : 42
% 1.85/1.21  #Fact    : 0
% 1.85/1.21  #Define  : 0
% 1.85/1.21  #Split   : 0
% 1.85/1.21  #Chain   : 0
% 1.85/1.21  #Close   : 0
% 1.85/1.21  
% 1.85/1.21  Ordering : KBO
% 1.85/1.21  
% 1.85/1.21  Simplification rules
% 1.85/1.21  ----------------------
% 1.85/1.21  #Subsume      : 1
% 1.85/1.21  #Demod        : 16
% 1.85/1.21  #Tautology    : 21
% 1.85/1.21  #SimpNegUnit  : 0
% 1.85/1.21  #BackRed      : 0
% 1.85/1.21  
% 1.85/1.21  #Partial instantiations: 0
% 1.85/1.21  #Strategies tried      : 1
% 1.85/1.21  
% 1.85/1.21  Timing (in seconds)
% 1.85/1.21  ----------------------
% 1.85/1.21  Preprocessing        : 0.26
% 1.85/1.21  Parsing              : 0.14
% 1.85/1.21  CNF conversion       : 0.02
% 1.85/1.21  Main loop            : 0.16
% 1.85/1.21  Inferencing          : 0.08
% 1.85/1.21  Reduction            : 0.04
% 1.85/1.21  Demodulation         : 0.03
% 1.85/1.21  BG Simplification    : 0.01
% 1.85/1.21  Subsumption          : 0.02
% 1.85/1.21  Abstraction          : 0.01
% 1.85/1.21  MUC search           : 0.00
% 1.85/1.21  Cooper               : 0.00
% 1.85/1.21  Total                : 0.44
% 1.85/1.21  Index Insertion      : 0.00
% 1.85/1.21  Index Deletion       : 0.00
% 1.85/1.21  Index Matching       : 0.00
% 1.85/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
