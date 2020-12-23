%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:12 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   45 (  59 expanded)
%              Number of leaves         :   23 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   63 (  84 expanded)
%              Number of equality atoms :   25 (  32 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

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

tff(f_64,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B,C] :
            ( r1_tarski(B,C)
           => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_27,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).

tff(c_20,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [A_1] : v1_relat_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_12] : k2_relat_1(k6_relat_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_60,plain,(
    ! [B_24,A_25] :
      ( k5_relat_1(B_24,k6_relat_1(A_25)) = k8_relat_1(A_25,B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( k5_relat_1(k6_relat_1(A_13),B_14) = k7_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_67,plain,(
    ! [A_25,A_13] :
      ( k8_relat_1(A_25,k6_relat_1(A_13)) = k7_relat_1(k6_relat_1(A_25),A_13)
      | ~ v1_relat_1(k6_relat_1(A_25))
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_16])).

tff(c_77,plain,(
    ! [A_25,A_13] : k8_relat_1(A_25,k6_relat_1(A_13)) = k7_relat_1(k6_relat_1(A_25),A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_67])).

tff(c_81,plain,(
    ! [A_26,B_27] :
      ( k8_relat_1(A_26,B_27) = B_27
      | ~ r1_tarski(k2_relat_1(B_27),A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_87,plain,(
    ! [A_26,A_12] :
      ( k8_relat_1(A_26,k6_relat_1(A_12)) = k6_relat_1(A_12)
      | ~ r1_tarski(A_12,A_26)
      | ~ v1_relat_1(k6_relat_1(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_81])).

tff(c_89,plain,(
    ! [A_26,A_12] :
      ( k8_relat_1(A_26,k6_relat_1(A_12)) = k6_relat_1(A_12)
      | ~ r1_tarski(A_12,A_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_87])).

tff(c_101,plain,(
    ! [A_30,A_31] :
      ( k7_relat_1(k6_relat_1(A_30),A_31) = k6_relat_1(A_31)
      | ~ r1_tarski(A_31,A_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_89])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( k2_relat_1(k7_relat_1(B_7,A_6)) = k9_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_107,plain,(
    ! [A_30,A_31] :
      ( k9_relat_1(k6_relat_1(A_30),A_31) = k2_relat_1(k6_relat_1(A_31))
      | ~ v1_relat_1(k6_relat_1(A_30))
      | ~ r1_tarski(A_31,A_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_8])).

tff(c_113,plain,(
    ! [A_30,A_31] :
      ( k9_relat_1(k6_relat_1(A_30),A_31) = A_31
      | ~ r1_tarski(A_31,A_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14,c_107])).

tff(c_124,plain,(
    ! [B_34,C_35,A_36] :
      ( k9_relat_1(k5_relat_1(B_34,C_35),A_36) = k9_relat_1(C_35,k9_relat_1(B_34,A_36))
      | ~ v1_relat_1(C_35)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_136,plain,(
    ! [B_14,A_13,A_36] :
      ( k9_relat_1(B_14,k9_relat_1(k6_relat_1(A_13),A_36)) = k9_relat_1(k7_relat_1(B_14,A_13),A_36)
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1(k6_relat_1(A_13))
      | ~ v1_relat_1(B_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_124])).

tff(c_177,plain,(
    ! [B_40,A_41,A_42] :
      ( k9_relat_1(B_40,k9_relat_1(k6_relat_1(A_41),A_42)) = k9_relat_1(k7_relat_1(B_40,A_41),A_42)
      | ~ v1_relat_1(B_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_136])).

tff(c_262,plain,(
    ! [B_46,A_47,A_48] :
      ( k9_relat_1(k7_relat_1(B_46,A_47),A_48) = k9_relat_1(B_46,A_48)
      | ~ v1_relat_1(B_46)
      | ~ r1_tarski(A_48,A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_177])).

tff(c_18,plain,(
    k9_relat_1(k7_relat_1('#skF_1','#skF_3'),'#skF_2') != k9_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_279,plain,
    ( ~ v1_relat_1('#skF_1')
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_18])).

tff(c_300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22,c_279])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:07:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.22  
% 1.97/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.22  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.97/1.22  
% 1.97/1.22  %Foreground sorts:
% 1.97/1.22  
% 1.97/1.22  
% 1.97/1.22  %Background operators:
% 1.97/1.22  
% 1.97/1.22  
% 1.97/1.22  %Foreground operators:
% 1.97/1.22  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.97/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.22  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.97/1.22  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.97/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.97/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.97/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.22  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.97/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.97/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.97/1.22  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.97/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.97/1.22  
% 2.08/1.23  tff(f_64, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 2.08/1.23  tff(f_27, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.08/1.23  tff(f_52, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.08/1.23  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 2.08/1.23  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.08/1.23  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 2.08/1.23  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.08/1.23  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t159_relat_1)).
% 2.08/1.23  tff(c_20, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.08/1.23  tff(c_22, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.08/1.23  tff(c_2, plain, (![A_1]: (v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.08/1.23  tff(c_14, plain, (![A_12]: (k2_relat_1(k6_relat_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.08/1.23  tff(c_60, plain, (![B_24, A_25]: (k5_relat_1(B_24, k6_relat_1(A_25))=k8_relat_1(A_25, B_24) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.08/1.23  tff(c_16, plain, (![A_13, B_14]: (k5_relat_1(k6_relat_1(A_13), B_14)=k7_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.08/1.23  tff(c_67, plain, (![A_25, A_13]: (k8_relat_1(A_25, k6_relat_1(A_13))=k7_relat_1(k6_relat_1(A_25), A_13) | ~v1_relat_1(k6_relat_1(A_25)) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_16])).
% 2.08/1.23  tff(c_77, plain, (![A_25, A_13]: (k8_relat_1(A_25, k6_relat_1(A_13))=k7_relat_1(k6_relat_1(A_25), A_13))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_67])).
% 2.08/1.23  tff(c_81, plain, (![A_26, B_27]: (k8_relat_1(A_26, B_27)=B_27 | ~r1_tarski(k2_relat_1(B_27), A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.08/1.23  tff(c_87, plain, (![A_26, A_12]: (k8_relat_1(A_26, k6_relat_1(A_12))=k6_relat_1(A_12) | ~r1_tarski(A_12, A_26) | ~v1_relat_1(k6_relat_1(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_81])).
% 2.08/1.23  tff(c_89, plain, (![A_26, A_12]: (k8_relat_1(A_26, k6_relat_1(A_12))=k6_relat_1(A_12) | ~r1_tarski(A_12, A_26))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_87])).
% 2.08/1.23  tff(c_101, plain, (![A_30, A_31]: (k7_relat_1(k6_relat_1(A_30), A_31)=k6_relat_1(A_31) | ~r1_tarski(A_31, A_30))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_89])).
% 2.08/1.23  tff(c_8, plain, (![B_7, A_6]: (k2_relat_1(k7_relat_1(B_7, A_6))=k9_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.08/1.23  tff(c_107, plain, (![A_30, A_31]: (k9_relat_1(k6_relat_1(A_30), A_31)=k2_relat_1(k6_relat_1(A_31)) | ~v1_relat_1(k6_relat_1(A_30)) | ~r1_tarski(A_31, A_30))), inference(superposition, [status(thm), theory('equality')], [c_101, c_8])).
% 2.08/1.23  tff(c_113, plain, (![A_30, A_31]: (k9_relat_1(k6_relat_1(A_30), A_31)=A_31 | ~r1_tarski(A_31, A_30))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14, c_107])).
% 2.08/1.23  tff(c_124, plain, (![B_34, C_35, A_36]: (k9_relat_1(k5_relat_1(B_34, C_35), A_36)=k9_relat_1(C_35, k9_relat_1(B_34, A_36)) | ~v1_relat_1(C_35) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.08/1.23  tff(c_136, plain, (![B_14, A_13, A_36]: (k9_relat_1(B_14, k9_relat_1(k6_relat_1(A_13), A_36))=k9_relat_1(k7_relat_1(B_14, A_13), A_36) | ~v1_relat_1(B_14) | ~v1_relat_1(k6_relat_1(A_13)) | ~v1_relat_1(B_14))), inference(superposition, [status(thm), theory('equality')], [c_16, c_124])).
% 2.08/1.23  tff(c_177, plain, (![B_40, A_41, A_42]: (k9_relat_1(B_40, k9_relat_1(k6_relat_1(A_41), A_42))=k9_relat_1(k7_relat_1(B_40, A_41), A_42) | ~v1_relat_1(B_40))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_136])).
% 2.08/1.23  tff(c_262, plain, (![B_46, A_47, A_48]: (k9_relat_1(k7_relat_1(B_46, A_47), A_48)=k9_relat_1(B_46, A_48) | ~v1_relat_1(B_46) | ~r1_tarski(A_48, A_47))), inference(superposition, [status(thm), theory('equality')], [c_113, c_177])).
% 2.08/1.23  tff(c_18, plain, (k9_relat_1(k7_relat_1('#skF_1', '#skF_3'), '#skF_2')!=k9_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.08/1.23  tff(c_279, plain, (~v1_relat_1('#skF_1') | ~r1_tarski('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_262, c_18])).
% 2.08/1.23  tff(c_300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_22, c_279])).
% 2.08/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.23  
% 2.08/1.23  Inference rules
% 2.08/1.23  ----------------------
% 2.08/1.23  #Ref     : 0
% 2.08/1.23  #Sup     : 61
% 2.08/1.23  #Fact    : 0
% 2.08/1.23  #Define  : 0
% 2.08/1.23  #Split   : 0
% 2.08/1.23  #Chain   : 0
% 2.08/1.23  #Close   : 0
% 2.08/1.23  
% 2.08/1.23  Ordering : KBO
% 2.08/1.23  
% 2.08/1.23  Simplification rules
% 2.08/1.23  ----------------------
% 2.08/1.23  #Subsume      : 0
% 2.08/1.23  #Demod        : 30
% 2.08/1.23  #Tautology    : 29
% 2.08/1.23  #SimpNegUnit  : 0
% 2.08/1.23  #BackRed      : 0
% 2.08/1.23  
% 2.08/1.23  #Partial instantiations: 0
% 2.08/1.23  #Strategies tried      : 1
% 2.08/1.23  
% 2.08/1.23  Timing (in seconds)
% 2.08/1.23  ----------------------
% 2.08/1.23  Preprocessing        : 0.28
% 2.08/1.23  Parsing              : 0.16
% 2.08/1.24  CNF conversion       : 0.02
% 2.08/1.24  Main loop            : 0.20
% 2.08/1.24  Inferencing          : 0.09
% 2.08/1.24  Reduction            : 0.06
% 2.08/1.24  Demodulation         : 0.04
% 2.08/1.24  BG Simplification    : 0.01
% 2.08/1.24  Subsumption          : 0.02
% 2.08/1.24  Abstraction          : 0.01
% 2.08/1.24  MUC search           : 0.00
% 2.08/1.24  Cooper               : 0.00
% 2.08/1.24  Total                : 0.51
% 2.08/1.24  Index Insertion      : 0.00
% 2.08/1.24  Index Deletion       : 0.00
% 2.08/1.24  Index Matching       : 0.00
% 2.08/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
