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
% DateTime   : Thu Dec  3 09:59:33 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :   43 (  73 expanded)
%              Number of leaves         :   20 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :   66 ( 141 expanded)
%              Number of equality atoms :   21 (  46 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(k2_relat_1(B),A)
         => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_31,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_50,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6,plain,(
    ! [A_3] :
      ( k4_relat_1(k4_relat_1(A_3)) = A_3
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_relat_1(k4_relat_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    r1_tarski(k2_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4,plain,(
    ! [A_2] : v1_relat_1(k6_relat_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_8] : k4_relat_1(k6_relat_1(A_8)) = k6_relat_1(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    ! [A_4] :
      ( k1_relat_1(k4_relat_1(A_4)) = k2_relat_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_107,plain,(
    ! [A_18,B_19] :
      ( k5_relat_1(k6_relat_1(A_18),B_19) = B_19
      | ~ r1_tarski(k1_relat_1(B_19),A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_653,plain,(
    ! [A_42,A_43] :
      ( k5_relat_1(k6_relat_1(A_42),k4_relat_1(A_43)) = k4_relat_1(A_43)
      | ~ r1_tarski(k2_relat_1(A_43),A_42)
      | ~ v1_relat_1(k4_relat_1(A_43))
      | ~ v1_relat_1(A_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_107])).

tff(c_111,plain,(
    ! [B_20,A_21] :
      ( k5_relat_1(k4_relat_1(B_20),k4_relat_1(A_21)) = k4_relat_1(k5_relat_1(A_21,B_20))
      | ~ v1_relat_1(B_20)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_120,plain,(
    ! [A_21,A_3] :
      ( k4_relat_1(k5_relat_1(A_21,k4_relat_1(A_3))) = k5_relat_1(A_3,k4_relat_1(A_21))
      | ~ v1_relat_1(k4_relat_1(A_3))
      | ~ v1_relat_1(A_21)
      | ~ v1_relat_1(A_3) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_111])).

tff(c_662,plain,(
    ! [A_43,A_42] :
      ( k5_relat_1(A_43,k4_relat_1(k6_relat_1(A_42))) = k4_relat_1(k4_relat_1(A_43))
      | ~ v1_relat_1(k4_relat_1(A_43))
      | ~ v1_relat_1(k6_relat_1(A_42))
      | ~ v1_relat_1(A_43)
      | ~ r1_tarski(k2_relat_1(A_43),A_42)
      | ~ v1_relat_1(k4_relat_1(A_43))
      | ~ v1_relat_1(A_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_653,c_120])).

tff(c_710,plain,(
    ! [A_46,A_47] :
      ( k5_relat_1(A_46,k6_relat_1(A_47)) = k4_relat_1(k4_relat_1(A_46))
      | ~ r1_tarski(k2_relat_1(A_46),A_47)
      | ~ v1_relat_1(k4_relat_1(A_46))
      | ~ v1_relat_1(A_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_14,c_662])).

tff(c_719,plain,
    ( k5_relat_1('#skF_2',k6_relat_1('#skF_1')) = k4_relat_1(k4_relat_1('#skF_2'))
    | ~ v1_relat_1(k4_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_710])).

tff(c_724,plain,
    ( k5_relat_1('#skF_2',k6_relat_1('#skF_1')) = k4_relat_1(k4_relat_1('#skF_2'))
    | ~ v1_relat_1(k4_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_719])).

tff(c_725,plain,(
    ~ v1_relat_1(k4_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_724])).

tff(c_728,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_725])).

tff(c_732,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_728])).

tff(c_733,plain,(
    k5_relat_1('#skF_2',k6_relat_1('#skF_1')) = k4_relat_1(k4_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_724])).

tff(c_18,plain,(
    k5_relat_1('#skF_2',k6_relat_1('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_735,plain,(
    k4_relat_1(k4_relat_1('#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_733,c_18])).

tff(c_747,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_735])).

tff(c_751,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_747])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n002.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 14:33:36 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.46  
% 2.62/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.46  %$ r1_tarski > v1_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.99/1.46  
% 2.99/1.46  %Foreground sorts:
% 2.99/1.46  
% 2.99/1.46  
% 2.99/1.46  %Background operators:
% 2.99/1.46  
% 2.99/1.46  
% 2.99/1.46  %Foreground operators:
% 2.99/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.46  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.99/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.99/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.99/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.99/1.46  tff('#skF_1', type, '#skF_1': $i).
% 2.99/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.99/1.46  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.99/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.99/1.46  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 2.99/1.46  
% 2.99/1.47  tff(f_63, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 2.99/1.47  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 2.99/1.47  tff(f_29, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 2.99/1.47  tff(f_31, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.99/1.47  tff(f_50, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_relat_1)).
% 2.99/1.47  tff(f_41, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 2.99/1.47  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 2.99/1.47  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_relat_1)).
% 2.99/1.47  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.99/1.47  tff(c_6, plain, (![A_3]: (k4_relat_1(k4_relat_1(A_3))=A_3 | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.99/1.47  tff(c_2, plain, (![A_1]: (v1_relat_1(k4_relat_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.99/1.47  tff(c_20, plain, (r1_tarski(k2_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.99/1.47  tff(c_4, plain, (![A_2]: (v1_relat_1(k6_relat_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.99/1.47  tff(c_14, plain, (![A_8]: (k4_relat_1(k6_relat_1(A_8))=k6_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.99/1.47  tff(c_10, plain, (![A_4]: (k1_relat_1(k4_relat_1(A_4))=k2_relat_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.99/1.47  tff(c_107, plain, (![A_18, B_19]: (k5_relat_1(k6_relat_1(A_18), B_19)=B_19 | ~r1_tarski(k1_relat_1(B_19), A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.99/1.47  tff(c_653, plain, (![A_42, A_43]: (k5_relat_1(k6_relat_1(A_42), k4_relat_1(A_43))=k4_relat_1(A_43) | ~r1_tarski(k2_relat_1(A_43), A_42) | ~v1_relat_1(k4_relat_1(A_43)) | ~v1_relat_1(A_43))), inference(superposition, [status(thm), theory('equality')], [c_10, c_107])).
% 2.99/1.47  tff(c_111, plain, (![B_20, A_21]: (k5_relat_1(k4_relat_1(B_20), k4_relat_1(A_21))=k4_relat_1(k5_relat_1(A_21, B_20)) | ~v1_relat_1(B_20) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.99/1.47  tff(c_120, plain, (![A_21, A_3]: (k4_relat_1(k5_relat_1(A_21, k4_relat_1(A_3)))=k5_relat_1(A_3, k4_relat_1(A_21)) | ~v1_relat_1(k4_relat_1(A_3)) | ~v1_relat_1(A_21) | ~v1_relat_1(A_3))), inference(superposition, [status(thm), theory('equality')], [c_6, c_111])).
% 2.99/1.47  tff(c_662, plain, (![A_43, A_42]: (k5_relat_1(A_43, k4_relat_1(k6_relat_1(A_42)))=k4_relat_1(k4_relat_1(A_43)) | ~v1_relat_1(k4_relat_1(A_43)) | ~v1_relat_1(k6_relat_1(A_42)) | ~v1_relat_1(A_43) | ~r1_tarski(k2_relat_1(A_43), A_42) | ~v1_relat_1(k4_relat_1(A_43)) | ~v1_relat_1(A_43))), inference(superposition, [status(thm), theory('equality')], [c_653, c_120])).
% 2.99/1.47  tff(c_710, plain, (![A_46, A_47]: (k5_relat_1(A_46, k6_relat_1(A_47))=k4_relat_1(k4_relat_1(A_46)) | ~r1_tarski(k2_relat_1(A_46), A_47) | ~v1_relat_1(k4_relat_1(A_46)) | ~v1_relat_1(A_46))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_14, c_662])).
% 2.99/1.47  tff(c_719, plain, (k5_relat_1('#skF_2', k6_relat_1('#skF_1'))=k4_relat_1(k4_relat_1('#skF_2')) | ~v1_relat_1(k4_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_20, c_710])).
% 2.99/1.47  tff(c_724, plain, (k5_relat_1('#skF_2', k6_relat_1('#skF_1'))=k4_relat_1(k4_relat_1('#skF_2')) | ~v1_relat_1(k4_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_719])).
% 2.99/1.47  tff(c_725, plain, (~v1_relat_1(k4_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_724])).
% 2.99/1.47  tff(c_728, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2, c_725])).
% 2.99/1.47  tff(c_732, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_728])).
% 2.99/1.47  tff(c_733, plain, (k5_relat_1('#skF_2', k6_relat_1('#skF_1'))=k4_relat_1(k4_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_724])).
% 2.99/1.47  tff(c_18, plain, (k5_relat_1('#skF_2', k6_relat_1('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.99/1.47  tff(c_735, plain, (k4_relat_1(k4_relat_1('#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_733, c_18])).
% 2.99/1.47  tff(c_747, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6, c_735])).
% 2.99/1.47  tff(c_751, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_747])).
% 2.99/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.47  
% 2.99/1.47  Inference rules
% 2.99/1.47  ----------------------
% 2.99/1.47  #Ref     : 0
% 2.99/1.47  #Sup     : 194
% 2.99/1.47  #Fact    : 0
% 2.99/1.47  #Define  : 0
% 2.99/1.47  #Split   : 1
% 2.99/1.47  #Chain   : 0
% 2.99/1.47  #Close   : 0
% 2.99/1.47  
% 2.99/1.47  Ordering : KBO
% 2.99/1.47  
% 2.99/1.47  Simplification rules
% 2.99/1.47  ----------------------
% 2.99/1.47  #Subsume      : 14
% 2.99/1.47  #Demod        : 88
% 2.99/1.47  #Tautology    : 58
% 2.99/1.47  #SimpNegUnit  : 0
% 2.99/1.47  #BackRed      : 1
% 2.99/1.47  
% 2.99/1.47  #Partial instantiations: 0
% 2.99/1.47  #Strategies tried      : 1
% 2.99/1.47  
% 2.99/1.47  Timing (in seconds)
% 2.99/1.47  ----------------------
% 2.99/1.47  Preprocessing        : 0.34
% 2.99/1.47  Parsing              : 0.18
% 2.99/1.47  CNF conversion       : 0.02
% 2.99/1.47  Main loop            : 0.38
% 2.99/1.47  Inferencing          : 0.15
% 2.99/1.48  Reduction            : 0.11
% 2.99/1.48  Demodulation         : 0.08
% 3.06/1.48  BG Simplification    : 0.02
% 3.06/1.48  Subsumption          : 0.07
% 3.06/1.48  Abstraction          : 0.03
% 3.06/1.48  MUC search           : 0.00
% 3.06/1.48  Cooper               : 0.00
% 3.06/1.48  Total                : 0.75
% 3.06/1.48  Index Insertion      : 0.00
% 3.06/1.48  Index Deletion       : 0.00
% 3.06/1.48  Index Matching       : 0.00
% 3.06/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
