%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:09 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   36 (  40 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 (  84 expanded)
%              Number of equality atoms :   16 (  18 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k5_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3] :
      ( k9_relat_1(A_3,k1_relat_1(A_3)) = k2_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_39,plain,(
    ! [A_23,B_24] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_23,B_24)),k1_relat_1(A_23))
      | ~ v1_relat_1(B_24)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [B_14,A_13] :
      ( k7_relat_1(B_14,A_13) = B_14
      | ~ r1_tarski(k1_relat_1(B_14),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_61,plain,(
    ! [A_28,B_29] :
      ( k7_relat_1(k5_relat_1(A_28,B_29),k1_relat_1(A_28)) = k5_relat_1(A_28,B_29)
      | ~ v1_relat_1(k5_relat_1(A_28,B_29))
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(A_28) ) ),
    inference(resolution,[status(thm)],[c_39,c_12])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( k2_relat_1(k7_relat_1(B_5,A_4)) = k9_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_94,plain,(
    ! [A_32,B_33] :
      ( k9_relat_1(k5_relat_1(A_32,B_33),k1_relat_1(A_32)) = k2_relat_1(k5_relat_1(A_32,B_33))
      | ~ v1_relat_1(k5_relat_1(A_32,B_33))
      | ~ v1_relat_1(k5_relat_1(A_32,B_33))
      | ~ v1_relat_1(B_33)
      | ~ v1_relat_1(A_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_6])).

tff(c_8,plain,(
    ! [B_7,C_9,A_6] :
      ( k9_relat_1(k5_relat_1(B_7,C_9),A_6) = k9_relat_1(C_9,k9_relat_1(B_7,A_6))
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_110,plain,(
    ! [B_34,A_35] :
      ( k9_relat_1(B_34,k9_relat_1(A_35,k1_relat_1(A_35))) = k2_relat_1(k5_relat_1(A_35,B_34))
      | ~ v1_relat_1(B_34)
      | ~ v1_relat_1(A_35)
      | ~ v1_relat_1(k5_relat_1(A_35,B_34))
      | ~ v1_relat_1(k5_relat_1(A_35,B_34))
      | ~ v1_relat_1(B_34)
      | ~ v1_relat_1(A_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_8])).

tff(c_159,plain,(
    ! [B_39,A_40] :
      ( k9_relat_1(B_39,k2_relat_1(A_40)) = k2_relat_1(k5_relat_1(A_40,B_39))
      | ~ v1_relat_1(B_39)
      | ~ v1_relat_1(A_40)
      | ~ v1_relat_1(k5_relat_1(A_40,B_39))
      | ~ v1_relat_1(k5_relat_1(A_40,B_39))
      | ~ v1_relat_1(B_39)
      | ~ v1_relat_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_110])).

tff(c_163,plain,(
    ! [B_41,A_42] :
      ( k9_relat_1(B_41,k2_relat_1(A_42)) = k2_relat_1(k5_relat_1(A_42,B_41))
      | ~ v1_relat_1(k5_relat_1(A_42,B_41))
      | ~ v1_relat_1(B_41)
      | ~ v1_relat_1(A_42) ) ),
    inference(resolution,[status(thm)],[c_2,c_159])).

tff(c_168,plain,(
    ! [B_43,A_44] :
      ( k9_relat_1(B_43,k2_relat_1(A_44)) = k2_relat_1(k5_relat_1(A_44,B_43))
      | ~ v1_relat_1(B_43)
      | ~ v1_relat_1(A_44) ) ),
    inference(resolution,[status(thm)],[c_2,c_163])).

tff(c_14,plain,(
    k9_relat_1('#skF_2',k2_relat_1('#skF_1')) != k2_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_178,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_14])).

tff(c_193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_178])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:22:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.29  
% 2.04/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.29  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.04/1.29  
% 2.04/1.29  %Foreground sorts:
% 2.04/1.29  
% 2.04/1.29  
% 2.04/1.29  %Background operators:
% 2.04/1.29  
% 2.04/1.29  
% 2.04/1.29  %Foreground operators:
% 2.04/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.29  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.04/1.29  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.04/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.04/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.04/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.29  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.04/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.04/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.04/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.04/1.29  
% 2.04/1.30  tff(f_67, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 2.04/1.30  tff(f_31, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.04/1.30  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.04/1.30  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_relat_1)).
% 2.04/1.30  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.04/1.30  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.04/1.30  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t159_relat_1)).
% 2.04/1.30  tff(c_18, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.04/1.30  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.04/1.30  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k5_relat_1(A_1, B_2)) | ~v1_relat_1(B_2) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.04/1.30  tff(c_4, plain, (![A_3]: (k9_relat_1(A_3, k1_relat_1(A_3))=k2_relat_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.04/1.30  tff(c_39, plain, (![A_23, B_24]: (r1_tarski(k1_relat_1(k5_relat_1(A_23, B_24)), k1_relat_1(A_23)) | ~v1_relat_1(B_24) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.04/1.30  tff(c_12, plain, (![B_14, A_13]: (k7_relat_1(B_14, A_13)=B_14 | ~r1_tarski(k1_relat_1(B_14), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.04/1.30  tff(c_61, plain, (![A_28, B_29]: (k7_relat_1(k5_relat_1(A_28, B_29), k1_relat_1(A_28))=k5_relat_1(A_28, B_29) | ~v1_relat_1(k5_relat_1(A_28, B_29)) | ~v1_relat_1(B_29) | ~v1_relat_1(A_28))), inference(resolution, [status(thm)], [c_39, c_12])).
% 2.04/1.30  tff(c_6, plain, (![B_5, A_4]: (k2_relat_1(k7_relat_1(B_5, A_4))=k9_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.04/1.30  tff(c_94, plain, (![A_32, B_33]: (k9_relat_1(k5_relat_1(A_32, B_33), k1_relat_1(A_32))=k2_relat_1(k5_relat_1(A_32, B_33)) | ~v1_relat_1(k5_relat_1(A_32, B_33)) | ~v1_relat_1(k5_relat_1(A_32, B_33)) | ~v1_relat_1(B_33) | ~v1_relat_1(A_32))), inference(superposition, [status(thm), theory('equality')], [c_61, c_6])).
% 2.04/1.30  tff(c_8, plain, (![B_7, C_9, A_6]: (k9_relat_1(k5_relat_1(B_7, C_9), A_6)=k9_relat_1(C_9, k9_relat_1(B_7, A_6)) | ~v1_relat_1(C_9) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.04/1.30  tff(c_110, plain, (![B_34, A_35]: (k9_relat_1(B_34, k9_relat_1(A_35, k1_relat_1(A_35)))=k2_relat_1(k5_relat_1(A_35, B_34)) | ~v1_relat_1(B_34) | ~v1_relat_1(A_35) | ~v1_relat_1(k5_relat_1(A_35, B_34)) | ~v1_relat_1(k5_relat_1(A_35, B_34)) | ~v1_relat_1(B_34) | ~v1_relat_1(A_35))), inference(superposition, [status(thm), theory('equality')], [c_94, c_8])).
% 2.04/1.30  tff(c_159, plain, (![B_39, A_40]: (k9_relat_1(B_39, k2_relat_1(A_40))=k2_relat_1(k5_relat_1(A_40, B_39)) | ~v1_relat_1(B_39) | ~v1_relat_1(A_40) | ~v1_relat_1(k5_relat_1(A_40, B_39)) | ~v1_relat_1(k5_relat_1(A_40, B_39)) | ~v1_relat_1(B_39) | ~v1_relat_1(A_40) | ~v1_relat_1(A_40))), inference(superposition, [status(thm), theory('equality')], [c_4, c_110])).
% 2.04/1.30  tff(c_163, plain, (![B_41, A_42]: (k9_relat_1(B_41, k2_relat_1(A_42))=k2_relat_1(k5_relat_1(A_42, B_41)) | ~v1_relat_1(k5_relat_1(A_42, B_41)) | ~v1_relat_1(B_41) | ~v1_relat_1(A_42))), inference(resolution, [status(thm)], [c_2, c_159])).
% 2.04/1.30  tff(c_168, plain, (![B_43, A_44]: (k9_relat_1(B_43, k2_relat_1(A_44))=k2_relat_1(k5_relat_1(A_44, B_43)) | ~v1_relat_1(B_43) | ~v1_relat_1(A_44))), inference(resolution, [status(thm)], [c_2, c_163])).
% 2.04/1.30  tff(c_14, plain, (k9_relat_1('#skF_2', k2_relat_1('#skF_1'))!=k2_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.04/1.30  tff(c_178, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_168, c_14])).
% 2.04/1.30  tff(c_193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_178])).
% 2.04/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.30  
% 2.04/1.30  Inference rules
% 2.04/1.30  ----------------------
% 2.04/1.30  #Ref     : 0
% 2.04/1.30  #Sup     : 41
% 2.04/1.30  #Fact    : 0
% 2.04/1.30  #Define  : 0
% 2.04/1.30  #Split   : 0
% 2.04/1.30  #Chain   : 0
% 2.04/1.30  #Close   : 0
% 2.04/1.30  
% 2.04/1.30  Ordering : KBO
% 2.04/1.30  
% 2.04/1.30  Simplification rules
% 2.04/1.30  ----------------------
% 2.04/1.30  #Subsume      : 4
% 2.04/1.30  #Demod        : 2
% 2.04/1.30  #Tautology    : 17
% 2.04/1.30  #SimpNegUnit  : 0
% 2.04/1.30  #BackRed      : 0
% 2.04/1.30  
% 2.04/1.30  #Partial instantiations: 0
% 2.04/1.30  #Strategies tried      : 1
% 2.04/1.30  
% 2.04/1.30  Timing (in seconds)
% 2.04/1.30  ----------------------
% 2.04/1.30  Preprocessing        : 0.26
% 2.04/1.30  Parsing              : 0.14
% 2.04/1.30  CNF conversion       : 0.02
% 2.04/1.30  Main loop            : 0.18
% 2.04/1.30  Inferencing          : 0.08
% 2.04/1.30  Reduction            : 0.04
% 2.04/1.30  Demodulation         : 0.03
% 2.04/1.30  BG Simplification    : 0.01
% 2.04/1.30  Subsumption          : 0.03
% 2.04/1.30  Abstraction          : 0.01
% 2.04/1.30  MUC search           : 0.00
% 2.04/1.30  Cooper               : 0.00
% 2.04/1.30  Total                : 0.47
% 2.04/1.30  Index Insertion      : 0.00
% 2.04/1.30  Index Deletion       : 0.00
% 2.04/1.30  Index Matching       : 0.00
% 2.04/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
