%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:21 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   41 (  61 expanded)
%              Number of leaves         :   21 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   51 (  79 expanded)
%              Number of equality atoms :   20 (  36 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_relat_1)).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_40,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_44,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_40])).

tff(c_6,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_9] : k2_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_12,plain,(
    ! [A_9] : k1_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_50,plain,(
    ! [A_19] :
      ( k9_relat_1(A_19,k1_relat_1(A_19)) = k2_relat_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_59,plain,(
    ! [A_9] :
      ( k9_relat_1(k6_relat_1(A_9),A_9) = k2_relat_1(k6_relat_1(A_9))
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_50])).

tff(c_63,plain,(
    ! [A_9] : k9_relat_1(k6_relat_1(A_9),A_9) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_14,c_59])).

tff(c_64,plain,(
    ! [B_20,A_21] :
      ( k5_relat_1(B_20,k6_relat_1(A_21)) = B_20
      | ~ r1_tarski(k2_relat_1(B_20),A_21)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_67,plain,(
    ! [A_9,A_21] :
      ( k5_relat_1(k6_relat_1(A_9),k6_relat_1(A_21)) = k6_relat_1(A_9)
      | ~ r1_tarski(A_9,A_21)
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_64])).

tff(c_69,plain,(
    ! [A_9,A_21] :
      ( k5_relat_1(k6_relat_1(A_9),k6_relat_1(A_21)) = k6_relat_1(A_9)
      | ~ r1_tarski(A_9,A_21) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_67])).

tff(c_88,plain,(
    ! [B_25,C_26,A_27] :
      ( k9_relat_1(k5_relat_1(B_25,C_26),A_27) = k9_relat_1(C_26,k9_relat_1(B_25,A_27))
      | ~ v1_relat_1(C_26)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_101,plain,(
    ! [A_21,A_9,A_27] :
      ( k9_relat_1(k6_relat_1(A_21),k9_relat_1(k6_relat_1(A_9),A_27)) = k9_relat_1(k6_relat_1(A_9),A_27)
      | ~ v1_relat_1(k6_relat_1(A_21))
      | ~ v1_relat_1(k6_relat_1(A_9))
      | ~ r1_tarski(A_9,A_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_88])).

tff(c_110,plain,(
    ! [A_28,A_29,A_30] :
      ( k9_relat_1(k6_relat_1(A_28),k9_relat_1(k6_relat_1(A_29),A_30)) = k9_relat_1(k6_relat_1(A_29),A_30)
      | ~ r1_tarski(A_29,A_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_101])).

tff(c_129,plain,(
    ! [A_9,A_28] :
      ( k9_relat_1(k6_relat_1(A_9),A_9) = k9_relat_1(k6_relat_1(A_28),A_9)
      | ~ r1_tarski(A_9,A_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_110])).

tff(c_145,plain,(
    ! [A_31,A_32] :
      ( k9_relat_1(k6_relat_1(A_31),A_32) = A_32
      | ~ r1_tarski(A_32,A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_129])).

tff(c_18,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_166,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_18])).

tff(c_188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_166])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:10:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.24  
% 1.94/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.24  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.94/1.24  
% 1.94/1.24  %Foreground sorts:
% 1.94/1.24  
% 1.94/1.24  
% 1.94/1.24  %Background operators:
% 1.94/1.24  
% 1.94/1.24  
% 1.94/1.24  %Foreground operators:
% 1.94/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.24  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.94/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.94/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.24  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.94/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.94/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.94/1.24  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.94/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.94/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.94/1.24  
% 1.94/1.25  tff(f_57, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_1)).
% 1.94/1.25  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.94/1.25  tff(f_31, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.94/1.25  tff(f_46, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.94/1.25  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 1.94/1.25  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 1.94/1.25  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t159_relat_1)).
% 1.94/1.25  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.94/1.25  tff(c_40, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.94/1.25  tff(c_44, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_20, c_40])).
% 1.94/1.25  tff(c_6, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.94/1.25  tff(c_14, plain, (![A_9]: (k2_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.94/1.25  tff(c_12, plain, (![A_9]: (k1_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.94/1.25  tff(c_50, plain, (![A_19]: (k9_relat_1(A_19, k1_relat_1(A_19))=k2_relat_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.94/1.25  tff(c_59, plain, (![A_9]: (k9_relat_1(k6_relat_1(A_9), A_9)=k2_relat_1(k6_relat_1(A_9)) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_50])).
% 1.94/1.25  tff(c_63, plain, (![A_9]: (k9_relat_1(k6_relat_1(A_9), A_9)=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_14, c_59])).
% 1.94/1.25  tff(c_64, plain, (![B_20, A_21]: (k5_relat_1(B_20, k6_relat_1(A_21))=B_20 | ~r1_tarski(k2_relat_1(B_20), A_21) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.94/1.25  tff(c_67, plain, (![A_9, A_21]: (k5_relat_1(k6_relat_1(A_9), k6_relat_1(A_21))=k6_relat_1(A_9) | ~r1_tarski(A_9, A_21) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_64])).
% 1.94/1.25  tff(c_69, plain, (![A_9, A_21]: (k5_relat_1(k6_relat_1(A_9), k6_relat_1(A_21))=k6_relat_1(A_9) | ~r1_tarski(A_9, A_21))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_67])).
% 1.94/1.25  tff(c_88, plain, (![B_25, C_26, A_27]: (k9_relat_1(k5_relat_1(B_25, C_26), A_27)=k9_relat_1(C_26, k9_relat_1(B_25, A_27)) | ~v1_relat_1(C_26) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.94/1.25  tff(c_101, plain, (![A_21, A_9, A_27]: (k9_relat_1(k6_relat_1(A_21), k9_relat_1(k6_relat_1(A_9), A_27))=k9_relat_1(k6_relat_1(A_9), A_27) | ~v1_relat_1(k6_relat_1(A_21)) | ~v1_relat_1(k6_relat_1(A_9)) | ~r1_tarski(A_9, A_21))), inference(superposition, [status(thm), theory('equality')], [c_69, c_88])).
% 1.94/1.25  tff(c_110, plain, (![A_28, A_29, A_30]: (k9_relat_1(k6_relat_1(A_28), k9_relat_1(k6_relat_1(A_29), A_30))=k9_relat_1(k6_relat_1(A_29), A_30) | ~r1_tarski(A_29, A_28))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_101])).
% 1.94/1.25  tff(c_129, plain, (![A_9, A_28]: (k9_relat_1(k6_relat_1(A_9), A_9)=k9_relat_1(k6_relat_1(A_28), A_9) | ~r1_tarski(A_9, A_28))), inference(superposition, [status(thm), theory('equality')], [c_63, c_110])).
% 1.94/1.25  tff(c_145, plain, (![A_31, A_32]: (k9_relat_1(k6_relat_1(A_31), A_32)=A_32 | ~r1_tarski(A_32, A_31))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_129])).
% 1.94/1.25  tff(c_18, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.94/1.25  tff(c_166, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_145, c_18])).
% 1.94/1.25  tff(c_188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_166])).
% 1.94/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.25  
% 1.94/1.25  Inference rules
% 1.94/1.25  ----------------------
% 1.94/1.25  #Ref     : 0
% 1.94/1.25  #Sup     : 37
% 1.94/1.25  #Fact    : 0
% 1.94/1.25  #Define  : 0
% 1.94/1.25  #Split   : 0
% 1.94/1.25  #Chain   : 0
% 1.94/1.25  #Close   : 0
% 1.94/1.25  
% 1.94/1.25  Ordering : KBO
% 1.94/1.25  
% 1.94/1.25  Simplification rules
% 1.94/1.25  ----------------------
% 1.94/1.25  #Subsume      : 0
% 1.94/1.25  #Demod        : 15
% 1.94/1.25  #Tautology    : 21
% 1.94/1.25  #SimpNegUnit  : 0
% 1.94/1.25  #BackRed      : 0
% 1.94/1.25  
% 1.94/1.25  #Partial instantiations: 0
% 1.94/1.25  #Strategies tried      : 1
% 1.94/1.25  
% 1.94/1.25  Timing (in seconds)
% 1.94/1.25  ----------------------
% 1.94/1.26  Preprocessing        : 0.29
% 1.94/1.26  Parsing              : 0.17
% 1.94/1.26  CNF conversion       : 0.02
% 1.94/1.26  Main loop            : 0.16
% 1.94/1.26  Inferencing          : 0.08
% 1.94/1.26  Reduction            : 0.04
% 1.94/1.26  Demodulation         : 0.03
% 1.94/1.26  BG Simplification    : 0.01
% 1.94/1.26  Subsumption          : 0.02
% 1.94/1.26  Abstraction          : 0.01
% 1.94/1.26  MUC search           : 0.00
% 1.94/1.26  Cooper               : 0.00
% 1.94/1.26  Total                : 0.48
% 1.94/1.26  Index Insertion      : 0.00
% 1.94/1.26  Index Deletion       : 0.00
% 1.94/1.26  Index Matching       : 0.00
% 1.94/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
