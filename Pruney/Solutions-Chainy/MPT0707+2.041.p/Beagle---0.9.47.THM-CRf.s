%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:21 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   36 (  45 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   43 (  55 expanded)
%              Number of equality atoms :   15 (  22 expanded)
%              Maximal formula depth    :    6 (   4 average)
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

tff(f_53,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_38,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_38])).

tff(c_6,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_7] : k2_relat_1(k6_relat_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_48,plain,(
    ! [B_17,A_18] :
      ( k5_relat_1(B_17,k6_relat_1(A_18)) = B_17
      | ~ r1_tarski(k2_relat_1(B_17),A_18)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_51,plain,(
    ! [A_7,A_18] :
      ( k5_relat_1(k6_relat_1(A_7),k6_relat_1(A_18)) = k6_relat_1(A_7)
      | ~ r1_tarski(A_7,A_18)
      | ~ v1_relat_1(k6_relat_1(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_48])).

tff(c_53,plain,(
    ! [A_7,A_18] :
      ( k5_relat_1(k6_relat_1(A_7),k6_relat_1(A_18)) = k6_relat_1(A_7)
      | ~ r1_tarski(A_7,A_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_51])).

tff(c_54,plain,(
    ! [B_19,A_20] :
      ( k9_relat_1(B_19,k2_relat_1(A_20)) = k2_relat_1(k5_relat_1(A_20,B_19))
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_63,plain,(
    ! [A_7,B_19] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_7),B_19)) = k9_relat_1(B_19,A_7)
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(k6_relat_1(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_54])).

tff(c_77,plain,(
    ! [A_23,B_24] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_23),B_24)) = k9_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_63])).

tff(c_92,plain,(
    ! [A_18,A_7] :
      ( k9_relat_1(k6_relat_1(A_18),A_7) = k2_relat_1(k6_relat_1(A_7))
      | ~ v1_relat_1(k6_relat_1(A_18))
      | ~ r1_tarski(A_7,A_18) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_77])).

tff(c_97,plain,(
    ! [A_25,A_26] :
      ( k9_relat_1(k6_relat_1(A_25),A_26) = A_26
      | ~ r1_tarski(A_26,A_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12,c_92])).

tff(c_16,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_107,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_16])).

tff(c_121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_107])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:05:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.10  
% 1.68/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.10  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.68/1.10  
% 1.68/1.10  %Foreground sorts:
% 1.68/1.10  
% 1.68/1.10  
% 1.68/1.10  %Background operators:
% 1.68/1.10  
% 1.68/1.10  
% 1.68/1.10  %Foreground operators:
% 1.68/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.10  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.68/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.68/1.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.68/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.10  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.68/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.68/1.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.68/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.68/1.10  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.68/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.68/1.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.68/1.10  
% 1.68/1.11  tff(f_53, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 1.68/1.11  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.68/1.11  tff(f_31, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.68/1.11  tff(f_42, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.68/1.11  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 1.68/1.11  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 1.68/1.11  tff(c_18, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.68/1.11  tff(c_38, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.68/1.11  tff(c_42, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_18, c_38])).
% 1.68/1.11  tff(c_6, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.68/1.11  tff(c_12, plain, (![A_7]: (k2_relat_1(k6_relat_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.68/1.11  tff(c_48, plain, (![B_17, A_18]: (k5_relat_1(B_17, k6_relat_1(A_18))=B_17 | ~r1_tarski(k2_relat_1(B_17), A_18) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.68/1.11  tff(c_51, plain, (![A_7, A_18]: (k5_relat_1(k6_relat_1(A_7), k6_relat_1(A_18))=k6_relat_1(A_7) | ~r1_tarski(A_7, A_18) | ~v1_relat_1(k6_relat_1(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_48])).
% 1.68/1.11  tff(c_53, plain, (![A_7, A_18]: (k5_relat_1(k6_relat_1(A_7), k6_relat_1(A_18))=k6_relat_1(A_7) | ~r1_tarski(A_7, A_18))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_51])).
% 1.68/1.11  tff(c_54, plain, (![B_19, A_20]: (k9_relat_1(B_19, k2_relat_1(A_20))=k2_relat_1(k5_relat_1(A_20, B_19)) | ~v1_relat_1(B_19) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.68/1.11  tff(c_63, plain, (![A_7, B_19]: (k2_relat_1(k5_relat_1(k6_relat_1(A_7), B_19))=k9_relat_1(B_19, A_7) | ~v1_relat_1(B_19) | ~v1_relat_1(k6_relat_1(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_54])).
% 1.68/1.11  tff(c_77, plain, (![A_23, B_24]: (k2_relat_1(k5_relat_1(k6_relat_1(A_23), B_24))=k9_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_63])).
% 1.68/1.11  tff(c_92, plain, (![A_18, A_7]: (k9_relat_1(k6_relat_1(A_18), A_7)=k2_relat_1(k6_relat_1(A_7)) | ~v1_relat_1(k6_relat_1(A_18)) | ~r1_tarski(A_7, A_18))), inference(superposition, [status(thm), theory('equality')], [c_53, c_77])).
% 1.68/1.11  tff(c_97, plain, (![A_25, A_26]: (k9_relat_1(k6_relat_1(A_25), A_26)=A_26 | ~r1_tarski(A_26, A_25))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_12, c_92])).
% 1.68/1.11  tff(c_16, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.68/1.11  tff(c_107, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_97, c_16])).
% 1.68/1.11  tff(c_121, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_107])).
% 1.68/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.11  
% 1.68/1.11  Inference rules
% 1.68/1.11  ----------------------
% 1.68/1.11  #Ref     : 0
% 1.68/1.11  #Sup     : 22
% 1.68/1.11  #Fact    : 0
% 1.68/1.11  #Define  : 0
% 1.68/1.11  #Split   : 0
% 1.68/1.11  #Chain   : 0
% 1.68/1.11  #Close   : 0
% 1.68/1.11  
% 1.68/1.11  Ordering : KBO
% 1.68/1.11  
% 1.68/1.11  Simplification rules
% 1.68/1.11  ----------------------
% 1.68/1.11  #Subsume      : 0
% 1.68/1.11  #Demod        : 6
% 1.68/1.11  #Tautology    : 12
% 1.68/1.11  #SimpNegUnit  : 0
% 1.68/1.11  #BackRed      : 0
% 1.68/1.11  
% 1.68/1.11  #Partial instantiations: 0
% 1.68/1.11  #Strategies tried      : 1
% 1.68/1.11  
% 1.68/1.11  Timing (in seconds)
% 1.68/1.11  ----------------------
% 1.68/1.11  Preprocessing        : 0.26
% 1.68/1.11  Parsing              : 0.14
% 1.68/1.11  CNF conversion       : 0.02
% 1.68/1.11  Main loop            : 0.11
% 1.68/1.11  Inferencing          : 0.05
% 1.68/1.11  Reduction            : 0.03
% 1.68/1.11  Demodulation         : 0.02
% 1.68/1.11  BG Simplification    : 0.01
% 1.68/1.11  Subsumption          : 0.01
% 1.68/1.11  Abstraction          : 0.01
% 1.68/1.11  MUC search           : 0.00
% 1.68/1.11  Cooper               : 0.00
% 1.68/1.11  Total                : 0.39
% 1.68/1.11  Index Insertion      : 0.00
% 1.68/1.11  Index Deletion       : 0.00
% 1.68/1.11  Index Matching       : 0.00
% 1.68/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
