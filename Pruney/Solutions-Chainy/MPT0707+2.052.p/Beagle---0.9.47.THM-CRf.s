%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:23 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   40 (  47 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :   46 (  57 expanded)
%              Number of equality atoms :   17 (  21 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_37,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_44,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ m1_subset_1(A_17,k1_zfmisc_1(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_52,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_44])).

tff(c_16,plain,(
    ! [A_10] : v1_relat_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [A_5] : k2_relat_1(k6_relat_1(A_5)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_71,plain,(
    ! [B_23,A_24] :
      ( k5_relat_1(B_23,k6_relat_1(A_24)) = B_23
      | ~ r1_tarski(k2_relat_1(B_23),A_24)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_77,plain,(
    ! [A_5,A_24] :
      ( k5_relat_1(k6_relat_1(A_5),k6_relat_1(A_24)) = k6_relat_1(A_5)
      | ~ r1_tarski(A_5,A_24)
      | ~ v1_relat_1(k6_relat_1(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_71])).

tff(c_80,plain,(
    ! [A_25,A_26] :
      ( k5_relat_1(k6_relat_1(A_25),k6_relat_1(A_26)) = k6_relat_1(A_25)
      | ~ r1_tarski(A_25,A_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_77])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( k5_relat_1(k6_relat_1(A_8),B_9) = k7_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_86,plain,(
    ! [A_26,A_25] :
      ( k7_relat_1(k6_relat_1(A_26),A_25) = k6_relat_1(A_25)
      | ~ v1_relat_1(k6_relat_1(A_26))
      | ~ r1_tarski(A_25,A_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_14])).

tff(c_100,plain,(
    ! [A_27,A_28] :
      ( k7_relat_1(k6_relat_1(A_27),A_28) = k6_relat_1(A_28)
      | ~ r1_tarski(A_28,A_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_86])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k2_relat_1(k7_relat_1(B_4,A_3)) = k9_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_106,plain,(
    ! [A_27,A_28] :
      ( k9_relat_1(k6_relat_1(A_27),A_28) = k2_relat_1(k6_relat_1(A_28))
      | ~ v1_relat_1(k6_relat_1(A_27))
      | ~ r1_tarski(A_28,A_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_6])).

tff(c_114,plain,(
    ! [A_29,A_30] :
      ( k9_relat_1(k6_relat_1(A_29),A_30) = A_30
      | ~ r1_tarski(A_30,A_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_10,c_106])).

tff(c_20,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_120,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_20])).

tff(c_128,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_120])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:47:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.12  
% 1.64/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.13  %$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.64/1.13  
% 1.64/1.13  %Foreground sorts:
% 1.64/1.13  
% 1.64/1.13  
% 1.64/1.13  %Background operators:
% 1.64/1.13  
% 1.64/1.13  
% 1.64/1.13  %Foreground operators:
% 1.64/1.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.64/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.13  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.64/1.13  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.64/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.64/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.13  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.64/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.64/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.64/1.13  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.64/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.64/1.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.64/1.13  
% 1.64/1.14  tff(f_56, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 1.64/1.14  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.64/1.14  tff(f_51, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.64/1.14  tff(f_37, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.64/1.14  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 1.64/1.14  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 1.64/1.14  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.64/1.14  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.64/1.14  tff(c_44, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~m1_subset_1(A_17, k1_zfmisc_1(B_18)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.64/1.14  tff(c_52, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_22, c_44])).
% 1.64/1.14  tff(c_16, plain, (![A_10]: (v1_relat_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.64/1.14  tff(c_10, plain, (![A_5]: (k2_relat_1(k6_relat_1(A_5))=A_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.64/1.14  tff(c_71, plain, (![B_23, A_24]: (k5_relat_1(B_23, k6_relat_1(A_24))=B_23 | ~r1_tarski(k2_relat_1(B_23), A_24) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.64/1.14  tff(c_77, plain, (![A_5, A_24]: (k5_relat_1(k6_relat_1(A_5), k6_relat_1(A_24))=k6_relat_1(A_5) | ~r1_tarski(A_5, A_24) | ~v1_relat_1(k6_relat_1(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_71])).
% 1.64/1.14  tff(c_80, plain, (![A_25, A_26]: (k5_relat_1(k6_relat_1(A_25), k6_relat_1(A_26))=k6_relat_1(A_25) | ~r1_tarski(A_25, A_26))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_77])).
% 1.64/1.14  tff(c_14, plain, (![A_8, B_9]: (k5_relat_1(k6_relat_1(A_8), B_9)=k7_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.64/1.14  tff(c_86, plain, (![A_26, A_25]: (k7_relat_1(k6_relat_1(A_26), A_25)=k6_relat_1(A_25) | ~v1_relat_1(k6_relat_1(A_26)) | ~r1_tarski(A_25, A_26))), inference(superposition, [status(thm), theory('equality')], [c_80, c_14])).
% 1.64/1.14  tff(c_100, plain, (![A_27, A_28]: (k7_relat_1(k6_relat_1(A_27), A_28)=k6_relat_1(A_28) | ~r1_tarski(A_28, A_27))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_86])).
% 1.64/1.14  tff(c_6, plain, (![B_4, A_3]: (k2_relat_1(k7_relat_1(B_4, A_3))=k9_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.64/1.14  tff(c_106, plain, (![A_27, A_28]: (k9_relat_1(k6_relat_1(A_27), A_28)=k2_relat_1(k6_relat_1(A_28)) | ~v1_relat_1(k6_relat_1(A_27)) | ~r1_tarski(A_28, A_27))), inference(superposition, [status(thm), theory('equality')], [c_100, c_6])).
% 1.64/1.14  tff(c_114, plain, (![A_29, A_30]: (k9_relat_1(k6_relat_1(A_29), A_30)=A_30 | ~r1_tarski(A_30, A_29))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_10, c_106])).
% 1.64/1.14  tff(c_20, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.64/1.14  tff(c_120, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_114, c_20])).
% 1.64/1.14  tff(c_128, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_120])).
% 1.64/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.14  
% 1.64/1.14  Inference rules
% 1.64/1.14  ----------------------
% 1.64/1.14  #Ref     : 0
% 1.64/1.14  #Sup     : 22
% 1.64/1.14  #Fact    : 0
% 1.64/1.14  #Define  : 0
% 1.64/1.14  #Split   : 0
% 1.64/1.14  #Chain   : 0
% 1.64/1.14  #Close   : 0
% 1.64/1.14  
% 1.64/1.14  Ordering : KBO
% 1.64/1.14  
% 1.64/1.14  Simplification rules
% 1.64/1.14  ----------------------
% 1.64/1.14  #Subsume      : 0
% 1.64/1.14  #Demod        : 6
% 1.64/1.14  #Tautology    : 14
% 1.64/1.14  #SimpNegUnit  : 0
% 1.64/1.14  #BackRed      : 0
% 1.64/1.14  
% 1.64/1.14  #Partial instantiations: 0
% 1.64/1.14  #Strategies tried      : 1
% 1.64/1.14  
% 1.64/1.14  Timing (in seconds)
% 1.64/1.14  ----------------------
% 1.64/1.14  Preprocessing        : 0.26
% 1.64/1.14  Parsing              : 0.15
% 1.64/1.14  CNF conversion       : 0.01
% 1.64/1.14  Main loop            : 0.11
% 1.64/1.14  Inferencing          : 0.05
% 1.64/1.14  Reduction            : 0.03
% 1.64/1.14  Demodulation         : 0.02
% 1.64/1.14  BG Simplification    : 0.01
% 1.64/1.14  Subsumption          : 0.01
% 1.64/1.14  Abstraction          : 0.01
% 1.64/1.14  MUC search           : 0.00
% 1.64/1.14  Cooper               : 0.00
% 1.64/1.14  Total                : 0.40
% 1.64/1.14  Index Insertion      : 0.00
% 1.64/1.14  Index Deletion       : 0.00
% 1.64/1.14  Index Matching       : 0.00
% 1.64/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
