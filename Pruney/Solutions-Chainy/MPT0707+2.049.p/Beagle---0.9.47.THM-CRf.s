%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:22 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   43 (  52 expanded)
%              Number of leaves         :   25 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   49 (  63 expanded)
%              Number of equality atoms :   19 (  23 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

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

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_47,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_46,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ m1_subset_1(A_19,k1_zfmisc_1(B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_54,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_46])).

tff(c_18,plain,(
    ! [A_12] : v1_relat_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    ! [A_9] : k2_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_73,plain,(
    ! [B_25,A_26] :
      ( k5_relat_1(B_25,k6_relat_1(A_26)) = k8_relat_1(A_26,B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( k5_relat_1(k6_relat_1(A_10),B_11) = k7_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_80,plain,(
    ! [A_26,A_10] :
      ( k8_relat_1(A_26,k6_relat_1(A_10)) = k7_relat_1(k6_relat_1(A_26),A_10)
      | ~ v1_relat_1(k6_relat_1(A_26))
      | ~ v1_relat_1(k6_relat_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_16])).

tff(c_90,plain,(
    ! [A_26,A_10] : k8_relat_1(A_26,k6_relat_1(A_10)) = k7_relat_1(k6_relat_1(A_26),A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_80])).

tff(c_104,plain,(
    ! [A_29,B_30] :
      ( k8_relat_1(A_29,B_30) = B_30
      | ~ r1_tarski(k2_relat_1(B_30),A_29)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_110,plain,(
    ! [A_29,A_9] :
      ( k8_relat_1(A_29,k6_relat_1(A_9)) = k6_relat_1(A_9)
      | ~ r1_tarski(A_9,A_29)
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_104])).

tff(c_113,plain,(
    ! [A_31,A_32] :
      ( k7_relat_1(k6_relat_1(A_31),A_32) = k6_relat_1(A_32)
      | ~ r1_tarski(A_32,A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_90,c_110])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( k2_relat_1(k7_relat_1(B_8,A_7)) = k9_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_119,plain,(
    ! [A_31,A_32] :
      ( k9_relat_1(k6_relat_1(A_31),A_32) = k2_relat_1(k6_relat_1(A_32))
      | ~ v1_relat_1(k6_relat_1(A_31))
      | ~ r1_tarski(A_32,A_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_10])).

tff(c_127,plain,(
    ! [A_33,A_34] :
      ( k9_relat_1(k6_relat_1(A_33),A_34) = A_34
      | ~ r1_tarski(A_34,A_33) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_14,c_119])).

tff(c_22,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_133,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_22])).

tff(c_141,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_133])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:38:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.25  
% 1.96/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.25  %$ r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.96/1.25  
% 1.96/1.25  %Foreground sorts:
% 1.96/1.25  
% 1.96/1.25  
% 1.96/1.25  %Background operators:
% 1.96/1.25  
% 1.96/1.25  
% 1.96/1.25  %Foreground operators:
% 1.96/1.25  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.96/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.96/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.25  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.96/1.25  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.96/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.96/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.96/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.96/1.25  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.96/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.96/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.96/1.25  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.96/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.96/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.96/1.25  
% 1.96/1.26  tff(f_60, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 1.96/1.26  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.96/1.26  tff(f_55, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.96/1.26  tff(f_47, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.96/1.26  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 1.96/1.26  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 1.96/1.26  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 1.96/1.26  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.96/1.26  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.96/1.26  tff(c_46, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | ~m1_subset_1(A_19, k1_zfmisc_1(B_20)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.96/1.26  tff(c_54, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_24, c_46])).
% 1.96/1.26  tff(c_18, plain, (![A_12]: (v1_relat_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.96/1.26  tff(c_14, plain, (![A_9]: (k2_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.96/1.26  tff(c_73, plain, (![B_25, A_26]: (k5_relat_1(B_25, k6_relat_1(A_26))=k8_relat_1(A_26, B_25) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.96/1.26  tff(c_16, plain, (![A_10, B_11]: (k5_relat_1(k6_relat_1(A_10), B_11)=k7_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.96/1.26  tff(c_80, plain, (![A_26, A_10]: (k8_relat_1(A_26, k6_relat_1(A_10))=k7_relat_1(k6_relat_1(A_26), A_10) | ~v1_relat_1(k6_relat_1(A_26)) | ~v1_relat_1(k6_relat_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_73, c_16])).
% 1.96/1.26  tff(c_90, plain, (![A_26, A_10]: (k8_relat_1(A_26, k6_relat_1(A_10))=k7_relat_1(k6_relat_1(A_26), A_10))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_80])).
% 1.96/1.26  tff(c_104, plain, (![A_29, B_30]: (k8_relat_1(A_29, B_30)=B_30 | ~r1_tarski(k2_relat_1(B_30), A_29) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.96/1.26  tff(c_110, plain, (![A_29, A_9]: (k8_relat_1(A_29, k6_relat_1(A_9))=k6_relat_1(A_9) | ~r1_tarski(A_9, A_29) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_104])).
% 1.96/1.26  tff(c_113, plain, (![A_31, A_32]: (k7_relat_1(k6_relat_1(A_31), A_32)=k6_relat_1(A_32) | ~r1_tarski(A_32, A_31))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_90, c_110])).
% 1.96/1.26  tff(c_10, plain, (![B_8, A_7]: (k2_relat_1(k7_relat_1(B_8, A_7))=k9_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.96/1.26  tff(c_119, plain, (![A_31, A_32]: (k9_relat_1(k6_relat_1(A_31), A_32)=k2_relat_1(k6_relat_1(A_32)) | ~v1_relat_1(k6_relat_1(A_31)) | ~r1_tarski(A_32, A_31))), inference(superposition, [status(thm), theory('equality')], [c_113, c_10])).
% 1.96/1.26  tff(c_127, plain, (![A_33, A_34]: (k9_relat_1(k6_relat_1(A_33), A_34)=A_34 | ~r1_tarski(A_34, A_33))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_14, c_119])).
% 1.96/1.26  tff(c_22, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.96/1.26  tff(c_133, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_127, c_22])).
% 1.96/1.26  tff(c_141, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_133])).
% 1.96/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.26  
% 1.96/1.26  Inference rules
% 1.96/1.26  ----------------------
% 1.96/1.26  #Ref     : 0
% 1.96/1.26  #Sup     : 24
% 1.96/1.26  #Fact    : 0
% 1.96/1.26  #Define  : 0
% 1.96/1.26  #Split   : 0
% 1.96/1.26  #Chain   : 0
% 1.96/1.26  #Close   : 0
% 1.96/1.26  
% 1.96/1.26  Ordering : KBO
% 1.96/1.26  
% 1.96/1.26  Simplification rules
% 1.96/1.26  ----------------------
% 1.96/1.26  #Subsume      : 0
% 1.96/1.26  #Demod        : 10
% 1.96/1.26  #Tautology    : 17
% 1.96/1.26  #SimpNegUnit  : 0
% 1.96/1.26  #BackRed      : 0
% 1.96/1.26  
% 1.96/1.26  #Partial instantiations: 0
% 1.96/1.26  #Strategies tried      : 1
% 1.96/1.26  
% 1.96/1.26  Timing (in seconds)
% 1.96/1.26  ----------------------
% 1.96/1.27  Preprocessing        : 0.30
% 1.96/1.27  Parsing              : 0.17
% 1.96/1.27  CNF conversion       : 0.02
% 1.96/1.27  Main loop            : 0.13
% 1.96/1.27  Inferencing          : 0.06
% 1.96/1.27  Reduction            : 0.04
% 1.96/1.27  Demodulation         : 0.03
% 1.96/1.27  BG Simplification    : 0.01
% 1.96/1.27  Subsumption          : 0.02
% 1.96/1.27  Abstraction          : 0.01
% 1.96/1.27  MUC search           : 0.00
% 1.96/1.27  Cooper               : 0.00
% 1.96/1.27  Total                : 0.46
% 1.96/1.27  Index Insertion      : 0.00
% 1.96/1.27  Index Deletion       : 0.00
% 1.96/1.27  Index Matching       : 0.00
% 1.96/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
