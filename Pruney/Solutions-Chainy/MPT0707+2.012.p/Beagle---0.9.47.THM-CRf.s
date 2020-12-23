%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:17 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   44 (  47 expanded)
%              Number of leaves         :   25 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  44 expanded)
%              Number of equality atoms :   22 (  23 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_51,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_77,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ m1_subset_1(A_20,k1_zfmisc_1(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_81,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_77])).

tff(c_87,plain,(
    ! [A_24,B_25] :
      ( k3_xboole_0(A_24,B_25) = A_24
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_91,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_81,c_87])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_95,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_2])).

tff(c_10,plain,(
    ! [A_7] : v1_relat_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_10] : k2_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_133,plain,(
    ! [A_30,B_31] :
      ( k5_relat_1(k6_relat_1(A_30),B_31) = k7_relat_1(B_31,A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [B_14,A_13] : k5_relat_1(k6_relat_1(B_14),k6_relat_1(A_13)) = k6_relat_1(k3_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_140,plain,(
    ! [A_13,A_30] :
      ( k7_relat_1(k6_relat_1(A_13),A_30) = k6_relat_1(k3_xboole_0(A_13,A_30))
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_20])).

tff(c_153,plain,(
    ! [A_32,A_33] : k7_relat_1(k6_relat_1(A_32),A_33) = k6_relat_1(k3_xboole_0(A_32,A_33)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_140])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( k2_relat_1(k7_relat_1(B_9,A_8)) = k9_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_159,plain,(
    ! [A_32,A_33] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_32,A_33))) = k9_relat_1(k6_relat_1(A_32),A_33)
      | ~ v1_relat_1(k6_relat_1(A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_12])).

tff(c_165,plain,(
    ! [A_32,A_33] : k9_relat_1(k6_relat_1(A_32),A_33) = k3_xboole_0(A_32,A_33) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_16,c_159])).

tff(c_22,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_167,plain,(
    k3_xboole_0('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_22])).

tff(c_170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_167])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:09:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.29  
% 1.72/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.29  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.72/1.29  
% 1.72/1.29  %Foreground sorts:
% 1.72/1.29  
% 1.72/1.29  
% 1.72/1.29  %Background operators:
% 1.72/1.29  
% 1.72/1.29  
% 1.72/1.29  %Foreground operators:
% 1.72/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.29  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.72/1.29  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.72/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.72/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.72/1.29  tff('#skF_2', type, '#skF_2': $i).
% 1.72/1.29  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.72/1.29  tff('#skF_1', type, '#skF_1': $i).
% 1.72/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.72/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.72/1.29  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.72/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.72/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.72/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.72/1.29  
% 1.88/1.30  tff(f_56, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_1)).
% 1.88/1.30  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.88/1.30  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.88/1.30  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.88/1.30  tff(f_37, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.88/1.30  tff(f_45, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.88/1.30  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 1.88/1.30  tff(f_51, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 1.88/1.30  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.88/1.30  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.88/1.30  tff(c_77, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~m1_subset_1(A_20, k1_zfmisc_1(B_21)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.88/1.30  tff(c_81, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_24, c_77])).
% 1.88/1.30  tff(c_87, plain, (![A_24, B_25]: (k3_xboole_0(A_24, B_25)=A_24 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.88/1.30  tff(c_91, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_81, c_87])).
% 1.88/1.30  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.88/1.30  tff(c_95, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_91, c_2])).
% 1.88/1.30  tff(c_10, plain, (![A_7]: (v1_relat_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.88/1.30  tff(c_16, plain, (![A_10]: (k2_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.88/1.30  tff(c_133, plain, (![A_30, B_31]: (k5_relat_1(k6_relat_1(A_30), B_31)=k7_relat_1(B_31, A_30) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.88/1.30  tff(c_20, plain, (![B_14, A_13]: (k5_relat_1(k6_relat_1(B_14), k6_relat_1(A_13))=k6_relat_1(k3_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.88/1.30  tff(c_140, plain, (![A_13, A_30]: (k7_relat_1(k6_relat_1(A_13), A_30)=k6_relat_1(k3_xboole_0(A_13, A_30)) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_133, c_20])).
% 1.88/1.30  tff(c_153, plain, (![A_32, A_33]: (k7_relat_1(k6_relat_1(A_32), A_33)=k6_relat_1(k3_xboole_0(A_32, A_33)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_140])).
% 1.88/1.30  tff(c_12, plain, (![B_9, A_8]: (k2_relat_1(k7_relat_1(B_9, A_8))=k9_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.88/1.30  tff(c_159, plain, (![A_32, A_33]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_32, A_33)))=k9_relat_1(k6_relat_1(A_32), A_33) | ~v1_relat_1(k6_relat_1(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_153, c_12])).
% 1.88/1.30  tff(c_165, plain, (![A_32, A_33]: (k9_relat_1(k6_relat_1(A_32), A_33)=k3_xboole_0(A_32, A_33))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_16, c_159])).
% 1.88/1.30  tff(c_22, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.88/1.30  tff(c_167, plain, (k3_xboole_0('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_165, c_22])).
% 1.88/1.30  tff(c_170, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95, c_167])).
% 1.88/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.30  
% 1.88/1.30  Inference rules
% 1.88/1.30  ----------------------
% 1.88/1.30  #Ref     : 0
% 1.88/1.30  #Sup     : 34
% 1.88/1.30  #Fact    : 0
% 1.88/1.30  #Define  : 0
% 1.88/1.30  #Split   : 0
% 1.88/1.30  #Chain   : 0
% 1.88/1.30  #Close   : 0
% 1.88/1.30  
% 1.88/1.30  Ordering : KBO
% 1.88/1.30  
% 1.88/1.30  Simplification rules
% 1.88/1.30  ----------------------
% 1.88/1.30  #Subsume      : 0
% 1.88/1.30  #Demod        : 9
% 1.88/1.30  #Tautology    : 28
% 1.88/1.30  #SimpNegUnit  : 0
% 1.88/1.30  #BackRed      : 1
% 1.88/1.30  
% 1.88/1.30  #Partial instantiations: 0
% 1.88/1.30  #Strategies tried      : 1
% 1.88/1.30  
% 1.88/1.30  Timing (in seconds)
% 1.88/1.30  ----------------------
% 1.88/1.31  Preprocessing        : 0.27
% 1.88/1.31  Parsing              : 0.14
% 1.88/1.31  CNF conversion       : 0.01
% 1.88/1.31  Main loop            : 0.14
% 1.88/1.31  Inferencing          : 0.06
% 1.88/1.31  Reduction            : 0.04
% 1.88/1.31  Demodulation         : 0.03
% 1.88/1.31  BG Simplification    : 0.01
% 1.88/1.31  Subsumption          : 0.02
% 1.88/1.31  Abstraction          : 0.01
% 1.88/1.31  MUC search           : 0.00
% 1.88/1.31  Cooper               : 0.00
% 1.88/1.31  Total                : 0.43
% 1.88/1.31  Index Insertion      : 0.00
% 1.88/1.31  Index Deletion       : 0.00
% 1.88/1.31  Index Matching       : 0.00
% 1.88/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
