%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:19 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   42 (  47 expanded)
%              Number of leaves         :   24 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 (  49 expanded)
%              Number of equality atoms :   20 (  24 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_46,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_52,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_78,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ m1_subset_1(A_20,k1_zfmisc_1(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_82,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_78])).

tff(c_83,plain,(
    ! [A_22,B_23] :
      ( k3_xboole_0(A_22,B_23) = A_22
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_87,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_82,c_83])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_91,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_2])).

tff(c_16,plain,(
    ! [A_11] : v1_relat_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    ! [A_10] : k2_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_20,plain,(
    ! [B_13,A_12] : k5_relat_1(k6_relat_1(B_13),k6_relat_1(A_12)) = k6_relat_1(k3_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_125,plain,(
    ! [B_28,A_29] :
      ( k9_relat_1(B_28,k2_relat_1(A_29)) = k2_relat_1(k5_relat_1(A_29,B_28))
      | ~ v1_relat_1(B_28)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_134,plain,(
    ! [A_10,B_28] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_10),B_28)) = k9_relat_1(B_28,A_10)
      | ~ v1_relat_1(B_28)
      | ~ v1_relat_1(k6_relat_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_125])).

tff(c_139,plain,(
    ! [A_30,B_31] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_30),B_31)) = k9_relat_1(B_31,A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_134])).

tff(c_151,plain,(
    ! [A_12,B_13] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_12,B_13))) = k9_relat_1(k6_relat_1(A_12),B_13)
      | ~ v1_relat_1(k6_relat_1(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_139])).

tff(c_155,plain,(
    ! [A_12,B_13] : k9_relat_1(k6_relat_1(A_12),B_13) = k3_xboole_0(A_12,B_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_151])).

tff(c_22,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_173,plain,(
    k3_xboole_0('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_22])).

tff(c_176,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_173])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:41:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.17  
% 1.66/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.17  %$ r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > k9_relat_1 > k5_relat_1 > k3_xboole_0 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.66/1.17  
% 1.66/1.17  %Foreground sorts:
% 1.66/1.17  
% 1.66/1.17  
% 1.66/1.17  %Background operators:
% 1.66/1.17  
% 1.66/1.17  
% 1.66/1.17  %Foreground operators:
% 1.66/1.17  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.66/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.17  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.66/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.66/1.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.66/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.17  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.66/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.66/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.66/1.17  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.66/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.66/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.66/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.66/1.17  
% 1.90/1.18  tff(f_57, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 1.90/1.18  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 1.90/1.18  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.90/1.18  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.90/1.18  tff(f_50, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 1.90/1.18  tff(f_46, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.90/1.18  tff(f_52, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 1.90/1.18  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 1.90/1.18  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.90/1.18  tff(c_78, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~m1_subset_1(A_20, k1_zfmisc_1(B_21)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.90/1.18  tff(c_82, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_24, c_78])).
% 1.90/1.18  tff(c_83, plain, (![A_22, B_23]: (k3_xboole_0(A_22, B_23)=A_22 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.90/1.18  tff(c_87, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_82, c_83])).
% 1.90/1.18  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.90/1.18  tff(c_91, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_87, c_2])).
% 1.90/1.18  tff(c_16, plain, (![A_11]: (v1_relat_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.90/1.18  tff(c_14, plain, (![A_10]: (k2_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.90/1.18  tff(c_20, plain, (![B_13, A_12]: (k5_relat_1(k6_relat_1(B_13), k6_relat_1(A_12))=k6_relat_1(k3_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.90/1.18  tff(c_125, plain, (![B_28, A_29]: (k9_relat_1(B_28, k2_relat_1(A_29))=k2_relat_1(k5_relat_1(A_29, B_28)) | ~v1_relat_1(B_28) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.90/1.18  tff(c_134, plain, (![A_10, B_28]: (k2_relat_1(k5_relat_1(k6_relat_1(A_10), B_28))=k9_relat_1(B_28, A_10) | ~v1_relat_1(B_28) | ~v1_relat_1(k6_relat_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_125])).
% 1.90/1.18  tff(c_139, plain, (![A_30, B_31]: (k2_relat_1(k5_relat_1(k6_relat_1(A_30), B_31))=k9_relat_1(B_31, A_30) | ~v1_relat_1(B_31))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_134])).
% 1.90/1.18  tff(c_151, plain, (![A_12, B_13]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_12, B_13)))=k9_relat_1(k6_relat_1(A_12), B_13) | ~v1_relat_1(k6_relat_1(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_139])).
% 1.90/1.18  tff(c_155, plain, (![A_12, B_13]: (k9_relat_1(k6_relat_1(A_12), B_13)=k3_xboole_0(A_12, B_13))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_151])).
% 1.90/1.18  tff(c_22, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.90/1.18  tff(c_173, plain, (k3_xboole_0('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_155, c_22])).
% 1.90/1.18  tff(c_176, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_173])).
% 1.90/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.18  
% 1.90/1.18  Inference rules
% 1.90/1.18  ----------------------
% 1.90/1.18  #Ref     : 0
% 1.90/1.18  #Sup     : 36
% 1.90/1.18  #Fact    : 0
% 1.90/1.18  #Define  : 0
% 1.90/1.18  #Split   : 0
% 1.90/1.18  #Chain   : 0
% 1.90/1.18  #Close   : 0
% 1.90/1.18  
% 1.90/1.18  Ordering : KBO
% 1.90/1.18  
% 1.90/1.18  Simplification rules
% 1.90/1.18  ----------------------
% 1.90/1.18  #Subsume      : 0
% 1.90/1.18  #Demod        : 11
% 1.90/1.18  #Tautology    : 28
% 1.90/1.18  #SimpNegUnit  : 0
% 1.90/1.18  #BackRed      : 1
% 1.90/1.18  
% 1.90/1.18  #Partial instantiations: 0
% 1.90/1.18  #Strategies tried      : 1
% 1.90/1.18  
% 1.90/1.18  Timing (in seconds)
% 1.90/1.18  ----------------------
% 1.90/1.18  Preprocessing        : 0.28
% 1.90/1.18  Parsing              : 0.15
% 1.90/1.19  CNF conversion       : 0.02
% 1.90/1.19  Main loop            : 0.14
% 1.90/1.19  Inferencing          : 0.06
% 1.90/1.19  Reduction            : 0.05
% 1.90/1.19  Demodulation         : 0.04
% 1.90/1.19  BG Simplification    : 0.01
% 1.90/1.19  Subsumption          : 0.02
% 1.90/1.19  Abstraction          : 0.01
% 1.90/1.19  MUC search           : 0.00
% 1.90/1.19  Cooper               : 0.00
% 1.90/1.19  Total                : 0.45
% 1.90/1.19  Index Insertion      : 0.00
% 1.90/1.19  Index Deletion       : 0.00
% 1.90/1.19  Index Matching       : 0.00
% 1.90/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
