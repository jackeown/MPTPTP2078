%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:53 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   36 (  42 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   48 (  62 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k7_relat_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k7_relat_1(C,A),k7_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_20,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k7_relat_1(B_15,A_14),B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_30,plain,(
    ! [C_22,A_23] :
      ( r2_hidden(C_22,k1_zfmisc_1(A_23))
      | ~ r1_tarski(C_22,A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_38,plain,(
    ! [C_22,A_23] :
      ( m1_subset_1(C_22,k1_zfmisc_1(A_23))
      | ~ r1_tarski(C_22,A_23) ) ),
    inference(resolution,[status(thm)],[c_30,c_14])).

tff(c_40,plain,(
    ! [B_26,A_27] :
      ( v1_relat_1(B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_27))
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_46,plain,(
    ! [C_30,A_31] :
      ( v1_relat_1(C_30)
      | ~ v1_relat_1(A_31)
      | ~ r1_tarski(C_30,A_31) ) ),
    inference(resolution,[status(thm)],[c_38,c_40])).

tff(c_53,plain,(
    ! [B_15,A_14] :
      ( v1_relat_1(k7_relat_1(B_15,A_14))
      | ~ v1_relat_1(B_15) ) ),
    inference(resolution,[status(thm)],[c_20,c_46])).

tff(c_24,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_57,plain,(
    ! [C_34,B_35,A_36] :
      ( k7_relat_1(k7_relat_1(C_34,B_35),A_36) = k7_relat_1(C_34,A_36)
      | ~ r1_tarski(A_36,B_35)
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_160,plain,(
    ! [C_55,A_56,B_57] :
      ( r1_tarski(k7_relat_1(C_55,A_56),k7_relat_1(C_55,B_57))
      | ~ v1_relat_1(k7_relat_1(C_55,B_57))
      | ~ r1_tarski(A_56,B_57)
      | ~ v1_relat_1(C_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_20])).

tff(c_22,plain,(
    ~ r1_tarski(k7_relat_1('#skF_5','#skF_3'),k7_relat_1('#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_166,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_5','#skF_4'))
    | ~ r1_tarski('#skF_3','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_160,c_22])).

tff(c_176,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_166])).

tff(c_179,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_53,c_176])).

tff(c_183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_179])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:05:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.20  
% 1.94/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.21  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k7_relat_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.94/1.21  
% 1.94/1.21  %Foreground sorts:
% 1.94/1.21  
% 1.94/1.21  
% 1.94/1.21  %Background operators:
% 1.94/1.21  
% 1.94/1.21  
% 1.94/1.21  %Foreground operators:
% 1.94/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.94/1.21  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.94/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.94/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.94/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.94/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.94/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.94/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.94/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.94/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.94/1.21  
% 1.94/1.21  tff(f_60, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t104_relat_1)).
% 1.94/1.21  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 1.94/1.21  tff(f_32, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.94/1.21  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 1.94/1.21  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.94/1.21  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_relat_1)).
% 1.94/1.21  tff(c_26, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.94/1.21  tff(c_20, plain, (![B_15, A_14]: (r1_tarski(k7_relat_1(B_15, A_14), B_15) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.94/1.21  tff(c_30, plain, (![C_22, A_23]: (r2_hidden(C_22, k1_zfmisc_1(A_23)) | ~r1_tarski(C_22, A_23))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.94/1.21  tff(c_14, plain, (![A_6, B_7]: (m1_subset_1(A_6, B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.94/1.21  tff(c_38, plain, (![C_22, A_23]: (m1_subset_1(C_22, k1_zfmisc_1(A_23)) | ~r1_tarski(C_22, A_23))), inference(resolution, [status(thm)], [c_30, c_14])).
% 1.94/1.21  tff(c_40, plain, (![B_26, A_27]: (v1_relat_1(B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(A_27)) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.94/1.21  tff(c_46, plain, (![C_30, A_31]: (v1_relat_1(C_30) | ~v1_relat_1(A_31) | ~r1_tarski(C_30, A_31))), inference(resolution, [status(thm)], [c_38, c_40])).
% 1.94/1.21  tff(c_53, plain, (![B_15, A_14]: (v1_relat_1(k7_relat_1(B_15, A_14)) | ~v1_relat_1(B_15))), inference(resolution, [status(thm)], [c_20, c_46])).
% 1.94/1.21  tff(c_24, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.94/1.21  tff(c_57, plain, (![C_34, B_35, A_36]: (k7_relat_1(k7_relat_1(C_34, B_35), A_36)=k7_relat_1(C_34, A_36) | ~r1_tarski(A_36, B_35) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.94/1.21  tff(c_160, plain, (![C_55, A_56, B_57]: (r1_tarski(k7_relat_1(C_55, A_56), k7_relat_1(C_55, B_57)) | ~v1_relat_1(k7_relat_1(C_55, B_57)) | ~r1_tarski(A_56, B_57) | ~v1_relat_1(C_55))), inference(superposition, [status(thm), theory('equality')], [c_57, c_20])).
% 1.94/1.21  tff(c_22, plain, (~r1_tarski(k7_relat_1('#skF_5', '#skF_3'), k7_relat_1('#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.94/1.21  tff(c_166, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_4')) | ~r1_tarski('#skF_3', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_160, c_22])).
% 1.94/1.21  tff(c_176, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_166])).
% 1.94/1.21  tff(c_179, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_53, c_176])).
% 1.94/1.21  tff(c_183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_179])).
% 1.94/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.21  
% 1.94/1.21  Inference rules
% 1.94/1.21  ----------------------
% 1.94/1.21  #Ref     : 0
% 1.94/1.21  #Sup     : 32
% 1.94/1.21  #Fact    : 0
% 1.94/1.21  #Define  : 0
% 1.94/1.21  #Split   : 1
% 1.94/1.21  #Chain   : 0
% 1.94/1.21  #Close   : 0
% 1.94/1.21  
% 1.94/1.21  Ordering : KBO
% 1.94/1.21  
% 1.94/1.21  Simplification rules
% 1.94/1.21  ----------------------
% 1.94/1.21  #Subsume      : 3
% 1.94/1.21  #Demod        : 3
% 1.94/1.21  #Tautology    : 5
% 1.94/1.21  #SimpNegUnit  : 0
% 1.94/1.21  #BackRed      : 0
% 1.94/1.21  
% 1.94/1.21  #Partial instantiations: 0
% 1.94/1.21  #Strategies tried      : 1
% 1.94/1.21  
% 1.94/1.21  Timing (in seconds)
% 1.94/1.21  ----------------------
% 1.94/1.22  Preprocessing        : 0.28
% 1.94/1.22  Parsing              : 0.15
% 1.94/1.22  CNF conversion       : 0.02
% 1.94/1.22  Main loop            : 0.18
% 1.94/1.22  Inferencing          : 0.08
% 1.94/1.22  Reduction            : 0.04
% 1.94/1.22  Demodulation         : 0.03
% 1.94/1.22  BG Simplification    : 0.01
% 1.94/1.22  Subsumption          : 0.03
% 1.94/1.22  Abstraction          : 0.01
% 1.94/1.22  MUC search           : 0.00
% 1.94/1.22  Cooper               : 0.00
% 1.94/1.22  Total                : 0.48
% 1.94/1.22  Index Insertion      : 0.00
% 1.94/1.22  Index Deletion       : 0.00
% 1.94/1.22  Index Matching       : 0.00
% 1.94/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
