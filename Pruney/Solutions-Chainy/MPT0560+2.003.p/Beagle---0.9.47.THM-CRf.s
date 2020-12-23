%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:11 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   41 (  47 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :   55 (  69 expanded)
%              Number of equality atoms :   11 (  16 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_65,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B,C] :
            ( r1_tarski(B,C)
           => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_20,plain,(
    ! [B_15,A_14] :
      ( k2_relat_1(k7_relat_1(B_15,A_14)) = k9_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_26,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k7_relat_1(B_17,A_16),B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_31,plain,(
    ! [C_24,A_25] :
      ( r2_hidden(C_24,k1_zfmisc_1(A_25))
      | ~ r1_tarski(C_24,A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_35,plain,(
    ! [C_24,A_25] :
      ( m1_subset_1(C_24,k1_zfmisc_1(A_25))
      | ~ r1_tarski(C_24,A_25) ) ),
    inference(resolution,[status(thm)],[c_31,c_14])).

tff(c_42,plain,(
    ! [B_30,A_31] :
      ( v1_relat_1(B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_31))
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_56,plain,(
    ! [C_34,A_35] :
      ( v1_relat_1(C_34)
      | ~ v1_relat_1(A_35)
      | ~ r1_tarski(C_34,A_35) ) ),
    inference(resolution,[status(thm)],[c_35,c_42])).

tff(c_63,plain,(
    ! [B_17,A_16] :
      ( v1_relat_1(k7_relat_1(B_17,A_16))
      | ~ v1_relat_1(B_17) ) ),
    inference(resolution,[status(thm)],[c_22,c_56])).

tff(c_86,plain,(
    ! [C_42,B_43,A_44] :
      ( k7_relat_1(k7_relat_1(C_42,B_43),A_44) = k7_relat_1(C_42,A_44)
      | ~ r1_tarski(A_44,B_43)
      | ~ v1_relat_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_245,plain,(
    ! [C_76,B_77,A_78] :
      ( k9_relat_1(k7_relat_1(C_76,B_77),A_78) = k2_relat_1(k7_relat_1(C_76,A_78))
      | ~ v1_relat_1(k7_relat_1(C_76,B_77))
      | ~ r1_tarski(A_78,B_77)
      | ~ v1_relat_1(C_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_20])).

tff(c_251,plain,(
    ! [B_79,A_80,A_81] :
      ( k9_relat_1(k7_relat_1(B_79,A_80),A_81) = k2_relat_1(k7_relat_1(B_79,A_81))
      | ~ r1_tarski(A_81,A_80)
      | ~ v1_relat_1(B_79) ) ),
    inference(resolution,[status(thm)],[c_63,c_245])).

tff(c_24,plain,(
    k9_relat_1(k7_relat_1('#skF_3','#skF_5'),'#skF_4') != k9_relat_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_257,plain,
    ( k2_relat_1(k7_relat_1('#skF_3','#skF_4')) != k9_relat_1('#skF_3','#skF_4')
    | ~ r1_tarski('#skF_4','#skF_5')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_24])).

tff(c_266,plain,(
    k2_relat_1(k7_relat_1('#skF_3','#skF_4')) != k9_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_257])).

tff(c_270,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_266])).

tff(c_274,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_270])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:04:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.31  
% 1.91/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.31  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.91/1.31  
% 1.91/1.31  %Foreground sorts:
% 1.91/1.31  
% 1.91/1.31  
% 1.91/1.31  %Background operators:
% 1.91/1.31  
% 1.91/1.31  
% 1.91/1.31  %Foreground operators:
% 1.91/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.91/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.91/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.91/1.31  tff('#skF_5', type, '#skF_5': $i).
% 1.91/1.31  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.91/1.31  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.91/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.91/1.31  tff('#skF_4', type, '#skF_4': $i).
% 1.91/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.91/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.91/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.91/1.31  
% 1.91/1.32  tff(f_65, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 1.91/1.32  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.91/1.32  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 1.91/1.32  tff(f_32, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.91/1.32  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 1.91/1.32  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.91/1.32  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_relat_1)).
% 1.91/1.32  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.91/1.32  tff(c_20, plain, (![B_15, A_14]: (k2_relat_1(k7_relat_1(B_15, A_14))=k9_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.91/1.32  tff(c_26, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.91/1.32  tff(c_22, plain, (![B_17, A_16]: (r1_tarski(k7_relat_1(B_17, A_16), B_17) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.91/1.32  tff(c_31, plain, (![C_24, A_25]: (r2_hidden(C_24, k1_zfmisc_1(A_25)) | ~r1_tarski(C_24, A_25))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.91/1.32  tff(c_14, plain, (![A_6, B_7]: (m1_subset_1(A_6, B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.91/1.32  tff(c_35, plain, (![C_24, A_25]: (m1_subset_1(C_24, k1_zfmisc_1(A_25)) | ~r1_tarski(C_24, A_25))), inference(resolution, [status(thm)], [c_31, c_14])).
% 1.91/1.32  tff(c_42, plain, (![B_30, A_31]: (v1_relat_1(B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(A_31)) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.91/1.32  tff(c_56, plain, (![C_34, A_35]: (v1_relat_1(C_34) | ~v1_relat_1(A_35) | ~r1_tarski(C_34, A_35))), inference(resolution, [status(thm)], [c_35, c_42])).
% 1.91/1.32  tff(c_63, plain, (![B_17, A_16]: (v1_relat_1(k7_relat_1(B_17, A_16)) | ~v1_relat_1(B_17))), inference(resolution, [status(thm)], [c_22, c_56])).
% 1.91/1.32  tff(c_86, plain, (![C_42, B_43, A_44]: (k7_relat_1(k7_relat_1(C_42, B_43), A_44)=k7_relat_1(C_42, A_44) | ~r1_tarski(A_44, B_43) | ~v1_relat_1(C_42))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.91/1.32  tff(c_245, plain, (![C_76, B_77, A_78]: (k9_relat_1(k7_relat_1(C_76, B_77), A_78)=k2_relat_1(k7_relat_1(C_76, A_78)) | ~v1_relat_1(k7_relat_1(C_76, B_77)) | ~r1_tarski(A_78, B_77) | ~v1_relat_1(C_76))), inference(superposition, [status(thm), theory('equality')], [c_86, c_20])).
% 1.91/1.32  tff(c_251, plain, (![B_79, A_80, A_81]: (k9_relat_1(k7_relat_1(B_79, A_80), A_81)=k2_relat_1(k7_relat_1(B_79, A_81)) | ~r1_tarski(A_81, A_80) | ~v1_relat_1(B_79))), inference(resolution, [status(thm)], [c_63, c_245])).
% 1.91/1.32  tff(c_24, plain, (k9_relat_1(k7_relat_1('#skF_3', '#skF_5'), '#skF_4')!=k9_relat_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.91/1.32  tff(c_257, plain, (k2_relat_1(k7_relat_1('#skF_3', '#skF_4'))!=k9_relat_1('#skF_3', '#skF_4') | ~r1_tarski('#skF_4', '#skF_5') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_251, c_24])).
% 1.91/1.32  tff(c_266, plain, (k2_relat_1(k7_relat_1('#skF_3', '#skF_4'))!=k9_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_257])).
% 1.91/1.32  tff(c_270, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20, c_266])).
% 1.91/1.32  tff(c_274, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_270])).
% 1.91/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.32  
% 1.91/1.32  Inference rules
% 1.91/1.32  ----------------------
% 1.91/1.32  #Ref     : 0
% 1.91/1.32  #Sup     : 50
% 1.91/1.32  #Fact    : 0
% 1.91/1.32  #Define  : 0
% 1.91/1.32  #Split   : 1
% 1.91/1.32  #Chain   : 0
% 1.91/1.32  #Close   : 0
% 1.91/1.32  
% 1.91/1.32  Ordering : KBO
% 1.91/1.32  
% 1.91/1.32  Simplification rules
% 1.91/1.32  ----------------------
% 1.91/1.32  #Subsume      : 7
% 1.91/1.32  #Demod        : 3
% 1.91/1.32  #Tautology    : 13
% 1.91/1.32  #SimpNegUnit  : 0
% 1.91/1.32  #BackRed      : 0
% 1.91/1.32  
% 1.91/1.32  #Partial instantiations: 0
% 1.91/1.32  #Strategies tried      : 1
% 1.91/1.32  
% 1.91/1.32  Timing (in seconds)
% 1.91/1.32  ----------------------
% 1.91/1.32  Preprocessing        : 0.29
% 1.91/1.32  Parsing              : 0.16
% 1.91/1.32  CNF conversion       : 0.02
% 1.91/1.32  Main loop            : 0.23
% 1.91/1.32  Inferencing          : 0.10
% 1.91/1.32  Reduction            : 0.05
% 1.91/1.32  Demodulation         : 0.03
% 1.91/1.32  BG Simplification    : 0.01
% 1.91/1.32  Subsumption          : 0.05
% 1.91/1.32  Abstraction          : 0.01
% 1.91/1.33  MUC search           : 0.00
% 1.91/1.33  Cooper               : 0.00
% 1.91/1.33  Total                : 0.55
% 1.91/1.33  Index Insertion      : 0.00
% 1.91/1.33  Index Deletion       : 0.00
% 1.91/1.33  Index Matching       : 0.00
% 1.91/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
