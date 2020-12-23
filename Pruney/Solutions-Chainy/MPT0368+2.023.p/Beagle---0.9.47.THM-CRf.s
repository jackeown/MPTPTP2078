%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:51 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   32 (  41 expanded)
%              Number of leaves         :   15 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :   56 (  86 expanded)
%              Number of equality atoms :   11 (  18 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( ! [C] :
              ( m1_subset_1(C,A)
             => r2_hidden(C,B) )
         => A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                <=> r2_hidden(D,C) ) )
           => B = C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_18,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_23,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8,plain,(
    ! [A_7,B_8,C_12] :
      ( m1_subset_1('#skF_1'(A_7,B_8,C_12),A_7)
      | C_12 = B_8
      | ~ m1_subset_1(C_12,k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_20,plain,(
    ! [C_15] :
      ( r2_hidden(C_15,'#skF_3')
      | ~ m1_subset_1(C_15,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_35,plain,(
    ! [C_19,A_20,B_21] :
      ( r2_hidden(C_19,A_20)
      | ~ r2_hidden(C_19,B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_39,plain,(
    ! [C_22,A_23] :
      ( r2_hidden(C_22,A_23)
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_23))
      | ~ m1_subset_1(C_22,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20,c_35])).

tff(c_45,plain,(
    ! [C_22] :
      ( r2_hidden(C_22,'#skF_2')
      | ~ m1_subset_1(C_22,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_39])).

tff(c_80,plain,(
    ! [A_33,B_34,C_35] :
      ( ~ r2_hidden('#skF_1'(A_33,B_34,C_35),C_35)
      | ~ r2_hidden('#skF_1'(A_33,B_34,C_35),B_34)
      | C_35 = B_34
      | ~ m1_subset_1(C_35,k1_zfmisc_1(A_33))
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_93,plain,(
    ! [A_36,B_37] :
      ( ~ r2_hidden('#skF_1'(A_36,B_37,'#skF_3'),B_37)
      | B_37 = '#skF_3'
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_36))
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_36))
      | ~ m1_subset_1('#skF_1'(A_36,B_37,'#skF_3'),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20,c_80])).

tff(c_103,plain,(
    ! [A_36] :
      ( '#skF_2' = '#skF_3'
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_36))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(A_36))
      | ~ m1_subset_1('#skF_1'(A_36,'#skF_2','#skF_3'),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_45,c_93])).

tff(c_114,plain,(
    ! [A_38] :
      ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_38))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1(A_38))
      | ~ m1_subset_1('#skF_1'(A_38,'#skF_2','#skF_3'),'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_103])).

tff(c_118,plain,
    ( '#skF_2' = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_8,c_114])).

tff(c_121,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23,c_22,c_118])).

tff(c_123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_121])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:25:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.21  
% 1.81/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.21  %$ r2_hidden > m1_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 1.81/1.21  
% 1.81/1.21  %Foreground sorts:
% 1.81/1.21  
% 1.81/1.21  
% 1.81/1.21  %Background operators:
% 1.81/1.21  
% 1.81/1.21  
% 1.81/1.21  %Foreground operators:
% 1.81/1.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.81/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.81/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.81/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.81/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.21  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 1.81/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.81/1.21  
% 1.81/1.22  tff(f_60, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_subset_1)).
% 1.81/1.22  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 1.81/1.22  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 1.81/1.22  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_subset_1)).
% 1.81/1.22  tff(f_36, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 1.81/1.22  tff(c_18, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.81/1.22  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.81/1.22  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.81/1.22  tff(c_23, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 1.81/1.22  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.81/1.22  tff(c_8, plain, (![A_7, B_8, C_12]: (m1_subset_1('#skF_1'(A_7, B_8, C_12), A_7) | C_12=B_8 | ~m1_subset_1(C_12, k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.81/1.22  tff(c_20, plain, (![C_15]: (r2_hidden(C_15, '#skF_3') | ~m1_subset_1(C_15, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.81/1.22  tff(c_35, plain, (![C_19, A_20, B_21]: (r2_hidden(C_19, A_20) | ~r2_hidden(C_19, B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.81/1.22  tff(c_39, plain, (![C_22, A_23]: (r2_hidden(C_22, A_23) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_23)) | ~m1_subset_1(C_22, '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_35])).
% 1.81/1.22  tff(c_45, plain, (![C_22]: (r2_hidden(C_22, '#skF_2') | ~m1_subset_1(C_22, '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_39])).
% 1.81/1.22  tff(c_80, plain, (![A_33, B_34, C_35]: (~r2_hidden('#skF_1'(A_33, B_34, C_35), C_35) | ~r2_hidden('#skF_1'(A_33, B_34, C_35), B_34) | C_35=B_34 | ~m1_subset_1(C_35, k1_zfmisc_1(A_33)) | ~m1_subset_1(B_34, k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.81/1.22  tff(c_93, plain, (![A_36, B_37]: (~r2_hidden('#skF_1'(A_36, B_37, '#skF_3'), B_37) | B_37='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_36)) | ~m1_subset_1(B_37, k1_zfmisc_1(A_36)) | ~m1_subset_1('#skF_1'(A_36, B_37, '#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_80])).
% 1.81/1.22  tff(c_103, plain, (![A_36]: ('#skF_2'='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_36)) | ~m1_subset_1('#skF_2', k1_zfmisc_1(A_36)) | ~m1_subset_1('#skF_1'(A_36, '#skF_2', '#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_45, c_93])).
% 1.81/1.22  tff(c_114, plain, (![A_38]: (~m1_subset_1('#skF_3', k1_zfmisc_1(A_38)) | ~m1_subset_1('#skF_2', k1_zfmisc_1(A_38)) | ~m1_subset_1('#skF_1'(A_38, '#skF_2', '#skF_3'), '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_18, c_103])).
% 1.81/1.22  tff(c_118, plain, ('#skF_2'='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_8, c_114])).
% 1.81/1.22  tff(c_121, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_23, c_22, c_118])).
% 1.81/1.22  tff(c_123, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_121])).
% 1.81/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.22  
% 1.81/1.22  Inference rules
% 1.81/1.22  ----------------------
% 1.81/1.22  #Ref     : 0
% 1.81/1.22  #Sup     : 16
% 1.81/1.22  #Fact    : 2
% 1.81/1.22  #Define  : 0
% 1.81/1.22  #Split   : 0
% 1.81/1.22  #Chain   : 0
% 1.81/1.22  #Close   : 0
% 1.81/1.22  
% 1.81/1.22  Ordering : KBO
% 1.81/1.22  
% 1.81/1.22  Simplification rules
% 1.81/1.22  ----------------------
% 1.81/1.22  #Subsume      : 3
% 1.81/1.22  #Demod        : 3
% 1.81/1.22  #Tautology    : 8
% 1.81/1.22  #SimpNegUnit  : 2
% 1.81/1.22  #BackRed      : 0
% 1.81/1.22  
% 1.81/1.22  #Partial instantiations: 0
% 1.81/1.22  #Strategies tried      : 1
% 1.81/1.22  
% 1.81/1.22  Timing (in seconds)
% 1.81/1.22  ----------------------
% 1.81/1.23  Preprocessing        : 0.35
% 1.81/1.23  Parsing              : 0.21
% 1.81/1.23  CNF conversion       : 0.02
% 1.81/1.23  Main loop            : 0.16
% 1.81/1.23  Inferencing          : 0.07
% 1.81/1.23  Reduction            : 0.04
% 1.81/1.23  Demodulation         : 0.03
% 1.81/1.23  BG Simplification    : 0.02
% 1.81/1.23  Subsumption          : 0.03
% 1.81/1.23  Abstraction          : 0.01
% 1.81/1.23  MUC search           : 0.00
% 1.81/1.23  Cooper               : 0.00
% 1.81/1.23  Total                : 0.54
% 1.81/1.23  Index Insertion      : 0.00
% 1.81/1.23  Index Deletion       : 0.00
% 1.81/1.23  Index Matching       : 0.00
% 1.81/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
