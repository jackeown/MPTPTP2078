%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:56 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   30 (  41 expanded)
%              Number of leaves         :   13 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :   70 ( 132 expanded)
%              Number of equality atoms :   14 (  24 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ! [D] :
                  ( m1_subset_1(D,A)
                 => ( ~ r2_hidden(D,B)
                  <=> r2_hidden(D,C) ) )
             => B = k3_subset_1(A,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                <=> ~ r2_hidden(D,C) ) )
           => B = k3_subset_1(A,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_subset_1)).

tff(c_12,plain,(
    k3_subset_1('#skF_2','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [A_1,B_2,C_6] :
      ( m1_subset_1('#skF_1'(A_1,B_2,C_6),A_1)
      | k3_subset_1(A_1,C_6) = B_2
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_20,plain,(
    ! [D_12] :
      ( r2_hidden(D_12,'#skF_4')
      | r2_hidden(D_12,'#skF_3')
      | ~ m1_subset_1(D_12,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_28,plain,(
    ! [A_18,B_19,C_20] :
      ( r2_hidden('#skF_1'(A_18,B_19,C_20),C_20)
      | ~ r2_hidden('#skF_1'(A_18,B_19,C_20),B_19)
      | k3_subset_1(A_18,C_20) = B_19
      | ~ m1_subset_1(C_20,k1_zfmisc_1(A_18))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_32,plain,(
    ! [A_18,C_20] :
      ( r2_hidden('#skF_1'(A_18,'#skF_3',C_20),C_20)
      | k3_subset_1(A_18,C_20) = '#skF_3'
      | ~ m1_subset_1(C_20,k1_zfmisc_1(A_18))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_18))
      | r2_hidden('#skF_1'(A_18,'#skF_3',C_20),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_18,'#skF_3',C_20),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_20,c_28])).

tff(c_50,plain,(
    ! [A_18] :
      ( k3_subset_1(A_18,'#skF_4') = '#skF_3'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_18))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_18))
      | ~ m1_subset_1('#skF_1'(A_18,'#skF_3','#skF_4'),'#skF_2')
      | r2_hidden('#skF_1'(A_18,'#skF_3','#skF_4'),'#skF_4') ) ),
    inference(factorization,[status(thm),theory(equality)],[c_32])).

tff(c_94,plain,(
    ! [A_28] :
      ( k3_subset_1(A_28,'#skF_4') = '#skF_3'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_28))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_28))
      | ~ m1_subset_1('#skF_1'(A_28,'#skF_3','#skF_4'),'#skF_2')
      | r2_hidden('#skF_1'(A_28,'#skF_3','#skF_4'),'#skF_4') ) ),
    inference(factorization,[status(thm),theory(equality)],[c_32])).

tff(c_10,plain,(
    ! [A_1,B_2,C_6] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_6),B_2)
      | ~ r2_hidden('#skF_1'(A_1,B_2,C_6),C_6)
      | k3_subset_1(A_1,C_6) = B_2
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_110,plain,(
    ! [A_31] :
      ( r2_hidden('#skF_1'(A_31,'#skF_3','#skF_4'),'#skF_3')
      | k3_subset_1(A_31,'#skF_4') = '#skF_3'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_31))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_31))
      | ~ m1_subset_1('#skF_1'(A_31,'#skF_3','#skF_4'),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_94,c_10])).

tff(c_18,plain,(
    ! [D_12] :
      ( ~ r2_hidden(D_12,'#skF_3')
      | ~ r2_hidden(D_12,'#skF_4')
      | ~ m1_subset_1(D_12,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_139,plain,(
    ! [A_34] :
      ( ~ r2_hidden('#skF_1'(A_34,'#skF_3','#skF_4'),'#skF_4')
      | k3_subset_1(A_34,'#skF_4') = '#skF_3'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_34))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_34))
      | ~ m1_subset_1('#skF_1'(A_34,'#skF_3','#skF_4'),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_110,c_18])).

tff(c_148,plain,(
    ! [A_35] :
      ( k3_subset_1(A_35,'#skF_4') = '#skF_3'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_35))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_35))
      | ~ m1_subset_1('#skF_1'(A_35,'#skF_3','#skF_4'),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_50,c_139])).

tff(c_152,plain,
    ( k3_subset_1('#skF_2','#skF_4') = '#skF_3'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2,c_148])).

tff(c_155,plain,(
    k3_subset_1('#skF_2','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_152])).

tff(c_157,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_155])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:42:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.32  
% 1.99/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.32  %$ r2_hidden > m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 1.99/1.32  
% 1.99/1.32  %Foreground sorts:
% 1.99/1.32  
% 1.99/1.32  
% 1.99/1.32  %Background operators:
% 1.99/1.32  
% 1.99/1.32  
% 1.99/1.32  %Foreground operators:
% 1.99/1.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.99/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.32  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.99/1.32  tff('#skF_2', type, '#skF_2': $i).
% 1.99/1.32  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.99/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.32  tff('#skF_4', type, '#skF_4': $i).
% 1.99/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.99/1.32  
% 1.99/1.33  tff(f_56, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (~r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_subset_1)).
% 1.99/1.33  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) <=> ~r2_hidden(D, C)))) => (B = k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_subset_1)).
% 1.99/1.33  tff(c_12, plain, (k3_subset_1('#skF_2', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.99/1.33  tff(c_16, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.99/1.33  tff(c_14, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.99/1.33  tff(c_2, plain, (![A_1, B_2, C_6]: (m1_subset_1('#skF_1'(A_1, B_2, C_6), A_1) | k3_subset_1(A_1, C_6)=B_2 | ~m1_subset_1(C_6, k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.99/1.33  tff(c_20, plain, (![D_12]: (r2_hidden(D_12, '#skF_4') | r2_hidden(D_12, '#skF_3') | ~m1_subset_1(D_12, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.99/1.33  tff(c_28, plain, (![A_18, B_19, C_20]: (r2_hidden('#skF_1'(A_18, B_19, C_20), C_20) | ~r2_hidden('#skF_1'(A_18, B_19, C_20), B_19) | k3_subset_1(A_18, C_20)=B_19 | ~m1_subset_1(C_20, k1_zfmisc_1(A_18)) | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.99/1.33  tff(c_32, plain, (![A_18, C_20]: (r2_hidden('#skF_1'(A_18, '#skF_3', C_20), C_20) | k3_subset_1(A_18, C_20)='#skF_3' | ~m1_subset_1(C_20, k1_zfmisc_1(A_18)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_18)) | r2_hidden('#skF_1'(A_18, '#skF_3', C_20), '#skF_4') | ~m1_subset_1('#skF_1'(A_18, '#skF_3', C_20), '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_28])).
% 1.99/1.33  tff(c_50, plain, (![A_18]: (k3_subset_1(A_18, '#skF_4')='#skF_3' | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_18)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_18)) | ~m1_subset_1('#skF_1'(A_18, '#skF_3', '#skF_4'), '#skF_2') | r2_hidden('#skF_1'(A_18, '#skF_3', '#skF_4'), '#skF_4'))), inference(factorization, [status(thm), theory('equality')], [c_32])).
% 1.99/1.33  tff(c_94, plain, (![A_28]: (k3_subset_1(A_28, '#skF_4')='#skF_3' | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_28)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_28)) | ~m1_subset_1('#skF_1'(A_28, '#skF_3', '#skF_4'), '#skF_2') | r2_hidden('#skF_1'(A_28, '#skF_3', '#skF_4'), '#skF_4'))), inference(factorization, [status(thm), theory('equality')], [c_32])).
% 1.99/1.33  tff(c_10, plain, (![A_1, B_2, C_6]: (r2_hidden('#skF_1'(A_1, B_2, C_6), B_2) | ~r2_hidden('#skF_1'(A_1, B_2, C_6), C_6) | k3_subset_1(A_1, C_6)=B_2 | ~m1_subset_1(C_6, k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.99/1.33  tff(c_110, plain, (![A_31]: (r2_hidden('#skF_1'(A_31, '#skF_3', '#skF_4'), '#skF_3') | k3_subset_1(A_31, '#skF_4')='#skF_3' | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_31)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_31)) | ~m1_subset_1('#skF_1'(A_31, '#skF_3', '#skF_4'), '#skF_2'))), inference(resolution, [status(thm)], [c_94, c_10])).
% 1.99/1.33  tff(c_18, plain, (![D_12]: (~r2_hidden(D_12, '#skF_3') | ~r2_hidden(D_12, '#skF_4') | ~m1_subset_1(D_12, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.99/1.33  tff(c_139, plain, (![A_34]: (~r2_hidden('#skF_1'(A_34, '#skF_3', '#skF_4'), '#skF_4') | k3_subset_1(A_34, '#skF_4')='#skF_3' | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_34)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_34)) | ~m1_subset_1('#skF_1'(A_34, '#skF_3', '#skF_4'), '#skF_2'))), inference(resolution, [status(thm)], [c_110, c_18])).
% 1.99/1.33  tff(c_148, plain, (![A_35]: (k3_subset_1(A_35, '#skF_4')='#skF_3' | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_35)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_35)) | ~m1_subset_1('#skF_1'(A_35, '#skF_3', '#skF_4'), '#skF_2'))), inference(resolution, [status(thm)], [c_50, c_139])).
% 1.99/1.33  tff(c_152, plain, (k3_subset_1('#skF_2', '#skF_4')='#skF_3' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_2, c_148])).
% 1.99/1.33  tff(c_155, plain, (k3_subset_1('#skF_2', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_152])).
% 1.99/1.33  tff(c_157, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_155])).
% 1.99/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.33  
% 1.99/1.33  Inference rules
% 1.99/1.33  ----------------------
% 1.99/1.33  #Ref     : 0
% 1.99/1.33  #Sup     : 21
% 1.99/1.33  #Fact    : 4
% 1.99/1.33  #Define  : 0
% 1.99/1.33  #Split   : 0
% 1.99/1.33  #Chain   : 0
% 1.99/1.33  #Close   : 0
% 1.99/1.33  
% 1.99/1.33  Ordering : KBO
% 1.99/1.33  
% 1.99/1.33  Simplification rules
% 1.99/1.33  ----------------------
% 1.99/1.33  #Subsume      : 14
% 1.99/1.33  #Demod        : 4
% 1.99/1.33  #Tautology    : 7
% 1.99/1.33  #SimpNegUnit  : 1
% 1.99/1.33  #BackRed      : 0
% 1.99/1.33  
% 1.99/1.33  #Partial instantiations: 0
% 1.99/1.33  #Strategies tried      : 1
% 1.99/1.33  
% 1.99/1.33  Timing (in seconds)
% 1.99/1.33  ----------------------
% 1.99/1.33  Preprocessing        : 0.27
% 1.99/1.33  Parsing              : 0.14
% 1.99/1.33  CNF conversion       : 0.02
% 1.99/1.33  Main loop            : 0.19
% 1.99/1.33  Inferencing          : 0.09
% 1.99/1.33  Reduction            : 0.04
% 1.99/1.33  Demodulation         : 0.03
% 1.99/1.33  BG Simplification    : 0.01
% 1.99/1.33  Subsumption          : 0.05
% 1.99/1.34  Abstraction          : 0.01
% 1.99/1.34  MUC search           : 0.00
% 1.99/1.34  Cooper               : 0.00
% 1.99/1.34  Total                : 0.49
% 1.99/1.34  Index Insertion      : 0.00
% 1.99/1.34  Index Deletion       : 0.00
% 1.99/1.34  Index Matching       : 0.00
% 1.99/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
