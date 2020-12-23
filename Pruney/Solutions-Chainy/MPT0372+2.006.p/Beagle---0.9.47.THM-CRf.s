%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:56 EST 2020

% Result     : Theorem 1.69s
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
                 => ~ ( r2_hidden(D,B)
                    <=> r2_hidden(D,C) ) )
             => B = k3_subset_1(A,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( ~ r2_hidden(D,B)
                <=> r2_hidden(D,C) ) )
           => B = k3_subset_1(A,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_subset_1)).

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

tff(c_24,plain,(
    ! [D_12] :
      ( r2_hidden(D_12,'#skF_3')
      | r2_hidden(D_12,'#skF_4')
      | ~ m1_subset_1(D_12,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_37,plain,(
    ! [A_21,B_22,C_23] :
      ( ~ r2_hidden('#skF_1'(A_21,B_22,C_23),B_22)
      | r2_hidden('#skF_1'(A_21,B_22,C_23),C_23)
      | k3_subset_1(A_21,C_23) = B_22
      | ~ m1_subset_1(C_23,k1_zfmisc_1(A_21))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_41,plain,(
    ! [A_21,C_23] :
      ( r2_hidden('#skF_1'(A_21,'#skF_3',C_23),C_23)
      | k3_subset_1(A_21,C_23) = '#skF_3'
      | ~ m1_subset_1(C_23,k1_zfmisc_1(A_21))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_21))
      | r2_hidden('#skF_1'(A_21,'#skF_3',C_23),'#skF_4')
      | ~ m1_subset_1('#skF_1'(A_21,'#skF_3',C_23),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_37])).

tff(c_83,plain,(
    ! [A_21] :
      ( k3_subset_1(A_21,'#skF_4') = '#skF_3'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_21))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_21))
      | ~ m1_subset_1('#skF_1'(A_21,'#skF_3','#skF_4'),'#skF_2')
      | r2_hidden('#skF_1'(A_21,'#skF_3','#skF_4'),'#skF_4') ) ),
    inference(factorization,[status(thm),theory(equality)],[c_41])).

tff(c_102,plain,(
    ! [A_29] :
      ( k3_subset_1(A_29,'#skF_4') = '#skF_3'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_29))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_29))
      | ~ m1_subset_1('#skF_1'(A_29,'#skF_3','#skF_4'),'#skF_2')
      | r2_hidden('#skF_1'(A_29,'#skF_3','#skF_4'),'#skF_4') ) ),
    inference(factorization,[status(thm),theory(equality)],[c_41])).

tff(c_4,plain,(
    ! [A_1,B_2,C_6] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_6),C_6)
      | r2_hidden('#skF_1'(A_1,B_2,C_6),B_2)
      | k3_subset_1(A_1,C_6) = B_2
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_106,plain,(
    ! [A_30] :
      ( r2_hidden('#skF_1'(A_30,'#skF_3','#skF_4'),'#skF_3')
      | k3_subset_1(A_30,'#skF_4') = '#skF_3'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_30))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_30))
      | ~ m1_subset_1('#skF_1'(A_30,'#skF_3','#skF_4'),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_102,c_4])).

tff(c_18,plain,(
    ! [D_12] :
      ( ~ r2_hidden(D_12,'#skF_4')
      | ~ r2_hidden(D_12,'#skF_3')
      | ~ m1_subset_1(D_12,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_122,plain,(
    ! [A_32] :
      ( ~ r2_hidden('#skF_1'(A_32,'#skF_3','#skF_4'),'#skF_4')
      | k3_subset_1(A_32,'#skF_4') = '#skF_3'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_32))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_32))
      | ~ m1_subset_1('#skF_1'(A_32,'#skF_3','#skF_4'),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_106,c_18])).

tff(c_131,plain,(
    ! [A_33] :
      ( k3_subset_1(A_33,'#skF_4') = '#skF_3'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(A_33))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(A_33))
      | ~ m1_subset_1('#skF_1'(A_33,'#skF_3','#skF_4'),'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_83,c_122])).

tff(c_135,plain,
    ( k3_subset_1('#skF_2','#skF_4') = '#skF_3'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_2,c_131])).

tff(c_138,plain,(
    k3_subset_1('#skF_2','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_135])).

tff(c_140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_138])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:01:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.17  
% 1.69/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.17  %$ r2_hidden > m1_subset_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 1.69/1.17  
% 1.69/1.17  %Foreground sorts:
% 1.69/1.17  
% 1.69/1.17  
% 1.69/1.17  %Background operators:
% 1.69/1.17  
% 1.69/1.17  
% 1.69/1.17  %Foreground operators:
% 1.69/1.17  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.69/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.69/1.17  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.69/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.69/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.69/1.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.69/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.69/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.69/1.17  
% 1.99/1.18  tff(f_56, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => ~(r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_subset_1)).
% 1.99/1.18  tff(f_40, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (~r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_subset_1)).
% 1.99/1.18  tff(c_12, plain, (k3_subset_1('#skF_2', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.99/1.18  tff(c_16, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.99/1.18  tff(c_14, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.99/1.18  tff(c_2, plain, (![A_1, B_2, C_6]: (m1_subset_1('#skF_1'(A_1, B_2, C_6), A_1) | k3_subset_1(A_1, C_6)=B_2 | ~m1_subset_1(C_6, k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.99/1.18  tff(c_24, plain, (![D_12]: (r2_hidden(D_12, '#skF_3') | r2_hidden(D_12, '#skF_4') | ~m1_subset_1(D_12, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.99/1.18  tff(c_37, plain, (![A_21, B_22, C_23]: (~r2_hidden('#skF_1'(A_21, B_22, C_23), B_22) | r2_hidden('#skF_1'(A_21, B_22, C_23), C_23) | k3_subset_1(A_21, C_23)=B_22 | ~m1_subset_1(C_23, k1_zfmisc_1(A_21)) | ~m1_subset_1(B_22, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.99/1.18  tff(c_41, plain, (![A_21, C_23]: (r2_hidden('#skF_1'(A_21, '#skF_3', C_23), C_23) | k3_subset_1(A_21, C_23)='#skF_3' | ~m1_subset_1(C_23, k1_zfmisc_1(A_21)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_21)) | r2_hidden('#skF_1'(A_21, '#skF_3', C_23), '#skF_4') | ~m1_subset_1('#skF_1'(A_21, '#skF_3', C_23), '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_37])).
% 1.99/1.18  tff(c_83, plain, (![A_21]: (k3_subset_1(A_21, '#skF_4')='#skF_3' | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_21)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_21)) | ~m1_subset_1('#skF_1'(A_21, '#skF_3', '#skF_4'), '#skF_2') | r2_hidden('#skF_1'(A_21, '#skF_3', '#skF_4'), '#skF_4'))), inference(factorization, [status(thm), theory('equality')], [c_41])).
% 1.99/1.18  tff(c_102, plain, (![A_29]: (k3_subset_1(A_29, '#skF_4')='#skF_3' | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_29)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_29)) | ~m1_subset_1('#skF_1'(A_29, '#skF_3', '#skF_4'), '#skF_2') | r2_hidden('#skF_1'(A_29, '#skF_3', '#skF_4'), '#skF_4'))), inference(factorization, [status(thm), theory('equality')], [c_41])).
% 1.99/1.18  tff(c_4, plain, (![A_1, B_2, C_6]: (~r2_hidden('#skF_1'(A_1, B_2, C_6), C_6) | r2_hidden('#skF_1'(A_1, B_2, C_6), B_2) | k3_subset_1(A_1, C_6)=B_2 | ~m1_subset_1(C_6, k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.99/1.18  tff(c_106, plain, (![A_30]: (r2_hidden('#skF_1'(A_30, '#skF_3', '#skF_4'), '#skF_3') | k3_subset_1(A_30, '#skF_4')='#skF_3' | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_30)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_30)) | ~m1_subset_1('#skF_1'(A_30, '#skF_3', '#skF_4'), '#skF_2'))), inference(resolution, [status(thm)], [c_102, c_4])).
% 1.99/1.18  tff(c_18, plain, (![D_12]: (~r2_hidden(D_12, '#skF_4') | ~r2_hidden(D_12, '#skF_3') | ~m1_subset_1(D_12, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.99/1.18  tff(c_122, plain, (![A_32]: (~r2_hidden('#skF_1'(A_32, '#skF_3', '#skF_4'), '#skF_4') | k3_subset_1(A_32, '#skF_4')='#skF_3' | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_32)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_32)) | ~m1_subset_1('#skF_1'(A_32, '#skF_3', '#skF_4'), '#skF_2'))), inference(resolution, [status(thm)], [c_106, c_18])).
% 1.99/1.18  tff(c_131, plain, (![A_33]: (k3_subset_1(A_33, '#skF_4')='#skF_3' | ~m1_subset_1('#skF_4', k1_zfmisc_1(A_33)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(A_33)) | ~m1_subset_1('#skF_1'(A_33, '#skF_3', '#skF_4'), '#skF_2'))), inference(resolution, [status(thm)], [c_83, c_122])).
% 1.99/1.18  tff(c_135, plain, (k3_subset_1('#skF_2', '#skF_4')='#skF_3' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_2, c_131])).
% 1.99/1.18  tff(c_138, plain, (k3_subset_1('#skF_2', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_135])).
% 1.99/1.18  tff(c_140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_138])).
% 1.99/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.18  
% 1.99/1.18  Inference rules
% 1.99/1.18  ----------------------
% 1.99/1.18  #Ref     : 0
% 1.99/1.18  #Sup     : 17
% 1.99/1.18  #Fact    : 4
% 1.99/1.18  #Define  : 0
% 1.99/1.18  #Split   : 0
% 1.99/1.18  #Chain   : 0
% 1.99/1.18  #Close   : 0
% 1.99/1.18  
% 1.99/1.18  Ordering : KBO
% 1.99/1.18  
% 1.99/1.18  Simplification rules
% 1.99/1.18  ----------------------
% 1.99/1.18  #Subsume      : 11
% 1.99/1.18  #Demod        : 2
% 1.99/1.18  #Tautology    : 7
% 1.99/1.18  #SimpNegUnit  : 1
% 1.99/1.18  #BackRed      : 0
% 1.99/1.18  
% 1.99/1.18  #Partial instantiations: 0
% 1.99/1.18  #Strategies tried      : 1
% 1.99/1.18  
% 1.99/1.18  Timing (in seconds)
% 1.99/1.18  ----------------------
% 2.01/1.19  Preprocessing        : 0.25
% 2.01/1.19  Parsing              : 0.13
% 2.01/1.19  CNF conversion       : 0.02
% 2.01/1.19  Main loop            : 0.18
% 2.01/1.19  Inferencing          : 0.08
% 2.01/1.19  Reduction            : 0.04
% 2.01/1.19  Demodulation         : 0.03
% 2.01/1.19  BG Simplification    : 0.01
% 2.01/1.19  Subsumption          : 0.04
% 2.01/1.19  Abstraction          : 0.01
% 2.01/1.19  MUC search           : 0.00
% 2.01/1.19  Cooper               : 0.00
% 2.01/1.19  Total                : 0.45
% 2.01/1.19  Index Insertion      : 0.00
% 2.01/1.19  Index Deletion       : 0.00
% 2.01/1.19  Index Matching       : 0.00
% 2.01/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
