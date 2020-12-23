%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:44 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   40 (  68 expanded)
%              Number of leaves         :   18 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   59 ( 150 expanded)
%              Number of equality atoms :    5 (  16 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(A))
                 => ( r2_hidden(D,B)
                  <=> r2_hidden(D,C) ) )
             => B = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_setfam_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_20,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_xboole_0(A_6,B_7)
      | B_7 = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_2'(A_8,B_9),B_9)
      | ~ r2_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_65,plain,(
    ! [A_37,C_38,B_39] :
      ( m1_subset_1(A_37,C_38)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(C_38))
      | ~ r2_hidden(A_37,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_70,plain,(
    ! [A_37] :
      ( m1_subset_1(A_37,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_37,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_65])).

tff(c_80,plain,(
    ! [D_41] :
      ( r2_hidden(D_41,'#skF_4')
      | ~ r2_hidden(D_41,'#skF_5')
      | ~ m1_subset_1(D_41,k1_zfmisc_1('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_85,plain,(
    ! [A_42] :
      ( r2_hidden(A_42,'#skF_4')
      | ~ r2_hidden(A_42,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_70,c_80])).

tff(c_131,plain,(
    ! [A_46] :
      ( r2_hidden('#skF_2'(A_46,'#skF_5'),'#skF_4')
      | ~ r2_xboole_0(A_46,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_16,c_85])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9),A_8)
      | ~ r2_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_139,plain,(
    ~ r2_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_131,c_14])).

tff(c_142,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_139])).

tff(c_145,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_142])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_96,plain,(
    ! [A_43] :
      ( m1_subset_1(A_43,k1_zfmisc_1('#skF_3'))
      | ~ r2_hidden(A_43,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_65])).

tff(c_28,plain,(
    ! [D_18] :
      ( r2_hidden(D_18,'#skF_5')
      | ~ r2_hidden(D_18,'#skF_4')
      | ~ m1_subset_1(D_18,k1_zfmisc_1('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_104,plain,(
    ! [A_44] :
      ( r2_hidden(A_44,'#skF_5')
      | ~ r2_hidden(A_44,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_96,c_28])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_146,plain,(
    ! [A_47] :
      ( r1_tarski(A_47,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_47,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_104,c_4])).

tff(c_154,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_146])).

tff(c_160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_145,c_154])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:14:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.16  
% 1.64/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.16  %$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.64/1.16  
% 1.64/1.16  %Foreground sorts:
% 1.64/1.16  
% 1.64/1.16  
% 1.64/1.16  %Background operators:
% 1.64/1.16  
% 1.64/1.16  
% 1.64/1.16  %Foreground operators:
% 1.64/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.64/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.64/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.64/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.64/1.16  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.64/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.64/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.64/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.64/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.64/1.17  
% 1.89/1.17  tff(f_70, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_setfam_1)).
% 1.89/1.17  tff(f_39, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.89/1.17  tff(f_49, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 1.89/1.17  tff(f_55, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 1.89/1.17  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.89/1.17  tff(c_20, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.89/1.17  tff(c_8, plain, (![A_6, B_7]: (r2_xboole_0(A_6, B_7) | B_7=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.89/1.17  tff(c_16, plain, (![A_8, B_9]: (r2_hidden('#skF_2'(A_8, B_9), B_9) | ~r2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.89/1.17  tff(c_22, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.89/1.17  tff(c_65, plain, (![A_37, C_38, B_39]: (m1_subset_1(A_37, C_38) | ~m1_subset_1(B_39, k1_zfmisc_1(C_38)) | ~r2_hidden(A_37, B_39))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.89/1.17  tff(c_70, plain, (![A_37]: (m1_subset_1(A_37, k1_zfmisc_1('#skF_3')) | ~r2_hidden(A_37, '#skF_5'))), inference(resolution, [status(thm)], [c_22, c_65])).
% 1.89/1.17  tff(c_80, plain, (![D_41]: (r2_hidden(D_41, '#skF_4') | ~r2_hidden(D_41, '#skF_5') | ~m1_subset_1(D_41, k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.89/1.17  tff(c_85, plain, (![A_42]: (r2_hidden(A_42, '#skF_4') | ~r2_hidden(A_42, '#skF_5'))), inference(resolution, [status(thm)], [c_70, c_80])).
% 1.89/1.17  tff(c_131, plain, (![A_46]: (r2_hidden('#skF_2'(A_46, '#skF_5'), '#skF_4') | ~r2_xboole_0(A_46, '#skF_5'))), inference(resolution, [status(thm)], [c_16, c_85])).
% 1.89/1.17  tff(c_14, plain, (![A_8, B_9]: (~r2_hidden('#skF_2'(A_8, B_9), A_8) | ~r2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.89/1.17  tff(c_139, plain, (~r2_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_131, c_14])).
% 1.89/1.17  tff(c_142, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_8, c_139])).
% 1.89/1.17  tff(c_145, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_20, c_142])).
% 1.89/1.17  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.89/1.17  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.89/1.17  tff(c_96, plain, (![A_43]: (m1_subset_1(A_43, k1_zfmisc_1('#skF_3')) | ~r2_hidden(A_43, '#skF_4'))), inference(resolution, [status(thm)], [c_24, c_65])).
% 1.89/1.17  tff(c_28, plain, (![D_18]: (r2_hidden(D_18, '#skF_5') | ~r2_hidden(D_18, '#skF_4') | ~m1_subset_1(D_18, k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.89/1.17  tff(c_104, plain, (![A_44]: (r2_hidden(A_44, '#skF_5') | ~r2_hidden(A_44, '#skF_4'))), inference(resolution, [status(thm)], [c_96, c_28])).
% 1.89/1.17  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.89/1.17  tff(c_146, plain, (![A_47]: (r1_tarski(A_47, '#skF_5') | ~r2_hidden('#skF_1'(A_47, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_104, c_4])).
% 1.89/1.17  tff(c_154, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_146])).
% 1.89/1.17  tff(c_160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_145, c_145, c_154])).
% 1.89/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.17  
% 1.89/1.17  Inference rules
% 1.89/1.17  ----------------------
% 1.89/1.17  #Ref     : 0
% 1.89/1.17  #Sup     : 26
% 1.89/1.17  #Fact    : 0
% 1.89/1.17  #Define  : 0
% 1.89/1.17  #Split   : 0
% 1.89/1.17  #Chain   : 0
% 1.89/1.18  #Close   : 0
% 1.89/1.18  
% 1.89/1.18  Ordering : KBO
% 1.89/1.18  
% 1.89/1.18  Simplification rules
% 1.89/1.18  ----------------------
% 1.89/1.18  #Subsume      : 3
% 1.89/1.18  #Demod        : 1
% 1.89/1.18  #Tautology    : 5
% 1.89/1.18  #SimpNegUnit  : 2
% 1.89/1.18  #BackRed      : 0
% 1.89/1.18  
% 1.89/1.18  #Partial instantiations: 0
% 1.89/1.18  #Strategies tried      : 1
% 1.89/1.18  
% 1.89/1.18  Timing (in seconds)
% 1.89/1.18  ----------------------
% 1.89/1.18  Preprocessing        : 0.28
% 1.89/1.18  Parsing              : 0.15
% 1.89/1.18  CNF conversion       : 0.02
% 1.89/1.18  Main loop            : 0.14
% 1.89/1.18  Inferencing          : 0.06
% 1.89/1.18  Reduction            : 0.04
% 1.89/1.18  Demodulation         : 0.02
% 1.89/1.18  BG Simplification    : 0.01
% 1.89/1.18  Subsumption          : 0.03
% 1.89/1.18  Abstraction          : 0.01
% 1.89/1.18  MUC search           : 0.00
% 1.89/1.18  Cooper               : 0.00
% 1.89/1.18  Total                : 0.44
% 1.89/1.18  Index Insertion      : 0.00
% 1.89/1.18  Index Deletion       : 0.00
% 1.89/1.18  Index Matching       : 0.00
% 1.89/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
