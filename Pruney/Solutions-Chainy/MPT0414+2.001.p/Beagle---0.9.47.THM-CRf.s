%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:42 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   40 (  53 expanded)
%              Number of leaves         :   17 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   53 ( 100 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k3_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_59,negated_conjecture,(
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

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_14,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_83,plain,(
    ! [A_32,C_33,B_34] :
      ( m1_subset_1(A_32,C_33)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(C_33))
      | ~ r2_hidden(A_32,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_90,plain,(
    ! [A_35] :
      ( m1_subset_1(A_35,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_35,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_83])).

tff(c_20,plain,(
    ! [D_17] :
      ( r2_hidden(D_17,'#skF_3')
      | ~ r2_hidden(D_17,'#skF_4')
      | ~ m1_subset_1(D_17,k1_zfmisc_1('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_98,plain,(
    ! [A_36] :
      ( r2_hidden(A_36,'#skF_3')
      | ~ r2_hidden(A_36,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_90,c_20])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_130,plain,(
    ! [A_40] :
      ( r1_tarski(A_40,'#skF_3')
      | ~ r2_hidden('#skF_1'(A_40,'#skF_3'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_98,c_6])).

tff(c_135,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_130])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_139,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_135,c_10])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_89,plain,(
    ! [A_32] :
      ( m1_subset_1(A_32,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_32,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_18,c_83])).

tff(c_111,plain,(
    ! [D_38] :
      ( r2_hidden(D_38,'#skF_4')
      | ~ r2_hidden(D_38,'#skF_3')
      | ~ m1_subset_1(D_38,k1_zfmisc_1('#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_120,plain,(
    ! [A_39] :
      ( r2_hidden(A_39,'#skF_4')
      | ~ r2_hidden(A_39,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_89,c_111])).

tff(c_140,plain,(
    ! [B_41] :
      ( r2_hidden('#skF_1'('#skF_3',B_41),'#skF_4')
      | r1_tarski('#skF_3',B_41) ) ),
    inference(resolution,[status(thm)],[c_8,c_120])).

tff(c_154,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_140,c_6])).

tff(c_158,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_154,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_166,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_2])).

tff(c_178,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_166])).

tff(c_180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_178])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:20:09 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.15  
% 1.68/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.16  %$ r2_hidden > r1_tarski > m1_subset_1 > k3_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.68/1.16  
% 1.68/1.16  %Foreground sorts:
% 1.68/1.16  
% 1.68/1.16  
% 1.68/1.16  %Background operators:
% 1.68/1.16  
% 1.68/1.16  
% 1.68/1.16  %Foreground operators:
% 1.68/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.68/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.68/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.68/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.68/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.68/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.68/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.68/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.68/1.16  
% 1.68/1.17  tff(f_59, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, B) <=> r2_hidden(D, C)))) => (B = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_setfam_1)).
% 1.68/1.17  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.68/1.17  tff(f_44, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 1.68/1.17  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.68/1.17  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.68/1.17  tff(c_14, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.68/1.17  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.68/1.17  tff(c_16, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.68/1.17  tff(c_83, plain, (![A_32, C_33, B_34]: (m1_subset_1(A_32, C_33) | ~m1_subset_1(B_34, k1_zfmisc_1(C_33)) | ~r2_hidden(A_32, B_34))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.68/1.17  tff(c_90, plain, (![A_35]: (m1_subset_1(A_35, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_35, '#skF_4'))), inference(resolution, [status(thm)], [c_16, c_83])).
% 1.68/1.17  tff(c_20, plain, (![D_17]: (r2_hidden(D_17, '#skF_3') | ~r2_hidden(D_17, '#skF_4') | ~m1_subset_1(D_17, k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.68/1.17  tff(c_98, plain, (![A_36]: (r2_hidden(A_36, '#skF_3') | ~r2_hidden(A_36, '#skF_4'))), inference(resolution, [status(thm)], [c_90, c_20])).
% 1.68/1.17  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.68/1.17  tff(c_130, plain, (![A_40]: (r1_tarski(A_40, '#skF_3') | ~r2_hidden('#skF_1'(A_40, '#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_98, c_6])).
% 1.68/1.17  tff(c_135, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_8, c_130])).
% 1.68/1.17  tff(c_10, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.68/1.17  tff(c_139, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_135, c_10])).
% 1.68/1.17  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.68/1.17  tff(c_89, plain, (![A_32]: (m1_subset_1(A_32, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_32, '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_83])).
% 1.68/1.17  tff(c_111, plain, (![D_38]: (r2_hidden(D_38, '#skF_4') | ~r2_hidden(D_38, '#skF_3') | ~m1_subset_1(D_38, k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.68/1.17  tff(c_120, plain, (![A_39]: (r2_hidden(A_39, '#skF_4') | ~r2_hidden(A_39, '#skF_3'))), inference(resolution, [status(thm)], [c_89, c_111])).
% 1.68/1.17  tff(c_140, plain, (![B_41]: (r2_hidden('#skF_1'('#skF_3', B_41), '#skF_4') | r1_tarski('#skF_3', B_41))), inference(resolution, [status(thm)], [c_8, c_120])).
% 1.68/1.17  tff(c_154, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_140, c_6])).
% 1.68/1.17  tff(c_158, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_154, c_10])).
% 1.68/1.17  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.68/1.17  tff(c_166, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_158, c_2])).
% 1.68/1.17  tff(c_178, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_139, c_166])).
% 1.68/1.17  tff(c_180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_178])).
% 1.68/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.17  
% 1.68/1.17  Inference rules
% 1.68/1.17  ----------------------
% 1.68/1.17  #Ref     : 0
% 1.68/1.17  #Sup     : 38
% 1.68/1.17  #Fact    : 0
% 1.68/1.17  #Define  : 0
% 1.68/1.17  #Split   : 0
% 1.68/1.17  #Chain   : 0
% 1.68/1.17  #Close   : 0
% 1.68/1.17  
% 1.68/1.17  Ordering : KBO
% 1.68/1.17  
% 1.68/1.17  Simplification rules
% 1.68/1.17  ----------------------
% 1.68/1.17  #Subsume      : 2
% 1.68/1.17  #Demod        : 2
% 1.68/1.17  #Tautology    : 16
% 1.68/1.17  #SimpNegUnit  : 1
% 1.68/1.17  #BackRed      : 0
% 1.68/1.17  
% 1.68/1.17  #Partial instantiations: 0
% 1.68/1.17  #Strategies tried      : 1
% 1.68/1.17  
% 1.68/1.17  Timing (in seconds)
% 1.68/1.17  ----------------------
% 1.68/1.17  Preprocessing        : 0.27
% 1.68/1.17  Parsing              : 0.14
% 1.68/1.17  CNF conversion       : 0.02
% 1.68/1.17  Main loop            : 0.15
% 1.68/1.17  Inferencing          : 0.06
% 1.68/1.17  Reduction            : 0.04
% 1.68/1.17  Demodulation         : 0.03
% 1.68/1.17  BG Simplification    : 0.01
% 1.68/1.17  Subsumption          : 0.03
% 1.68/1.17  Abstraction          : 0.01
% 1.68/1.17  MUC search           : 0.00
% 1.68/1.17  Cooper               : 0.00
% 1.68/1.17  Total                : 0.45
% 1.68/1.17  Index Insertion      : 0.00
% 1.68/1.17  Index Deletion       : 0.00
% 1.68/1.17  Index Matching       : 0.00
% 1.68/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
