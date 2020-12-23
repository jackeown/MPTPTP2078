%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:51 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   37 (  47 expanded)
%              Number of leaves         :   17 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :   63 (  95 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k7_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(k7_setfam_1(A,B),k7_setfam_1(A,C))
             => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r2_hidden(k3_subset_1(A,C),k7_setfam_1(A,B))
          <=> r2_hidden(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_setfam_1)).

tff(c_14,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_33,plain,(
    ! [A_22,C_23,B_24] :
      ( m1_subset_1(A_22,C_23)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(C_23))
      | ~ r2_hidden(A_22,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_39,plain,(
    ! [A_22] :
      ( m1_subset_1(A_22,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_22,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_33])).

tff(c_18,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    r1_tarski(k7_setfam_1('#skF_2','#skF_3'),k7_setfam_1('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_72,plain,(
    ! [A_36,C_37,B_38] :
      ( r2_hidden(k3_subset_1(A_36,C_37),k7_setfam_1(A_36,B_38))
      | ~ r2_hidden(C_37,B_38)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(A_36))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(k1_zfmisc_1(A_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_183,plain,(
    ! [A_79,C_80,B_81,B_82] :
      ( r2_hidden(k3_subset_1(A_79,C_80),B_81)
      | ~ r1_tarski(k7_setfam_1(A_79,B_82),B_81)
      | ~ r2_hidden(C_80,B_82)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(A_79))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k1_zfmisc_1(A_79))) ) ),
    inference(resolution,[status(thm)],[c_72,c_2])).

tff(c_188,plain,(
    ! [C_80] :
      ( r2_hidden(k3_subset_1('#skF_2',C_80),k7_setfam_1('#skF_2','#skF_4'))
      | ~ r2_hidden(C_80,'#skF_3')
      | ~ m1_subset_1(C_80,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_16,c_183])).

tff(c_193,plain,(
    ! [C_83] :
      ( r2_hidden(k3_subset_1('#skF_2',C_83),k7_setfam_1('#skF_2','#skF_4'))
      | ~ r2_hidden(C_83,'#skF_3')
      | ~ m1_subset_1(C_83,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_188])).

tff(c_10,plain,(
    ! [C_9,B_7,A_6] :
      ( r2_hidden(C_9,B_7)
      | ~ r2_hidden(k3_subset_1(A_6,C_9),k7_setfam_1(A_6,B_7))
      | ~ m1_subset_1(C_9,k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k1_zfmisc_1(A_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_196,plain,(
    ! [C_83] :
      ( r2_hidden(C_83,'#skF_4')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ r2_hidden(C_83,'#skF_3')
      | ~ m1_subset_1(C_83,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_193,c_10])).

tff(c_209,plain,(
    ! [C_84] :
      ( r2_hidden(C_84,'#skF_4')
      | ~ r2_hidden(C_84,'#skF_3')
      | ~ m1_subset_1(C_84,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_196])).

tff(c_218,plain,(
    ! [A_85] :
      ( r2_hidden(A_85,'#skF_4')
      | ~ r2_hidden(A_85,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_39,c_209])).

tff(c_234,plain,(
    ! [B_86] :
      ( r2_hidden('#skF_1'('#skF_3',B_86),'#skF_4')
      | r1_tarski('#skF_3',B_86) ) ),
    inference(resolution,[status(thm)],[c_6,c_218])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_246,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_234,c_4])).

tff(c_254,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_14,c_246])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:04:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.25  
% 2.20/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.25  %$ r2_hidden > r1_tarski > m1_subset_1 > k7_setfam_1 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.20/1.25  
% 2.20/1.25  %Foreground sorts:
% 2.20/1.25  
% 2.20/1.25  
% 2.20/1.25  %Background operators:
% 2.20/1.25  
% 2.20/1.25  
% 2.20/1.25  %Foreground operators:
% 2.20/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.25  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.20/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.25  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.20/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.20/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.20/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.20/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.20/1.25  
% 2.20/1.26  tff(f_57, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(k7_setfam_1(A, B), k7_setfam_1(A, C)) => r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_setfam_1)).
% 2.20/1.26  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.20/1.26  tff(f_47, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.20/1.26  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r2_hidden(k3_subset_1(A, C), k7_setfam_1(A, B)) <=> r2_hidden(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_setfam_1)).
% 2.20/1.26  tff(c_14, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.20/1.26  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.20/1.26  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.20/1.26  tff(c_33, plain, (![A_22, C_23, B_24]: (m1_subset_1(A_22, C_23) | ~m1_subset_1(B_24, k1_zfmisc_1(C_23)) | ~r2_hidden(A_22, B_24))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.20/1.26  tff(c_39, plain, (![A_22]: (m1_subset_1(A_22, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_22, '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_33])).
% 2.20/1.26  tff(c_18, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.20/1.26  tff(c_16, plain, (r1_tarski(k7_setfam_1('#skF_2', '#skF_3'), k7_setfam_1('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.20/1.26  tff(c_72, plain, (![A_36, C_37, B_38]: (r2_hidden(k3_subset_1(A_36, C_37), k7_setfam_1(A_36, B_38)) | ~r2_hidden(C_37, B_38) | ~m1_subset_1(C_37, k1_zfmisc_1(A_36)) | ~m1_subset_1(B_38, k1_zfmisc_1(k1_zfmisc_1(A_36))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.20/1.26  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.20/1.26  tff(c_183, plain, (![A_79, C_80, B_81, B_82]: (r2_hidden(k3_subset_1(A_79, C_80), B_81) | ~r1_tarski(k7_setfam_1(A_79, B_82), B_81) | ~r2_hidden(C_80, B_82) | ~m1_subset_1(C_80, k1_zfmisc_1(A_79)) | ~m1_subset_1(B_82, k1_zfmisc_1(k1_zfmisc_1(A_79))))), inference(resolution, [status(thm)], [c_72, c_2])).
% 2.20/1.26  tff(c_188, plain, (![C_80]: (r2_hidden(k3_subset_1('#skF_2', C_80), k7_setfam_1('#skF_2', '#skF_4')) | ~r2_hidden(C_80, '#skF_3') | ~m1_subset_1(C_80, k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(resolution, [status(thm)], [c_16, c_183])).
% 2.20/1.26  tff(c_193, plain, (![C_83]: (r2_hidden(k3_subset_1('#skF_2', C_83), k7_setfam_1('#skF_2', '#skF_4')) | ~r2_hidden(C_83, '#skF_3') | ~m1_subset_1(C_83, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_188])).
% 2.20/1.26  tff(c_10, plain, (![C_9, B_7, A_6]: (r2_hidden(C_9, B_7) | ~r2_hidden(k3_subset_1(A_6, C_9), k7_setfam_1(A_6, B_7)) | ~m1_subset_1(C_9, k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(k1_zfmisc_1(A_6))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.20/1.26  tff(c_196, plain, (![C_83]: (r2_hidden(C_83, '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~r2_hidden(C_83, '#skF_3') | ~m1_subset_1(C_83, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_193, c_10])).
% 2.20/1.26  tff(c_209, plain, (![C_84]: (r2_hidden(C_84, '#skF_4') | ~r2_hidden(C_84, '#skF_3') | ~m1_subset_1(C_84, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_196])).
% 2.20/1.26  tff(c_218, plain, (![A_85]: (r2_hidden(A_85, '#skF_4') | ~r2_hidden(A_85, '#skF_3'))), inference(resolution, [status(thm)], [c_39, c_209])).
% 2.20/1.26  tff(c_234, plain, (![B_86]: (r2_hidden('#skF_1'('#skF_3', B_86), '#skF_4') | r1_tarski('#skF_3', B_86))), inference(resolution, [status(thm)], [c_6, c_218])).
% 2.20/1.26  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.20/1.26  tff(c_246, plain, (r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_234, c_4])).
% 2.20/1.26  tff(c_254, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_14, c_246])).
% 2.20/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.26  
% 2.20/1.26  Inference rules
% 2.20/1.26  ----------------------
% 2.20/1.26  #Ref     : 0
% 2.20/1.26  #Sup     : 53
% 2.20/1.26  #Fact    : 0
% 2.20/1.26  #Define  : 0
% 2.20/1.26  #Split   : 2
% 2.20/1.26  #Chain   : 0
% 2.20/1.26  #Close   : 0
% 2.20/1.26  
% 2.20/1.26  Ordering : KBO
% 2.20/1.26  
% 2.20/1.26  Simplification rules
% 2.20/1.26  ----------------------
% 2.20/1.26  #Subsume      : 7
% 2.20/1.26  #Demod        : 3
% 2.20/1.26  #Tautology    : 4
% 2.20/1.26  #SimpNegUnit  : 1
% 2.20/1.26  #BackRed      : 0
% 2.20/1.26  
% 2.20/1.26  #Partial instantiations: 0
% 2.20/1.26  #Strategies tried      : 1
% 2.20/1.26  
% 2.20/1.26  Timing (in seconds)
% 2.20/1.26  ----------------------
% 2.20/1.27  Preprocessing        : 0.26
% 2.20/1.27  Parsing              : 0.14
% 2.20/1.27  CNF conversion       : 0.02
% 2.20/1.27  Main loop            : 0.24
% 2.20/1.27  Inferencing          : 0.10
% 2.20/1.27  Reduction            : 0.06
% 2.20/1.27  Demodulation         : 0.04
% 2.20/1.27  BG Simplification    : 0.01
% 2.20/1.27  Subsumption          : 0.06
% 2.20/1.27  Abstraction          : 0.01
% 2.20/1.27  MUC search           : 0.00
% 2.20/1.27  Cooper               : 0.00
% 2.20/1.27  Total                : 0.53
% 2.20/1.27  Index Insertion      : 0.00
% 2.20/1.27  Index Deletion       : 0.00
% 2.20/1.27  Index Matching       : 0.00
% 2.20/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
