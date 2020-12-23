%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:22:29 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   34 (  37 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   42 (  52 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > l1_struct_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_57,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
           => ! [C] :
                ( r1_tarski(C,B)
               => m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_tops_2)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_35,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(A_21,B_22)
      | ~ m1_subset_1(A_21,k1_zfmisc_1(B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_39,plain,(
    r1_tarski('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_26,c_35])).

tff(c_24,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(k1_zfmisc_1(A_6),k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_4,plain,(
    ! [C_5,A_1] :
      ( r2_hidden(C_5,k1_zfmisc_1(A_1))
      | ~ r1_tarski(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(A_8,k1_zfmisc_1(B_9))
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_50,plain,(
    ! [A_27,C_28,B_29] :
      ( m1_subset_1(A_27,C_28)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(C_28))
      | ~ r2_hidden(A_27,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_66,plain,(
    ! [A_32,B_33,A_34] :
      ( m1_subset_1(A_32,B_33)
      | ~ r2_hidden(A_32,A_34)
      | ~ r1_tarski(A_34,B_33) ) ),
    inference(resolution,[status(thm)],[c_18,c_50])).

tff(c_86,plain,(
    ! [C_39,B_40,A_41] :
      ( m1_subset_1(C_39,B_40)
      | ~ r1_tarski(k1_zfmisc_1(A_41),B_40)
      | ~ r1_tarski(C_39,A_41) ) ),
    inference(resolution,[status(thm)],[c_4,c_66])).

tff(c_94,plain,(
    ! [C_42,B_43,A_44] :
      ( m1_subset_1(C_42,k1_zfmisc_1(B_43))
      | ~ r1_tarski(C_42,A_44)
      | ~ r1_tarski(A_44,B_43) ) ),
    inference(resolution,[status(thm)],[c_14,c_86])).

tff(c_107,plain,(
    ! [B_45] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1(B_45))
      | ~ r1_tarski('#skF_4',B_45) ) ),
    inference(resolution,[status(thm)],[c_24,c_94])).

tff(c_22,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_115,plain,(
    ~ r1_tarski('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_107,c_22])).

tff(c_121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_115])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:39:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.23  
% 1.88/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.23  %$ r2_hidden > r1_tarski > m1_subset_1 > l1_struct_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.88/1.23  
% 1.88/1.23  %Foreground sorts:
% 1.88/1.23  
% 1.88/1.23  
% 1.88/1.23  %Background operators:
% 1.88/1.23  
% 1.88/1.23  
% 1.88/1.23  %Foreground operators:
% 1.88/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.88/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.23  tff('#skF_5', type, '#skF_5': $i).
% 1.88/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.88/1.23  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.88/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.23  tff('#skF_4', type, '#skF_4': $i).
% 1.88/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.88/1.23  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.88/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.88/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.88/1.23  
% 1.88/1.24  tff(f_57, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => (![C]: (r1_tarski(C, B) => m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_tops_2)).
% 1.88/1.24  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.88/1.24  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 1.88/1.24  tff(f_32, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.88/1.24  tff(f_46, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 1.88/1.24  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.88/1.24  tff(c_35, plain, (![A_21, B_22]: (r1_tarski(A_21, B_22) | ~m1_subset_1(A_21, k1_zfmisc_1(B_22)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.88/1.24  tff(c_39, plain, (r1_tarski('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_26, c_35])).
% 1.88/1.24  tff(c_24, plain, (r1_tarski('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.88/1.24  tff(c_14, plain, (![A_6, B_7]: (r1_tarski(k1_zfmisc_1(A_6), k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.88/1.24  tff(c_4, plain, (![C_5, A_1]: (r2_hidden(C_5, k1_zfmisc_1(A_1)) | ~r1_tarski(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.88/1.24  tff(c_18, plain, (![A_8, B_9]: (m1_subset_1(A_8, k1_zfmisc_1(B_9)) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.88/1.24  tff(c_50, plain, (![A_27, C_28, B_29]: (m1_subset_1(A_27, C_28) | ~m1_subset_1(B_29, k1_zfmisc_1(C_28)) | ~r2_hidden(A_27, B_29))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.88/1.24  tff(c_66, plain, (![A_32, B_33, A_34]: (m1_subset_1(A_32, B_33) | ~r2_hidden(A_32, A_34) | ~r1_tarski(A_34, B_33))), inference(resolution, [status(thm)], [c_18, c_50])).
% 1.88/1.24  tff(c_86, plain, (![C_39, B_40, A_41]: (m1_subset_1(C_39, B_40) | ~r1_tarski(k1_zfmisc_1(A_41), B_40) | ~r1_tarski(C_39, A_41))), inference(resolution, [status(thm)], [c_4, c_66])).
% 1.88/1.24  tff(c_94, plain, (![C_42, B_43, A_44]: (m1_subset_1(C_42, k1_zfmisc_1(B_43)) | ~r1_tarski(C_42, A_44) | ~r1_tarski(A_44, B_43))), inference(resolution, [status(thm)], [c_14, c_86])).
% 1.88/1.24  tff(c_107, plain, (![B_45]: (m1_subset_1('#skF_5', k1_zfmisc_1(B_45)) | ~r1_tarski('#skF_4', B_45))), inference(resolution, [status(thm)], [c_24, c_94])).
% 1.88/1.24  tff(c_22, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.88/1.24  tff(c_115, plain, (~r1_tarski('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_107, c_22])).
% 1.88/1.24  tff(c_121, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39, c_115])).
% 1.88/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.24  
% 1.88/1.24  Inference rules
% 1.88/1.24  ----------------------
% 1.88/1.24  #Ref     : 0
% 1.88/1.24  #Sup     : 22
% 1.88/1.24  #Fact    : 0
% 1.88/1.24  #Define  : 0
% 1.88/1.24  #Split   : 0
% 1.88/1.24  #Chain   : 0
% 1.88/1.24  #Close   : 0
% 1.88/1.24  
% 1.88/1.24  Ordering : KBO
% 1.88/1.24  
% 1.88/1.24  Simplification rules
% 1.88/1.24  ----------------------
% 1.88/1.24  #Subsume      : 0
% 1.88/1.24  #Demod        : 1
% 1.88/1.24  #Tautology    : 2
% 1.88/1.24  #SimpNegUnit  : 0
% 1.88/1.24  #BackRed      : 0
% 1.88/1.24  
% 1.88/1.24  #Partial instantiations: 0
% 1.88/1.24  #Strategies tried      : 1
% 1.88/1.24  
% 1.88/1.24  Timing (in seconds)
% 1.88/1.24  ----------------------
% 1.88/1.25  Preprocessing        : 0.29
% 1.88/1.25  Parsing              : 0.16
% 1.88/1.25  CNF conversion       : 0.02
% 1.88/1.25  Main loop            : 0.14
% 1.88/1.25  Inferencing          : 0.06
% 1.88/1.25  Reduction            : 0.04
% 1.88/1.25  Demodulation         : 0.03
% 1.88/1.25  BG Simplification    : 0.01
% 1.88/1.25  Subsumption          : 0.03
% 1.88/1.25  Abstraction          : 0.01
% 1.88/1.25  MUC search           : 0.00
% 1.88/1.25  Cooper               : 0.00
% 1.88/1.25  Total                : 0.46
% 1.88/1.25  Index Insertion      : 0.00
% 1.88/1.25  Index Deletion       : 0.00
% 1.88/1.25  Index Matching       : 0.00
% 1.88/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
