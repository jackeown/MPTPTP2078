%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:53 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   31 (  35 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   44 (  64 expanded)
%              Number of equality atoms :    7 (  11 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
       => ~ ( r2_hidden(A,D)
            & ! [E,F] :
                ~ ( A = k4_tarski(E,F)
                  & r2_hidden(E,B)
                  & r2_hidden(F,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B,C,D] :
      ~ ( r1_tarski(A,k2_zfmisc_1(B,C))
        & r2_hidden(D,A)
        & ! [E,F] :
            ~ ( r2_hidden(E,B)
              & r2_hidden(F,C)
              & D = k4_tarski(E,F) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).

tff(c_16,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_26,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_16,c_18])).

tff(c_14,plain,(
    r2_hidden('#skF_3','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3,D_4),B_2)
      | ~ r2_hidden(D_4,A_1)
      | ~ r1_tarski(A_1,k2_zfmisc_1(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_40,plain,(
    ! [A_35,B_36,C_37,D_38] :
      ( k4_tarski('#skF_1'(A_35,B_36,C_37,D_38),'#skF_2'(A_35,B_36,C_37,D_38)) = D_38
      | ~ r2_hidden(D_38,A_35)
      | ~ r1_tarski(A_35,k2_zfmisc_1(B_36,C_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_28,plain,(
    ! [A_19,B_20,C_21,D_22] :
      ( r2_hidden('#skF_2'(A_19,B_20,C_21,D_22),C_21)
      | ~ r2_hidden(D_22,A_19)
      | ~ r1_tarski(A_19,k2_zfmisc_1(B_20,C_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12,plain,(
    ! [F_12,E_11] :
      ( ~ r2_hidden(F_12,'#skF_5')
      | ~ r2_hidden(E_11,'#skF_4')
      | k4_tarski(E_11,F_12) != '#skF_3' ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_32,plain,(
    ! [E_11,A_19,B_20,D_22] :
      ( ~ r2_hidden(E_11,'#skF_4')
      | k4_tarski(E_11,'#skF_2'(A_19,B_20,'#skF_5',D_22)) != '#skF_3'
      | ~ r2_hidden(D_22,A_19)
      | ~ r1_tarski(A_19,k2_zfmisc_1(B_20,'#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_28,c_12])).

tff(c_53,plain,(
    ! [A_39,B_40,D_41] :
      ( ~ r2_hidden('#skF_1'(A_39,B_40,'#skF_5',D_41),'#skF_4')
      | D_41 != '#skF_3'
      | ~ r2_hidden(D_41,A_39)
      | ~ r1_tarski(A_39,k2_zfmisc_1(B_40,'#skF_5'))
      | ~ r2_hidden(D_41,A_39)
      | ~ r1_tarski(A_39,k2_zfmisc_1(B_40,'#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_32])).

tff(c_60,plain,(
    ! [D_42,A_43] :
      ( D_42 != '#skF_3'
      | ~ r2_hidden(D_42,A_43)
      | ~ r1_tarski(A_43,k2_zfmisc_1('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_6,c_53])).

tff(c_66,plain,(
    ~ r1_tarski('#skF_6',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_14,c_60])).

tff(c_72,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_66])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:36:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.12  
% 1.59/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.13  %$ r2_hidden > r1_tarski > m1_subset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 1.59/1.13  
% 1.59/1.13  %Foreground sorts:
% 1.59/1.13  
% 1.59/1.13  
% 1.59/1.13  %Background operators:
% 1.59/1.13  
% 1.59/1.13  
% 1.59/1.13  %Foreground operators:
% 1.59/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.59/1.13  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.59/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.59/1.13  tff('#skF_5', type, '#skF_5': $i).
% 1.59/1.13  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 1.59/1.13  tff('#skF_6', type, '#skF_6': $i).
% 1.59/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.59/1.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.59/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.59/1.13  tff('#skF_4', type, '#skF_4': $i).
% 1.59/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.13  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 1.59/1.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.59/1.13  
% 1.59/1.14  tff(f_56, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => ~(r2_hidden(A, D) & (![E, F]: ~(((A = k4_tarski(E, F)) & r2_hidden(E, B)) & r2_hidden(F, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_relset_1)).
% 1.59/1.14  tff(f_42, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.59/1.14  tff(f_38, axiom, (![A, B, C, D]: ~((r1_tarski(A, k2_zfmisc_1(B, C)) & r2_hidden(D, A)) & (![E, F]: ~((r2_hidden(E, B) & r2_hidden(F, C)) & (D = k4_tarski(E, F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_zfmisc_1)).
% 1.59/1.14  tff(c_16, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.59/1.14  tff(c_18, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.59/1.14  tff(c_26, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_16, c_18])).
% 1.59/1.14  tff(c_14, plain, (r2_hidden('#skF_3', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.59/1.14  tff(c_6, plain, (![A_1, B_2, C_3, D_4]: (r2_hidden('#skF_1'(A_1, B_2, C_3, D_4), B_2) | ~r2_hidden(D_4, A_1) | ~r1_tarski(A_1, k2_zfmisc_1(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.59/1.14  tff(c_40, plain, (![A_35, B_36, C_37, D_38]: (k4_tarski('#skF_1'(A_35, B_36, C_37, D_38), '#skF_2'(A_35, B_36, C_37, D_38))=D_38 | ~r2_hidden(D_38, A_35) | ~r1_tarski(A_35, k2_zfmisc_1(B_36, C_37)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.59/1.14  tff(c_28, plain, (![A_19, B_20, C_21, D_22]: (r2_hidden('#skF_2'(A_19, B_20, C_21, D_22), C_21) | ~r2_hidden(D_22, A_19) | ~r1_tarski(A_19, k2_zfmisc_1(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.59/1.14  tff(c_12, plain, (![F_12, E_11]: (~r2_hidden(F_12, '#skF_5') | ~r2_hidden(E_11, '#skF_4') | k4_tarski(E_11, F_12)!='#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.59/1.14  tff(c_32, plain, (![E_11, A_19, B_20, D_22]: (~r2_hidden(E_11, '#skF_4') | k4_tarski(E_11, '#skF_2'(A_19, B_20, '#skF_5', D_22))!='#skF_3' | ~r2_hidden(D_22, A_19) | ~r1_tarski(A_19, k2_zfmisc_1(B_20, '#skF_5')))), inference(resolution, [status(thm)], [c_28, c_12])).
% 1.59/1.14  tff(c_53, plain, (![A_39, B_40, D_41]: (~r2_hidden('#skF_1'(A_39, B_40, '#skF_5', D_41), '#skF_4') | D_41!='#skF_3' | ~r2_hidden(D_41, A_39) | ~r1_tarski(A_39, k2_zfmisc_1(B_40, '#skF_5')) | ~r2_hidden(D_41, A_39) | ~r1_tarski(A_39, k2_zfmisc_1(B_40, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_40, c_32])).
% 1.59/1.14  tff(c_60, plain, (![D_42, A_43]: (D_42!='#skF_3' | ~r2_hidden(D_42, A_43) | ~r1_tarski(A_43, k2_zfmisc_1('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_6, c_53])).
% 1.59/1.14  tff(c_66, plain, (~r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_14, c_60])).
% 1.59/1.14  tff(c_72, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_66])).
% 1.59/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.14  
% 1.59/1.14  Inference rules
% 1.59/1.14  ----------------------
% 1.59/1.14  #Ref     : 0
% 1.59/1.14  #Sup     : 11
% 1.59/1.14  #Fact    : 0
% 1.59/1.14  #Define  : 0
% 1.59/1.14  #Split   : 0
% 1.59/1.14  #Chain   : 0
% 1.59/1.14  #Close   : 0
% 1.59/1.14  
% 1.59/1.14  Ordering : KBO
% 1.59/1.14  
% 1.59/1.14  Simplification rules
% 1.59/1.14  ----------------------
% 1.59/1.14  #Subsume      : 0
% 1.59/1.14  #Demod        : 1
% 1.59/1.14  #Tautology    : 3
% 1.59/1.14  #SimpNegUnit  : 0
% 1.59/1.14  #BackRed      : 0
% 1.59/1.14  
% 1.59/1.14  #Partial instantiations: 0
% 1.59/1.14  #Strategies tried      : 1
% 1.59/1.14  
% 1.59/1.14  Timing (in seconds)
% 1.59/1.14  ----------------------
% 1.59/1.14  Preprocessing        : 0.25
% 1.59/1.14  Parsing              : 0.14
% 1.59/1.14  CNF conversion       : 0.02
% 1.59/1.14  Main loop            : 0.12
% 1.59/1.14  Inferencing          : 0.06
% 1.59/1.14  Reduction            : 0.03
% 1.59/1.14  Demodulation         : 0.02
% 1.59/1.14  BG Simplification    : 0.01
% 1.59/1.14  Subsumption          : 0.02
% 1.59/1.14  Abstraction          : 0.01
% 1.59/1.14  MUC search           : 0.00
% 1.59/1.14  Cooper               : 0.00
% 1.59/1.14  Total                : 0.39
% 1.59/1.14  Index Insertion      : 0.00
% 1.59/1.14  Index Deletion       : 0.00
% 1.59/1.14  Index Matching       : 0.00
% 1.59/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
