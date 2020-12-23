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
% DateTime   : Thu Dec  3 10:06:53 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   36 (  58 expanded)
%              Number of leaves         :   18 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   49 ( 110 expanded)
%              Number of equality atoms :    6 (  15 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
       => ~ ( r2_hidden(A,D)
            & ! [E,F] :
                ~ ( A = k4_tarski(E,F)
                  & r2_hidden(E,B)
                  & r2_hidden(F,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,k2_zfmisc_1(B,C))
        & ! [D,E] : k4_tarski(D,E) != A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l139_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_16,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_14,plain,(
    r2_hidden('#skF_3','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_17,plain,(
    ! [C_18,A_19,B_20] :
      ( r2_hidden(C_18,A_19)
      | ~ r2_hidden(C_18,B_20)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_21,plain,(
    ! [A_21] :
      ( r2_hidden('#skF_3',A_21)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_21)) ) ),
    inference(resolution,[status(thm)],[c_14,c_17])).

tff(c_25,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_16,c_21])).

tff(c_45,plain,(
    ! [A_37,B_38,C_39] :
      ( k4_tarski('#skF_1'(A_37,B_38,C_39),'#skF_2'(A_37,B_38,C_39)) = A_37
      | ~ r2_hidden(A_37,k2_zfmisc_1(B_38,C_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7,D_9] :
      ( r2_hidden(A_6,C_8)
      | ~ r2_hidden(k4_tarski(A_6,B_7),k2_zfmisc_1(C_8,D_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_83,plain,(
    ! [C_56,B_53,A_52,D_54,C_55] :
      ( r2_hidden('#skF_1'(A_52,B_53,C_56),C_55)
      | ~ r2_hidden(A_52,k2_zfmisc_1(C_55,D_54))
      | ~ r2_hidden(A_52,k2_zfmisc_1(B_53,C_56)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_8])).

tff(c_90,plain,(
    ! [B_57,C_58] :
      ( r2_hidden('#skF_1'('#skF_3',B_57,C_58),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_zfmisc_1(B_57,C_58)) ) ),
    inference(resolution,[status(thm)],[c_25,c_83])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( k4_tarski('#skF_1'(A_1,B_2,C_3),'#skF_2'(A_1,B_2,C_3)) = A_1
      | ~ r2_hidden(A_1,k2_zfmisc_1(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6,plain,(
    ! [B_7,D_9,A_6,C_8] :
      ( r2_hidden(B_7,D_9)
      | ~ r2_hidden(k4_tarski(A_6,B_7),k2_zfmisc_1(C_8,D_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_63,plain,(
    ! [C_43,D_42,C_44,A_40,B_41] :
      ( r2_hidden('#skF_2'(A_40,B_41,C_44),D_42)
      | ~ r2_hidden(A_40,k2_zfmisc_1(C_43,D_42))
      | ~ r2_hidden(A_40,k2_zfmisc_1(B_41,C_44)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_6])).

tff(c_70,plain,(
    ! [B_45,C_46] :
      ( r2_hidden('#skF_2'('#skF_3',B_45,C_46),'#skF_5')
      | ~ r2_hidden('#skF_3',k2_zfmisc_1(B_45,C_46)) ) ),
    inference(resolution,[status(thm)],[c_25,c_63])).

tff(c_12,plain,(
    ! [F_17,E_16] :
      ( ~ r2_hidden(F_17,'#skF_5')
      | ~ r2_hidden(E_16,'#skF_4')
      | k4_tarski(E_16,F_17) != '#skF_3' ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_77,plain,(
    ! [E_47,B_48,C_49] :
      ( ~ r2_hidden(E_47,'#skF_4')
      | k4_tarski(E_47,'#skF_2'('#skF_3',B_48,C_49)) != '#skF_3'
      | ~ r2_hidden('#skF_3',k2_zfmisc_1(B_48,C_49)) ) ),
    inference(resolution,[status(thm)],[c_70,c_12])).

tff(c_81,plain,(
    ! [B_2,C_3] :
      ( ~ r2_hidden('#skF_1'('#skF_3',B_2,C_3),'#skF_4')
      | ~ r2_hidden('#skF_3',k2_zfmisc_1(B_2,C_3)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_77])).

tff(c_96,plain,(
    ! [B_57,C_58] : ~ r2_hidden('#skF_3',k2_zfmisc_1(B_57,C_58)) ),
    inference(resolution,[status(thm)],[c_90,c_81])).

tff(c_99,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_25])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 20:14:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.13  
% 1.65/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.14  %$ r2_hidden > m1_subset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 1.65/1.14  
% 1.65/1.14  %Foreground sorts:
% 1.65/1.14  
% 1.65/1.14  
% 1.65/1.14  %Background operators:
% 1.65/1.14  
% 1.65/1.14  
% 1.65/1.14  %Foreground operators:
% 1.65/1.14  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.65/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.65/1.14  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.65/1.14  tff('#skF_5', type, '#skF_5': $i).
% 1.65/1.14  tff('#skF_6', type, '#skF_6': $i).
% 1.65/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.65/1.14  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.65/1.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.65/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.65/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.65/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.65/1.14  
% 1.65/1.15  tff(f_59, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => ~(r2_hidden(A, D) & (![E, F]: ~(((A = k4_tarski(E, F)) & r2_hidden(E, B)) & r2_hidden(F, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_relset_1)).
% 1.65/1.15  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 1.65/1.15  tff(f_32, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 1.65/1.15  tff(f_38, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 1.65/1.15  tff(c_16, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.65/1.15  tff(c_14, plain, (r2_hidden('#skF_3', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.65/1.15  tff(c_17, plain, (![C_18, A_19, B_20]: (r2_hidden(C_18, A_19) | ~r2_hidden(C_18, B_20) | ~m1_subset_1(B_20, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.65/1.15  tff(c_21, plain, (![A_21]: (r2_hidden('#skF_3', A_21) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_21)))), inference(resolution, [status(thm)], [c_14, c_17])).
% 1.65/1.15  tff(c_25, plain, (r2_hidden('#skF_3', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_16, c_21])).
% 1.65/1.15  tff(c_45, plain, (![A_37, B_38, C_39]: (k4_tarski('#skF_1'(A_37, B_38, C_39), '#skF_2'(A_37, B_38, C_39))=A_37 | ~r2_hidden(A_37, k2_zfmisc_1(B_38, C_39)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.65/1.15  tff(c_8, plain, (![A_6, C_8, B_7, D_9]: (r2_hidden(A_6, C_8) | ~r2_hidden(k4_tarski(A_6, B_7), k2_zfmisc_1(C_8, D_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.65/1.15  tff(c_83, plain, (![C_56, B_53, A_52, D_54, C_55]: (r2_hidden('#skF_1'(A_52, B_53, C_56), C_55) | ~r2_hidden(A_52, k2_zfmisc_1(C_55, D_54)) | ~r2_hidden(A_52, k2_zfmisc_1(B_53, C_56)))), inference(superposition, [status(thm), theory('equality')], [c_45, c_8])).
% 1.65/1.15  tff(c_90, plain, (![B_57, C_58]: (r2_hidden('#skF_1'('#skF_3', B_57, C_58), '#skF_4') | ~r2_hidden('#skF_3', k2_zfmisc_1(B_57, C_58)))), inference(resolution, [status(thm)], [c_25, c_83])).
% 1.65/1.15  tff(c_2, plain, (![A_1, B_2, C_3]: (k4_tarski('#skF_1'(A_1, B_2, C_3), '#skF_2'(A_1, B_2, C_3))=A_1 | ~r2_hidden(A_1, k2_zfmisc_1(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.65/1.15  tff(c_6, plain, (![B_7, D_9, A_6, C_8]: (r2_hidden(B_7, D_9) | ~r2_hidden(k4_tarski(A_6, B_7), k2_zfmisc_1(C_8, D_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.65/1.15  tff(c_63, plain, (![C_43, D_42, C_44, A_40, B_41]: (r2_hidden('#skF_2'(A_40, B_41, C_44), D_42) | ~r2_hidden(A_40, k2_zfmisc_1(C_43, D_42)) | ~r2_hidden(A_40, k2_zfmisc_1(B_41, C_44)))), inference(superposition, [status(thm), theory('equality')], [c_45, c_6])).
% 1.65/1.15  tff(c_70, plain, (![B_45, C_46]: (r2_hidden('#skF_2'('#skF_3', B_45, C_46), '#skF_5') | ~r2_hidden('#skF_3', k2_zfmisc_1(B_45, C_46)))), inference(resolution, [status(thm)], [c_25, c_63])).
% 1.65/1.15  tff(c_12, plain, (![F_17, E_16]: (~r2_hidden(F_17, '#skF_5') | ~r2_hidden(E_16, '#skF_4') | k4_tarski(E_16, F_17)!='#skF_3')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.65/1.15  tff(c_77, plain, (![E_47, B_48, C_49]: (~r2_hidden(E_47, '#skF_4') | k4_tarski(E_47, '#skF_2'('#skF_3', B_48, C_49))!='#skF_3' | ~r2_hidden('#skF_3', k2_zfmisc_1(B_48, C_49)))), inference(resolution, [status(thm)], [c_70, c_12])).
% 1.65/1.15  tff(c_81, plain, (![B_2, C_3]: (~r2_hidden('#skF_1'('#skF_3', B_2, C_3), '#skF_4') | ~r2_hidden('#skF_3', k2_zfmisc_1(B_2, C_3)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_77])).
% 1.65/1.15  tff(c_96, plain, (![B_57, C_58]: (~r2_hidden('#skF_3', k2_zfmisc_1(B_57, C_58)))), inference(resolution, [status(thm)], [c_90, c_81])).
% 1.65/1.15  tff(c_99, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_25])).
% 1.65/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.65/1.15  
% 1.65/1.15  Inference rules
% 1.65/1.15  ----------------------
% 1.65/1.15  #Ref     : 0
% 1.65/1.15  #Sup     : 20
% 1.65/1.15  #Fact    : 0
% 1.65/1.15  #Define  : 0
% 1.65/1.15  #Split   : 0
% 1.65/1.15  #Chain   : 0
% 1.65/1.15  #Close   : 0
% 1.65/1.15  
% 1.65/1.15  Ordering : KBO
% 1.65/1.15  
% 1.65/1.15  Simplification rules
% 1.65/1.15  ----------------------
% 1.65/1.15  #Subsume      : 4
% 1.65/1.15  #Demod        : 0
% 1.65/1.15  #Tautology    : 4
% 1.65/1.15  #SimpNegUnit  : 1
% 1.65/1.15  #BackRed      : 1
% 1.65/1.15  
% 1.65/1.15  #Partial instantiations: 0
% 1.65/1.15  #Strategies tried      : 1
% 1.65/1.15  
% 1.65/1.15  Timing (in seconds)
% 1.65/1.15  ----------------------
% 1.65/1.15  Preprocessing        : 0.26
% 1.65/1.15  Parsing              : 0.15
% 1.65/1.15  CNF conversion       : 0.02
% 1.65/1.15  Main loop            : 0.13
% 1.65/1.15  Inferencing          : 0.06
% 1.65/1.15  Reduction            : 0.03
% 1.65/1.15  Demodulation         : 0.02
% 1.65/1.15  BG Simplification    : 0.01
% 1.65/1.15  Subsumption          : 0.03
% 1.65/1.15  Abstraction          : 0.01
% 1.65/1.15  MUC search           : 0.00
% 1.65/1.15  Cooper               : 0.00
% 1.65/1.15  Total                : 0.42
% 1.65/1.15  Index Insertion      : 0.00
% 1.65/1.15  Index Deletion       : 0.00
% 1.65/1.15  Index Matching       : 0.00
% 1.65/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
