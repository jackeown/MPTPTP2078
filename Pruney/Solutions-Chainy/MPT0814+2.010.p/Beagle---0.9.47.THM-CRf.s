%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:52 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   34 (  38 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :    5
%              Number of atoms          :   39 (  59 expanded)
%              Number of equality atoms :    7 (  13 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
       => ~ ( r2_hidden(A,D)
            & ! [E,F] :
                ~ ( A = k4_tarski(E,F)
                  & r2_hidden(E,B)
                  & r2_hidden(F,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(c_8,plain,(
    ! [A_1,B_2,D_28] :
      ( r2_hidden('#skF_5'(A_1,B_2,k2_zfmisc_1(A_1,B_2),D_28),A_1)
      | ~ r2_hidden(D_28,k2_zfmisc_1(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_94,plain,(
    ! [A_77,B_78,D_79] :
      ( k4_tarski('#skF_5'(A_77,B_78,k2_zfmisc_1(A_77,B_78),D_79),'#skF_6'(A_77,B_78,k2_zfmisc_1(A_77,B_78),D_79)) = D_79
      | ~ r2_hidden(D_79,k2_zfmisc_1(A_77,B_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_51,plain,(
    ! [A_54,B_55,D_56] :
      ( r2_hidden('#skF_6'(A_54,B_55,k2_zfmisc_1(A_54,B_55),D_56),B_55)
      | ~ r2_hidden(D_56,k2_zfmisc_1(A_54,B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    ! [F_42,E_41] :
      ( ~ r2_hidden(F_42,'#skF_9')
      | ~ r2_hidden(E_41,'#skF_8')
      | k4_tarski(E_41,F_42) != '#skF_7' ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_57,plain,(
    ! [E_41,A_54,D_56] :
      ( ~ r2_hidden(E_41,'#skF_8')
      | k4_tarski(E_41,'#skF_6'(A_54,'#skF_9',k2_zfmisc_1(A_54,'#skF_9'),D_56)) != '#skF_7'
      | ~ r2_hidden(D_56,k2_zfmisc_1(A_54,'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_51,c_28])).

tff(c_181,plain,(
    ! [A_118,D_119] :
      ( ~ r2_hidden('#skF_5'(A_118,'#skF_9',k2_zfmisc_1(A_118,'#skF_9'),D_119),'#skF_8')
      | D_119 != '#skF_7'
      | ~ r2_hidden(D_119,k2_zfmisc_1(A_118,'#skF_9'))
      | ~ r2_hidden(D_119,k2_zfmisc_1(A_118,'#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_57])).

tff(c_192,plain,(
    ~ r2_hidden('#skF_7',k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_8,c_181])).

tff(c_32,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_30,plain,(
    r2_hidden('#skF_7','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_33,plain,(
    ! [C_43,A_44,B_45] :
      ( r2_hidden(C_43,A_44)
      | ~ r2_hidden(C_43,B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_37,plain,(
    ! [A_46] :
      ( r2_hidden('#skF_7',A_46)
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(A_46)) ) ),
    inference(resolution,[status(thm)],[c_30,c_33])).

tff(c_41,plain,(
    r2_hidden('#skF_7',k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_32,c_37])).

tff(c_194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_192,c_41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:42:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.34  
% 2.18/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.35  %$ r2_hidden > m1_subset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_5 > #skF_3
% 2.18/1.35  
% 2.18/1.35  %Foreground sorts:
% 2.18/1.35  
% 2.18/1.35  
% 2.18/1.35  %Background operators:
% 2.18/1.35  
% 2.18/1.35  
% 2.18/1.35  %Foreground operators:
% 2.18/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.18/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.18/1.35  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.18/1.35  tff('#skF_7', type, '#skF_7': $i).
% 2.18/1.35  tff('#skF_10', type, '#skF_10': $i).
% 2.18/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.18/1.35  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 2.18/1.35  tff('#skF_9', type, '#skF_9': $i).
% 2.18/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.35  tff('#skF_8', type, '#skF_8': $i).
% 2.18/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.35  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.18/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.18/1.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.18/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.35  
% 2.18/1.35  tff(f_37, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 2.18/1.35  tff(f_58, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => ~(r2_hidden(A, D) & (![E, F]: ~(((A = k4_tarski(E, F)) & r2_hidden(E, B)) & r2_hidden(F, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_relset_1)).
% 2.18/1.35  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.18/1.35  tff(c_8, plain, (![A_1, B_2, D_28]: (r2_hidden('#skF_5'(A_1, B_2, k2_zfmisc_1(A_1, B_2), D_28), A_1) | ~r2_hidden(D_28, k2_zfmisc_1(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.18/1.35  tff(c_94, plain, (![A_77, B_78, D_79]: (k4_tarski('#skF_5'(A_77, B_78, k2_zfmisc_1(A_77, B_78), D_79), '#skF_6'(A_77, B_78, k2_zfmisc_1(A_77, B_78), D_79))=D_79 | ~r2_hidden(D_79, k2_zfmisc_1(A_77, B_78)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.18/1.35  tff(c_51, plain, (![A_54, B_55, D_56]: (r2_hidden('#skF_6'(A_54, B_55, k2_zfmisc_1(A_54, B_55), D_56), B_55) | ~r2_hidden(D_56, k2_zfmisc_1(A_54, B_55)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.18/1.35  tff(c_28, plain, (![F_42, E_41]: (~r2_hidden(F_42, '#skF_9') | ~r2_hidden(E_41, '#skF_8') | k4_tarski(E_41, F_42)!='#skF_7')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.18/1.35  tff(c_57, plain, (![E_41, A_54, D_56]: (~r2_hidden(E_41, '#skF_8') | k4_tarski(E_41, '#skF_6'(A_54, '#skF_9', k2_zfmisc_1(A_54, '#skF_9'), D_56))!='#skF_7' | ~r2_hidden(D_56, k2_zfmisc_1(A_54, '#skF_9')))), inference(resolution, [status(thm)], [c_51, c_28])).
% 2.18/1.35  tff(c_181, plain, (![A_118, D_119]: (~r2_hidden('#skF_5'(A_118, '#skF_9', k2_zfmisc_1(A_118, '#skF_9'), D_119), '#skF_8') | D_119!='#skF_7' | ~r2_hidden(D_119, k2_zfmisc_1(A_118, '#skF_9')) | ~r2_hidden(D_119, k2_zfmisc_1(A_118, '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_94, c_57])).
% 2.18/1.35  tff(c_192, plain, (~r2_hidden('#skF_7', k2_zfmisc_1('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_8, c_181])).
% 2.18/1.35  tff(c_32, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.18/1.35  tff(c_30, plain, (r2_hidden('#skF_7', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.18/1.35  tff(c_33, plain, (![C_43, A_44, B_45]: (r2_hidden(C_43, A_44) | ~r2_hidden(C_43, B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.18/1.35  tff(c_37, plain, (![A_46]: (r2_hidden('#skF_7', A_46) | ~m1_subset_1('#skF_10', k1_zfmisc_1(A_46)))), inference(resolution, [status(thm)], [c_30, c_33])).
% 2.18/1.35  tff(c_41, plain, (r2_hidden('#skF_7', k2_zfmisc_1('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_32, c_37])).
% 2.18/1.35  tff(c_194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_192, c_41])).
% 2.18/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.35  
% 2.18/1.35  Inference rules
% 2.18/1.35  ----------------------
% 2.18/1.35  #Ref     : 0
% 2.18/1.35  #Sup     : 37
% 2.18/1.35  #Fact    : 0
% 2.18/1.35  #Define  : 0
% 2.18/1.35  #Split   : 0
% 2.18/1.35  #Chain   : 0
% 2.18/1.35  #Close   : 0
% 2.18/1.35  
% 2.18/1.35  Ordering : KBO
% 2.18/1.35  
% 2.18/1.35  Simplification rules
% 2.18/1.35  ----------------------
% 2.18/1.35  #Subsume      : 0
% 2.18/1.35  #Demod        : 0
% 2.18/1.35  #Tautology    : 2
% 2.18/1.35  #SimpNegUnit  : 1
% 2.18/1.35  #BackRed      : 1
% 2.18/1.35  
% 2.18/1.35  #Partial instantiations: 0
% 2.18/1.35  #Strategies tried      : 1
% 2.18/1.35  
% 2.18/1.35  Timing (in seconds)
% 2.18/1.35  ----------------------
% 2.18/1.36  Preprocessing        : 0.31
% 2.18/1.36  Parsing              : 0.16
% 2.18/1.36  CNF conversion       : 0.03
% 2.18/1.36  Main loop            : 0.21
% 2.18/1.36  Inferencing          : 0.09
% 2.18/1.36  Reduction            : 0.04
% 2.18/1.36  Demodulation         : 0.03
% 2.18/1.36  BG Simplification    : 0.02
% 2.18/1.36  Subsumption          : 0.05
% 2.18/1.36  Abstraction          : 0.01
% 2.18/1.36  MUC search           : 0.00
% 2.18/1.36  Cooper               : 0.00
% 2.18/1.36  Total                : 0.54
% 2.18/1.36  Index Insertion      : 0.00
% 2.18/1.36  Index Deletion       : 0.00
% 2.18/1.36  Index Matching       : 0.00
% 2.18/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
