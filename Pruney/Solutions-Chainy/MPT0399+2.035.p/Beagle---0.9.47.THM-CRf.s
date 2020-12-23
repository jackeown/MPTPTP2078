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
% DateTime   : Thu Dec  3 09:57:36 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   34 (  48 expanded)
%              Number of leaves         :   18 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   39 (  66 expanded)
%              Number of equality atoms :   11 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_28,plain,(
    r1_setfam_1('#skF_5',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_24,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_3'(A_8,B_9),A_8)
      | r1_setfam_1(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_84,plain,(
    ! [A_35,B_36,C_37] :
      ( r2_hidden('#skF_4'(A_35,B_36,C_37),B_36)
      | ~ r2_hidden(C_37,A_35)
      | ~ r1_setfam_1(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_51,plain,(
    ! [A_22,B_23] : ~ r2_hidden(A_22,k2_zfmisc_1(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_54,plain,(
    ! [A_4] : ~ r2_hidden(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_51])).

tff(c_90,plain,(
    ! [C_38,A_39] :
      ( ~ r2_hidden(C_38,A_39)
      | ~ r1_setfam_1(A_39,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_84,c_54])).

tff(c_103,plain,(
    ! [A_40,B_41] :
      ( ~ r1_setfam_1(A_40,k1_xboole_0)
      | r1_setfam_1(A_40,B_41) ) ),
    inference(resolution,[status(thm)],[c_24,c_90])).

tff(c_111,plain,(
    ! [B_41] : r1_setfam_1('#skF_5',B_41) ),
    inference(resolution,[status(thm)],[c_28,c_103])).

tff(c_112,plain,(
    ! [A_42,B_43] :
      ( r2_hidden('#skF_1'(A_42,B_43),B_43)
      | r2_hidden('#skF_2'(A_42,B_43),A_42)
      | B_43 = A_42 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_135,plain,(
    ! [B_45] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_45),B_45)
      | k1_xboole_0 = B_45 ) ),
    inference(resolution,[status(thm)],[c_112,c_54])).

tff(c_89,plain,(
    ! [C_37,A_35] :
      ( ~ r2_hidden(C_37,A_35)
      | ~ r1_setfam_1(A_35,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_84,c_54])).

tff(c_146,plain,(
    ! [B_46] :
      ( ~ r1_setfam_1(B_46,k1_xboole_0)
      | k1_xboole_0 = B_46 ) ),
    inference(resolution,[status(thm)],[c_135,c_89])).

tff(c_150,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_111,c_146])).

tff(c_158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_150])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:15:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.12  
% 1.67/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.12  %$ r2_hidden > r1_tarski > r1_setfam_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_4 > #skF_3 > #skF_5 > #skF_2 > #skF_1
% 1.67/1.12  
% 1.67/1.12  %Foreground sorts:
% 1.67/1.12  
% 1.67/1.12  
% 1.67/1.12  %Background operators:
% 1.67/1.12  
% 1.67/1.12  
% 1.67/1.12  %Foreground operators:
% 1.67/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.12  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.67/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.67/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.67/1.12  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.67/1.12  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.67/1.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.67/1.12  tff('#skF_5', type, '#skF_5': $i).
% 1.67/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.67/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.12  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.67/1.12  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.67/1.12  
% 1.79/1.13  tff(f_58, negated_conjecture, ~(![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_setfam_1)).
% 1.79/1.13  tff(f_53, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_setfam_1)).
% 1.79/1.13  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.79/1.13  tff(f_41, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.79/1.13  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 1.79/1.13  tff(c_26, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.79/1.13  tff(c_28, plain, (r1_setfam_1('#skF_5', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.79/1.13  tff(c_24, plain, (![A_8, B_9]: (r2_hidden('#skF_3'(A_8, B_9), A_8) | r1_setfam_1(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.79/1.13  tff(c_84, plain, (![A_35, B_36, C_37]: (r2_hidden('#skF_4'(A_35, B_36, C_37), B_36) | ~r2_hidden(C_37, A_35) | ~r1_setfam_1(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.79/1.13  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.79/1.13  tff(c_51, plain, (![A_22, B_23]: (~r2_hidden(A_22, k2_zfmisc_1(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.79/1.13  tff(c_54, plain, (![A_4]: (~r2_hidden(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_51])).
% 1.79/1.13  tff(c_90, plain, (![C_38, A_39]: (~r2_hidden(C_38, A_39) | ~r1_setfam_1(A_39, k1_xboole_0))), inference(resolution, [status(thm)], [c_84, c_54])).
% 1.79/1.13  tff(c_103, plain, (![A_40, B_41]: (~r1_setfam_1(A_40, k1_xboole_0) | r1_setfam_1(A_40, B_41))), inference(resolution, [status(thm)], [c_24, c_90])).
% 1.79/1.13  tff(c_111, plain, (![B_41]: (r1_setfam_1('#skF_5', B_41))), inference(resolution, [status(thm)], [c_28, c_103])).
% 1.79/1.13  tff(c_112, plain, (![A_42, B_43]: (r2_hidden('#skF_1'(A_42, B_43), B_43) | r2_hidden('#skF_2'(A_42, B_43), A_42) | B_43=A_42)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.79/1.13  tff(c_135, plain, (![B_45]: (r2_hidden('#skF_1'(k1_xboole_0, B_45), B_45) | k1_xboole_0=B_45)), inference(resolution, [status(thm)], [c_112, c_54])).
% 1.79/1.13  tff(c_89, plain, (![C_37, A_35]: (~r2_hidden(C_37, A_35) | ~r1_setfam_1(A_35, k1_xboole_0))), inference(resolution, [status(thm)], [c_84, c_54])).
% 1.79/1.13  tff(c_146, plain, (![B_46]: (~r1_setfam_1(B_46, k1_xboole_0) | k1_xboole_0=B_46)), inference(resolution, [status(thm)], [c_135, c_89])).
% 1.79/1.13  tff(c_150, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_111, c_146])).
% 1.79/1.13  tff(c_158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_150])).
% 1.79/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.13  
% 1.79/1.13  Inference rules
% 1.79/1.13  ----------------------
% 1.79/1.13  #Ref     : 0
% 1.79/1.13  #Sup     : 26
% 1.79/1.13  #Fact    : 0
% 1.79/1.13  #Define  : 0
% 1.79/1.13  #Split   : 0
% 1.79/1.13  #Chain   : 0
% 1.79/1.13  #Close   : 0
% 1.79/1.13  
% 1.79/1.13  Ordering : KBO
% 1.79/1.13  
% 1.79/1.13  Simplification rules
% 1.79/1.13  ----------------------
% 1.79/1.13  #Subsume      : 3
% 1.79/1.13  #Demod        : 3
% 1.79/1.13  #Tautology    : 12
% 1.79/1.13  #SimpNegUnit  : 1
% 1.79/1.13  #BackRed      : 0
% 1.79/1.13  
% 1.79/1.13  #Partial instantiations: 0
% 1.79/1.13  #Strategies tried      : 1
% 1.79/1.13  
% 1.79/1.13  Timing (in seconds)
% 1.79/1.13  ----------------------
% 1.79/1.14  Preprocessing        : 0.27
% 1.79/1.14  Parsing              : 0.14
% 1.79/1.14  CNF conversion       : 0.02
% 1.79/1.14  Main loop            : 0.12
% 1.79/1.14  Inferencing          : 0.05
% 1.79/1.14  Reduction            : 0.03
% 1.79/1.14  Demodulation         : 0.02
% 1.79/1.14  BG Simplification    : 0.01
% 1.79/1.14  Subsumption          : 0.02
% 1.79/1.14  Abstraction          : 0.01
% 1.79/1.14  MUC search           : 0.00
% 1.79/1.14  Cooper               : 0.00
% 1.79/1.14  Total                : 0.41
% 1.79/1.14  Index Insertion      : 0.00
% 1.79/1.14  Index Deletion       : 0.00
% 1.79/1.14  Index Matching       : 0.00
% 1.79/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
