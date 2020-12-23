%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:36 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   39 (  40 expanded)
%              Number of leaves         :   24 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   53 (  55 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_tarski > r2_hidden > r1_xboole_0 > r1_tarski > r1_setfam_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_7 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r2_tarski,type,(
    r2_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_103,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_78,axiom,(
    ! [A] :
    ? [B] :
      ( r2_hidden(A,B)
      & ! [C,D] :
          ( ( r2_hidden(C,B)
            & r1_tarski(D,C) )
         => r2_hidden(D,B) )
      & ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(k1_zfmisc_1(C),B) )
      & ! [C] :
          ~ ( r1_tarski(C,B)
            & ~ r2_tarski(C,B)
            & ~ r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_zfmisc_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(f_53,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_34,plain,(
    r1_setfam_1('#skF_7',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_183,plain,(
    ! [A_87,B_88,C_89] :
      ( r2_hidden('#skF_6'(A_87,B_88,C_89),B_88)
      | ~ r2_hidden(C_89,A_87)
      | ~ r1_setfam_1(A_87,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_18,plain,(
    ! [A_9] : r2_hidden(A_9,'#skF_3'(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_22,plain,(
    ! [A_27,B_28] :
      ( r2_hidden('#skF_4'(A_27,B_28),B_28)
      | ~ r2_hidden(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_10,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_42,plain,(
    ! [A_57,B_58,C_59] :
      ( ~ r1_xboole_0(A_57,B_58)
      | ~ r2_hidden(C_59,B_58)
      | ~ r2_hidden(C_59,A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_46,plain,(
    ! [C_60,A_61] :
      ( ~ r2_hidden(C_60,k1_xboole_0)
      | ~ r2_hidden(C_60,A_61) ) ),
    inference(resolution,[status(thm)],[c_10,c_42])).

tff(c_106,plain,(
    ! [A_73,A_74] :
      ( ~ r2_hidden('#skF_4'(A_73,k1_xboole_0),A_74)
      | ~ r2_hidden(A_73,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_46])).

tff(c_115,plain,(
    ! [A_73] : ~ r2_hidden(A_73,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_106])).

tff(c_194,plain,(
    ! [C_90,A_91] :
      ( ~ r2_hidden(C_90,A_91)
      | ~ r1_setfam_1(A_91,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_183,c_115])).

tff(c_228,plain,(
    ! [A_93] :
      ( ~ r1_setfam_1(A_93,k1_xboole_0)
      | k1_xboole_0 = A_93 ) ),
    inference(resolution,[status(thm)],[c_8,c_194])).

tff(c_235,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_34,c_228])).

tff(c_241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_235])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:50:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.25  
% 2.06/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.25  %$ r2_tarski > r2_hidden > r1_xboole_0 > r1_tarski > r1_setfam_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_7 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 2.06/1.25  
% 2.06/1.25  %Foreground sorts:
% 2.06/1.25  
% 2.06/1.25  
% 2.06/1.25  %Background operators:
% 2.06/1.25  
% 2.06/1.25  
% 2.06/1.25  %Foreground operators:
% 2.06/1.25  tff(r2_tarski, type, r2_tarski: ($i * $i) > $o).
% 2.06/1.25  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.06/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.25  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.06/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.25  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.06/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.25  tff('#skF_7', type, '#skF_7': $i).
% 2.06/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.06/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.06/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.25  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.06/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.06/1.25  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.06/1.25  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.06/1.25  
% 2.06/1.26  tff(f_108, negated_conjecture, ~(![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_setfam_1)).
% 2.06/1.26  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.06/1.26  tff(f_103, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 2.06/1.26  tff(f_78, axiom, (![A]: (?[B]: (((r2_hidden(A, B) & (![C, D]: ((r2_hidden(C, B) & r1_tarski(D, C)) => r2_hidden(D, B)))) & (![C]: (r2_hidden(C, B) => r2_hidden(k1_zfmisc_1(C), B)))) & (![C]: ~((r1_tarski(C, B) & ~r2_tarski(C, B)) & ~r2_hidden(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t136_zfmisc_1)).
% 2.06/1.26  tff(f_91, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 2.06/1.26  tff(f_53, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.06/1.26  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.06/1.26  tff(c_32, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.06/1.26  tff(c_34, plain, (r1_setfam_1('#skF_7', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.06/1.26  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.06/1.26  tff(c_183, plain, (![A_87, B_88, C_89]: (r2_hidden('#skF_6'(A_87, B_88, C_89), B_88) | ~r2_hidden(C_89, A_87) | ~r1_setfam_1(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.06/1.26  tff(c_18, plain, (![A_9]: (r2_hidden(A_9, '#skF_3'(A_9)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.06/1.26  tff(c_22, plain, (![A_27, B_28]: (r2_hidden('#skF_4'(A_27, B_28), B_28) | ~r2_hidden(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.06/1.26  tff(c_10, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.06/1.26  tff(c_42, plain, (![A_57, B_58, C_59]: (~r1_xboole_0(A_57, B_58) | ~r2_hidden(C_59, B_58) | ~r2_hidden(C_59, A_57))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.06/1.26  tff(c_46, plain, (![C_60, A_61]: (~r2_hidden(C_60, k1_xboole_0) | ~r2_hidden(C_60, A_61))), inference(resolution, [status(thm)], [c_10, c_42])).
% 2.06/1.26  tff(c_106, plain, (![A_73, A_74]: (~r2_hidden('#skF_4'(A_73, k1_xboole_0), A_74) | ~r2_hidden(A_73, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_46])).
% 2.06/1.26  tff(c_115, plain, (![A_73]: (~r2_hidden(A_73, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_106])).
% 2.06/1.26  tff(c_194, plain, (![C_90, A_91]: (~r2_hidden(C_90, A_91) | ~r1_setfam_1(A_91, k1_xboole_0))), inference(resolution, [status(thm)], [c_183, c_115])).
% 2.06/1.26  tff(c_228, plain, (![A_93]: (~r1_setfam_1(A_93, k1_xboole_0) | k1_xboole_0=A_93)), inference(resolution, [status(thm)], [c_8, c_194])).
% 2.06/1.26  tff(c_235, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_34, c_228])).
% 2.06/1.26  tff(c_241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_235])).
% 2.06/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.26  
% 2.06/1.26  Inference rules
% 2.06/1.26  ----------------------
% 2.06/1.26  #Ref     : 0
% 2.06/1.26  #Sup     : 38
% 2.06/1.26  #Fact    : 0
% 2.06/1.26  #Define  : 0
% 2.06/1.26  #Split   : 0
% 2.06/1.26  #Chain   : 0
% 2.06/1.26  #Close   : 0
% 2.06/1.26  
% 2.06/1.26  Ordering : KBO
% 2.06/1.26  
% 2.06/1.26  Simplification rules
% 2.06/1.26  ----------------------
% 2.06/1.26  #Subsume      : 7
% 2.06/1.26  #Demod        : 9
% 2.06/1.26  #Tautology    : 12
% 2.06/1.26  #SimpNegUnit  : 1
% 2.06/1.26  #BackRed      : 0
% 2.06/1.26  
% 2.06/1.26  #Partial instantiations: 0
% 2.06/1.26  #Strategies tried      : 1
% 2.06/1.26  
% 2.06/1.26  Timing (in seconds)
% 2.06/1.26  ----------------------
% 2.06/1.27  Preprocessing        : 0.31
% 2.06/1.27  Parsing              : 0.17
% 2.06/1.27  CNF conversion       : 0.02
% 2.06/1.27  Main loop            : 0.16
% 2.06/1.27  Inferencing          : 0.07
% 2.06/1.27  Reduction            : 0.04
% 2.06/1.27  Demodulation         : 0.03
% 2.06/1.27  BG Simplification    : 0.01
% 2.06/1.27  Subsumption          : 0.03
% 2.06/1.27  Abstraction          : 0.01
% 2.06/1.27  MUC search           : 0.00
% 2.06/1.27  Cooper               : 0.00
% 2.06/1.27  Total                : 0.49
% 2.06/1.27  Index Insertion      : 0.00
% 2.06/1.27  Index Deletion       : 0.00
% 2.06/1.27  Index Matching       : 0.00
% 2.06/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
