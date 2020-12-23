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
% DateTime   : Thu Dec  3 09:57:33 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :   45 (  99 expanded)
%              Number of leaves         :   24 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :   49 ( 157 expanded)
%              Number of equality atoms :   20 (  63 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k4_tarski > k2_zfmisc_1 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_2 > #skF_6 > #skF_9 > #skF_5 > #skF_3 > #skF_8 > #skF_7

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_46,plain,(
    r1_setfam_1('#skF_9',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_42,plain,(
    ! [A_39,B_40] :
      ( r2_hidden('#skF_7'(A_39,B_40),A_39)
      | r1_setfam_1(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_100,plain,(
    ! [A_64,B_65,C_66] :
      ( r2_hidden('#skF_8'(A_64,B_65,C_66),B_65)
      | ~ r2_hidden(C_66,A_64)
      | ~ r1_setfam_1(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_30,plain,(
    ! [A_35] : k2_zfmisc_1(A_35,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_73,plain,(
    ! [A_53,B_54] : ~ r2_hidden(A_53,k2_zfmisc_1(A_53,B_54)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_76,plain,(
    ! [A_35] : ~ r2_hidden(A_35,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_73])).

tff(c_106,plain,(
    ! [C_67,A_68] :
      ( ~ r2_hidden(C_67,A_68)
      | ~ r1_setfam_1(A_68,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_100,c_76])).

tff(c_115,plain,(
    ! [A_69,B_70] :
      ( ~ r1_setfam_1(A_69,k1_xboole_0)
      | r1_setfam_1(A_69,B_70) ) ),
    inference(resolution,[status(thm)],[c_42,c_106])).

tff(c_123,plain,(
    ! [B_70] : r1_setfam_1('#skF_9',B_70) ),
    inference(resolution,[status(thm)],[c_46,c_115])).

tff(c_890,plain,(
    ! [A_169,B_170,C_171] :
      ( r2_hidden('#skF_3'(A_169,B_170,C_171),B_170)
      | r2_hidden('#skF_4'(A_169,B_170,C_171),C_171)
      | k2_zfmisc_1(A_169,B_170) = C_171 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1010,plain,(
    ! [A_172,B_173] :
      ( r2_hidden('#skF_3'(A_172,B_173,k1_xboole_0),B_173)
      | k2_zfmisc_1(A_172,B_173) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_890,c_76])).

tff(c_105,plain,(
    ! [C_66,A_64] :
      ( ~ r2_hidden(C_66,A_64)
      | ~ r1_setfam_1(A_64,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_100,c_76])).

tff(c_1073,plain,(
    ! [B_174,A_175] :
      ( ~ r1_setfam_1(B_174,k1_xboole_0)
      | k2_zfmisc_1(A_175,B_174) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1010,c_105])).

tff(c_1115,plain,(
    ! [A_176] : k2_zfmisc_1(A_176,'#skF_9') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_123,c_1073])).

tff(c_28,plain,(
    ! [B_36,A_35] :
      ( k1_xboole_0 = B_36
      | k1_xboole_0 = A_35
      | k2_zfmisc_1(A_35,B_36) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1193,plain,(
    ! [A_176] :
      ( k1_xboole_0 = '#skF_9'
      | k1_xboole_0 = A_176 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1115,c_28])).

tff(c_1245,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1193])).

tff(c_1240,plain,(
    ! [A_176] : k1_xboole_0 = A_176 ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_1193])).

tff(c_1359,plain,(
    ! [A_1440] : A_1440 = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_1245,c_1240])).

tff(c_1477,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_1359,c_44])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 19:30:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.00/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.00/1.46  
% 3.00/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.46  %$ r2_hidden > r1_tarski > r1_setfam_1 > k4_tarski > k2_zfmisc_1 > #nlpp > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_2 > #skF_6 > #skF_9 > #skF_5 > #skF_3 > #skF_8 > #skF_7
% 3.14/1.46  
% 3.14/1.46  %Foreground sorts:
% 3.14/1.46  
% 3.14/1.46  
% 3.14/1.46  %Background operators:
% 3.14/1.46  
% 3.14/1.46  
% 3.14/1.46  %Foreground operators:
% 3.14/1.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.14/1.46  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 3.14/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.46  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 3.14/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.14/1.46  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.14/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.14/1.46  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.14/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.14/1.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.14/1.46  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 3.14/1.46  tff('#skF_9', type, '#skF_9': $i).
% 3.14/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.46  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 3.14/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.14/1.46  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.14/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.46  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 3.14/1.46  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.14/1.46  
% 3.14/1.47  tff(f_64, negated_conjecture, ~(![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_setfam_1)).
% 3.14/1.47  tff(f_59, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_setfam_1)).
% 3.14/1.47  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.14/1.47  tff(f_47, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.14/1.47  tff(f_38, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 3.14/1.47  tff(c_44, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.14/1.47  tff(c_46, plain, (r1_setfam_1('#skF_9', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.14/1.47  tff(c_42, plain, (![A_39, B_40]: (r2_hidden('#skF_7'(A_39, B_40), A_39) | r1_setfam_1(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.14/1.47  tff(c_100, plain, (![A_64, B_65, C_66]: (r2_hidden('#skF_8'(A_64, B_65, C_66), B_65) | ~r2_hidden(C_66, A_64) | ~r1_setfam_1(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.14/1.47  tff(c_30, plain, (![A_35]: (k2_zfmisc_1(A_35, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.14/1.47  tff(c_73, plain, (![A_53, B_54]: (~r2_hidden(A_53, k2_zfmisc_1(A_53, B_54)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.14/1.47  tff(c_76, plain, (![A_35]: (~r2_hidden(A_35, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_73])).
% 3.14/1.47  tff(c_106, plain, (![C_67, A_68]: (~r2_hidden(C_67, A_68) | ~r1_setfam_1(A_68, k1_xboole_0))), inference(resolution, [status(thm)], [c_100, c_76])).
% 3.14/1.47  tff(c_115, plain, (![A_69, B_70]: (~r1_setfam_1(A_69, k1_xboole_0) | r1_setfam_1(A_69, B_70))), inference(resolution, [status(thm)], [c_42, c_106])).
% 3.14/1.47  tff(c_123, plain, (![B_70]: (r1_setfam_1('#skF_9', B_70))), inference(resolution, [status(thm)], [c_46, c_115])).
% 3.14/1.47  tff(c_890, plain, (![A_169, B_170, C_171]: (r2_hidden('#skF_3'(A_169, B_170, C_171), B_170) | r2_hidden('#skF_4'(A_169, B_170, C_171), C_171) | k2_zfmisc_1(A_169, B_170)=C_171)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.14/1.47  tff(c_1010, plain, (![A_172, B_173]: (r2_hidden('#skF_3'(A_172, B_173, k1_xboole_0), B_173) | k2_zfmisc_1(A_172, B_173)=k1_xboole_0)), inference(resolution, [status(thm)], [c_890, c_76])).
% 3.14/1.47  tff(c_105, plain, (![C_66, A_64]: (~r2_hidden(C_66, A_64) | ~r1_setfam_1(A_64, k1_xboole_0))), inference(resolution, [status(thm)], [c_100, c_76])).
% 3.14/1.47  tff(c_1073, plain, (![B_174, A_175]: (~r1_setfam_1(B_174, k1_xboole_0) | k2_zfmisc_1(A_175, B_174)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1010, c_105])).
% 3.14/1.47  tff(c_1115, plain, (![A_176]: (k2_zfmisc_1(A_176, '#skF_9')=k1_xboole_0)), inference(resolution, [status(thm)], [c_123, c_1073])).
% 3.14/1.47  tff(c_28, plain, (![B_36, A_35]: (k1_xboole_0=B_36 | k1_xboole_0=A_35 | k2_zfmisc_1(A_35, B_36)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.14/1.47  tff(c_1193, plain, (![A_176]: (k1_xboole_0='#skF_9' | k1_xboole_0=A_176)), inference(superposition, [status(thm), theory('equality')], [c_1115, c_28])).
% 3.14/1.47  tff(c_1245, plain, (k1_xboole_0='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_44, c_1193])).
% 3.14/1.47  tff(c_1240, plain, (![A_176]: (k1_xboole_0=A_176)), inference(negUnitSimplification, [status(thm)], [c_44, c_1193])).
% 3.14/1.47  tff(c_1359, plain, (![A_1440]: (A_1440='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_1245, c_1240])).
% 3.14/1.47  tff(c_1477, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_1359, c_44])).
% 3.14/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/1.47  
% 3.14/1.47  Inference rules
% 3.14/1.47  ----------------------
% 3.14/1.47  #Ref     : 0
% 3.14/1.47  #Sup     : 371
% 3.14/1.47  #Fact    : 0
% 3.14/1.47  #Define  : 0
% 3.14/1.47  #Split   : 0
% 3.14/1.47  #Chain   : 0
% 3.14/1.47  #Close   : 0
% 3.14/1.47  
% 3.14/1.47  Ordering : KBO
% 3.14/1.47  
% 3.14/1.47  Simplification rules
% 3.14/1.47  ----------------------
% 3.14/1.47  #Subsume      : 116
% 3.14/1.48  #Demod        : 125
% 3.14/1.48  #Tautology    : 68
% 3.14/1.48  #SimpNegUnit  : 7
% 3.14/1.48  #BackRed      : 0
% 3.14/1.48  
% 3.14/1.48  #Partial instantiations: 43
% 3.14/1.48  #Strategies tried      : 1
% 3.14/1.48  
% 3.14/1.48  Timing (in seconds)
% 3.14/1.48  ----------------------
% 3.14/1.48  Preprocessing        : 0.28
% 3.14/1.48  Parsing              : 0.14
% 3.14/1.48  CNF conversion       : 0.02
% 3.14/1.48  Main loop            : 0.41
% 3.14/1.48  Inferencing          : 0.17
% 3.14/1.48  Reduction            : 0.10
% 3.14/1.48  Demodulation         : 0.07
% 3.14/1.48  BG Simplification    : 0.02
% 3.14/1.48  Subsumption          : 0.09
% 3.14/1.48  Abstraction          : 0.02
% 3.14/1.48  MUC search           : 0.00
% 3.14/1.48  Cooper               : 0.00
% 3.14/1.48  Total                : 0.72
% 3.14/1.48  Index Insertion      : 0.00
% 3.14/1.48  Index Deletion       : 0.00
% 3.14/1.48  Index Matching       : 0.00
% 3.14/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
