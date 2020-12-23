%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:47 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   43 (  46 expanded)
%              Number of leaves         :   24 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   55 (  68 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_74,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

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

tff(f_63,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_165,plain,(
    ! [A_82,B_83] :
      ( r2_hidden(k4_tarski('#skF_3'(A_82,B_83),'#skF_4'(A_82,B_83)),A_82)
      | r2_hidden('#skF_5'(A_82,B_83),B_83)
      | k1_relat_1(A_82) = B_83 ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_57,plain,(
    ! [A_44,C_45,B_46] :
      ( ~ r2_hidden(A_44,C_45)
      | ~ r1_xboole_0(k2_tarski(A_44,B_46),C_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_62,plain,(
    ! [A_44] : ~ r2_hidden(A_44,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_57])).

tff(c_176,plain,(
    ! [B_83] :
      ( r2_hidden('#skF_5'(k1_xboole_0,B_83),B_83)
      | k1_relat_1(k1_xboole_0) = B_83 ) ),
    inference(resolution,[status(thm)],[c_165,c_62])).

tff(c_184,plain,(
    ! [B_83] :
      ( r2_hidden('#skF_5'(k1_xboole_0,B_83),B_83)
      | k1_xboole_0 = B_83 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_176])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_98,plain,(
    ! [D_60,A_61,B_62] :
      ( ~ r2_hidden(D_60,'#skF_2'(A_61,B_62))
      | ~ r2_hidden(D_60,B_62)
      | ~ r2_hidden(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_159,plain,(
    ! [A_79,B_80,B_81] :
      ( ~ r2_hidden('#skF_1'('#skF_2'(A_79,B_80),B_81),B_80)
      | ~ r2_hidden(A_79,B_80)
      | r1_xboole_0('#skF_2'(A_79,B_80),B_81) ) ),
    inference(resolution,[status(thm)],[c_6,c_98])).

tff(c_205,plain,(
    ! [A_85,B_86] :
      ( ~ r2_hidden(A_85,B_86)
      | r1_xboole_0('#skF_2'(A_85,B_86),B_86) ) ),
    inference(resolution,[status(thm)],[c_4,c_159])).

tff(c_77,plain,(
    ! [A_50,B_51] :
      ( r2_hidden('#skF_2'(A_50,B_51),B_51)
      | ~ r2_hidden(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_32,plain,(
    ! [B_37] :
      ( ~ r1_xboole_0(B_37,'#skF_7')
      | ~ r2_hidden(B_37,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_87,plain,(
    ! [A_50] :
      ( ~ r1_xboole_0('#skF_2'(A_50,'#skF_7'),'#skF_7')
      | ~ r2_hidden(A_50,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_77,c_32])).

tff(c_215,plain,(
    ! [A_88] : ~ r2_hidden(A_88,'#skF_7') ),
    inference(resolution,[status(thm)],[c_205,c_87])).

tff(c_219,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_184,c_215])).

tff(c_243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_219])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n001.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 14:35:59 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.62  
% 2.45/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.63  %$ r2_hidden > r1_xboole_0 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 2.45/1.63  
% 2.45/1.63  %Foreground sorts:
% 2.45/1.63  
% 2.45/1.63  
% 2.45/1.63  %Background operators:
% 2.45/1.63  
% 2.45/1.63  
% 2.45/1.63  %Foreground operators:
% 2.45/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.45/1.63  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.45/1.63  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.45/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.45/1.63  tff('#skF_7', type, '#skF_7': $i).
% 2.45/1.63  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.45/1.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.45/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.45/1.63  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.45/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.63  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.45/1.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.45/1.63  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.45/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.45/1.63  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.45/1.63  
% 2.45/1.65  tff(f_85, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_mcart_1)).
% 2.45/1.65  tff(f_74, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.45/1.65  tff(f_71, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 2.45/1.65  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.45/1.65  tff(f_50, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.45/1.65  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.45/1.65  tff(f_63, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 2.45/1.65  tff(c_34, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.45/1.65  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.45/1.65  tff(c_165, plain, (![A_82, B_83]: (r2_hidden(k4_tarski('#skF_3'(A_82, B_83), '#skF_4'(A_82, B_83)), A_82) | r2_hidden('#skF_5'(A_82, B_83), B_83) | k1_relat_1(A_82)=B_83)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.45/1.65  tff(c_8, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.45/1.65  tff(c_57, plain, (![A_44, C_45, B_46]: (~r2_hidden(A_44, C_45) | ~r1_xboole_0(k2_tarski(A_44, B_46), C_45))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.45/1.65  tff(c_62, plain, (![A_44]: (~r2_hidden(A_44, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_57])).
% 2.45/1.65  tff(c_176, plain, (![B_83]: (r2_hidden('#skF_5'(k1_xboole_0, B_83), B_83) | k1_relat_1(k1_xboole_0)=B_83)), inference(resolution, [status(thm)], [c_165, c_62])).
% 2.45/1.65  tff(c_184, plain, (![B_83]: (r2_hidden('#skF_5'(k1_xboole_0, B_83), B_83) | k1_xboole_0=B_83)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_176])).
% 2.45/1.65  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.45/1.65  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.45/1.65  tff(c_98, plain, (![D_60, A_61, B_62]: (~r2_hidden(D_60, '#skF_2'(A_61, B_62)) | ~r2_hidden(D_60, B_62) | ~r2_hidden(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.45/1.65  tff(c_159, plain, (![A_79, B_80, B_81]: (~r2_hidden('#skF_1'('#skF_2'(A_79, B_80), B_81), B_80) | ~r2_hidden(A_79, B_80) | r1_xboole_0('#skF_2'(A_79, B_80), B_81))), inference(resolution, [status(thm)], [c_6, c_98])).
% 2.45/1.65  tff(c_205, plain, (![A_85, B_86]: (~r2_hidden(A_85, B_86) | r1_xboole_0('#skF_2'(A_85, B_86), B_86))), inference(resolution, [status(thm)], [c_4, c_159])).
% 2.45/1.65  tff(c_77, plain, (![A_50, B_51]: (r2_hidden('#skF_2'(A_50, B_51), B_51) | ~r2_hidden(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.45/1.65  tff(c_32, plain, (![B_37]: (~r1_xboole_0(B_37, '#skF_7') | ~r2_hidden(B_37, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.45/1.65  tff(c_87, plain, (![A_50]: (~r1_xboole_0('#skF_2'(A_50, '#skF_7'), '#skF_7') | ~r2_hidden(A_50, '#skF_7'))), inference(resolution, [status(thm)], [c_77, c_32])).
% 2.45/1.65  tff(c_215, plain, (![A_88]: (~r2_hidden(A_88, '#skF_7'))), inference(resolution, [status(thm)], [c_205, c_87])).
% 2.45/1.65  tff(c_219, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_184, c_215])).
% 2.45/1.65  tff(c_243, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_219])).
% 2.45/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.65  
% 2.45/1.65  Inference rules
% 2.45/1.65  ----------------------
% 2.45/1.65  #Ref     : 0
% 2.45/1.65  #Sup     : 40
% 2.45/1.65  #Fact    : 0
% 2.45/1.65  #Define  : 0
% 2.45/1.65  #Split   : 0
% 2.45/1.65  #Chain   : 0
% 2.45/1.65  #Close   : 0
% 2.45/1.65  
% 2.45/1.65  Ordering : KBO
% 2.45/1.65  
% 2.45/1.65  Simplification rules
% 2.45/1.65  ----------------------
% 2.45/1.65  #Subsume      : 9
% 2.45/1.65  #Demod        : 4
% 2.45/1.65  #Tautology    : 7
% 2.45/1.65  #SimpNegUnit  : 3
% 2.45/1.65  #BackRed      : 0
% 2.45/1.65  
% 2.45/1.65  #Partial instantiations: 0
% 2.45/1.65  #Strategies tried      : 1
% 2.45/1.65  
% 2.45/1.65  Timing (in seconds)
% 2.45/1.65  ----------------------
% 2.45/1.65  Preprocessing        : 0.49
% 2.45/1.65  Parsing              : 0.25
% 2.45/1.65  CNF conversion       : 0.04
% 2.45/1.65  Main loop            : 0.30
% 2.45/1.65  Inferencing          : 0.13
% 2.45/1.65  Reduction            : 0.08
% 2.45/1.65  Demodulation         : 0.06
% 2.45/1.65  BG Simplification    : 0.02
% 2.45/1.65  Subsumption          : 0.06
% 2.45/1.65  Abstraction          : 0.01
% 2.45/1.65  MUC search           : 0.00
% 2.45/1.65  Cooper               : 0.00
% 2.45/1.65  Total                : 0.84
% 2.45/1.65  Index Insertion      : 0.00
% 2.45/1.65  Index Deletion       : 0.00
% 2.45/1.65  Index Matching       : 0.00
% 2.45/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
