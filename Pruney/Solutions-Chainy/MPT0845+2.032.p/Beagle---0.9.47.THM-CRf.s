%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:48 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   44 (  49 expanded)
%              Number of leaves         :   24 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   57 (  76 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_69,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(f_74,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

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

tff(c_34,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_197,plain,(
    ! [A_86,B_87] :
      ( r2_hidden(k4_tarski('#skF_4'(A_86,B_87),'#skF_3'(A_86,B_87)),A_86)
      | r2_hidden('#skF_5'(A_86,B_87),B_87)
      | k2_relat_1(A_86) = B_87 ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_56,plain,(
    ! [A_43,B_44] :
      ( r2_hidden('#skF_2'(A_43,B_44),B_44)
      | ~ r2_hidden(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_30,plain,(
    ! [B_34,A_33] :
      ( ~ r1_tarski(B_34,A_33)
      | ~ r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_78,plain,(
    ! [B_49,A_50] :
      ( ~ r1_tarski(B_49,'#skF_2'(A_50,B_49))
      | ~ r2_hidden(A_50,B_49) ) ),
    inference(resolution,[status(thm)],[c_56,c_30])).

tff(c_83,plain,(
    ! [A_50] : ~ r2_hidden(A_50,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_78])).

tff(c_208,plain,(
    ! [B_87] :
      ( r2_hidden('#skF_5'(k1_xboole_0,B_87),B_87)
      | k2_relat_1(k1_xboole_0) = B_87 ) ),
    inference(resolution,[status(thm)],[c_197,c_83])).

tff(c_219,plain,(
    ! [B_87] :
      ( r2_hidden('#skF_5'(k1_xboole_0,B_87),B_87)
      | k1_xboole_0 = B_87 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_208])).

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

tff(c_125,plain,(
    ! [D_65,A_66,B_67] :
      ( ~ r2_hidden(D_65,'#skF_2'(A_66,B_67))
      | ~ r2_hidden(D_65,B_67)
      | ~ r2_hidden(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_318,plain,(
    ! [A_104,B_105,B_106] :
      ( ~ r2_hidden('#skF_1'('#skF_2'(A_104,B_105),B_106),B_105)
      | ~ r2_hidden(A_104,B_105)
      | r1_xboole_0('#skF_2'(A_104,B_105),B_106) ) ),
    inference(resolution,[status(thm)],[c_6,c_125])).

tff(c_324,plain,(
    ! [A_107,B_108] :
      ( ~ r2_hidden(A_107,B_108)
      | r1_xboole_0('#skF_2'(A_107,B_108),B_108) ) ),
    inference(resolution,[status(thm)],[c_4,c_318])).

tff(c_32,plain,(
    ! [B_36] :
      ( ~ r1_xboole_0(B_36,'#skF_7')
      | ~ r2_hidden(B_36,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_65,plain,(
    ! [A_43] :
      ( ~ r1_xboole_0('#skF_2'(A_43,'#skF_7'),'#skF_7')
      | ~ r2_hidden(A_43,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_56,c_32])).

tff(c_333,plain,(
    ! [A_109] : ~ r2_hidden(A_109,'#skF_7') ),
    inference(resolution,[status(thm)],[c_324,c_65])).

tff(c_339,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_219,c_333])).

tff(c_363,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_339])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n017.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 18:06:01 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.26  
% 2.12/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.26  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 2.12/1.26  
% 2.12/1.26  %Foreground sorts:
% 2.12/1.26  
% 2.12/1.26  
% 2.12/1.26  %Background operators:
% 2.12/1.26  
% 2.12/1.26  
% 2.12/1.26  %Foreground operators:
% 2.12/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.12/1.26  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.12/1.26  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.12/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.12/1.26  tff('#skF_7', type, '#skF_7': $i).
% 2.12/1.26  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.12/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.12/1.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.12/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.12/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.12/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.12/1.26  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.12/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.12/1.26  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.12/1.26  
% 2.12/1.27  tff(f_85, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_mcart_1)).
% 2.12/1.27  tff(f_69, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.12/1.27  tff(f_66, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 2.12/1.27  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.12/1.27  tff(f_58, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 2.12/1.27  tff(f_74, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.12/1.27  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.12/1.27  tff(c_34, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.12/1.27  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.12/1.27  tff(c_197, plain, (![A_86, B_87]: (r2_hidden(k4_tarski('#skF_4'(A_86, B_87), '#skF_3'(A_86, B_87)), A_86) | r2_hidden('#skF_5'(A_86, B_87), B_87) | k2_relat_1(A_86)=B_87)), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.12/1.27  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.12/1.27  tff(c_56, plain, (![A_43, B_44]: (r2_hidden('#skF_2'(A_43, B_44), B_44) | ~r2_hidden(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.12/1.27  tff(c_30, plain, (![B_34, A_33]: (~r1_tarski(B_34, A_33) | ~r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.12/1.27  tff(c_78, plain, (![B_49, A_50]: (~r1_tarski(B_49, '#skF_2'(A_50, B_49)) | ~r2_hidden(A_50, B_49))), inference(resolution, [status(thm)], [c_56, c_30])).
% 2.12/1.27  tff(c_83, plain, (![A_50]: (~r2_hidden(A_50, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_78])).
% 2.12/1.27  tff(c_208, plain, (![B_87]: (r2_hidden('#skF_5'(k1_xboole_0, B_87), B_87) | k2_relat_1(k1_xboole_0)=B_87)), inference(resolution, [status(thm)], [c_197, c_83])).
% 2.12/1.27  tff(c_219, plain, (![B_87]: (r2_hidden('#skF_5'(k1_xboole_0, B_87), B_87) | k1_xboole_0=B_87)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_208])).
% 2.12/1.27  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.12/1.27  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.12/1.27  tff(c_125, plain, (![D_65, A_66, B_67]: (~r2_hidden(D_65, '#skF_2'(A_66, B_67)) | ~r2_hidden(D_65, B_67) | ~r2_hidden(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.12/1.27  tff(c_318, plain, (![A_104, B_105, B_106]: (~r2_hidden('#skF_1'('#skF_2'(A_104, B_105), B_106), B_105) | ~r2_hidden(A_104, B_105) | r1_xboole_0('#skF_2'(A_104, B_105), B_106))), inference(resolution, [status(thm)], [c_6, c_125])).
% 2.12/1.27  tff(c_324, plain, (![A_107, B_108]: (~r2_hidden(A_107, B_108) | r1_xboole_0('#skF_2'(A_107, B_108), B_108))), inference(resolution, [status(thm)], [c_4, c_318])).
% 2.12/1.27  tff(c_32, plain, (![B_36]: (~r1_xboole_0(B_36, '#skF_7') | ~r2_hidden(B_36, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.12/1.27  tff(c_65, plain, (![A_43]: (~r1_xboole_0('#skF_2'(A_43, '#skF_7'), '#skF_7') | ~r2_hidden(A_43, '#skF_7'))), inference(resolution, [status(thm)], [c_56, c_32])).
% 2.12/1.27  tff(c_333, plain, (![A_109]: (~r2_hidden(A_109, '#skF_7'))), inference(resolution, [status(thm)], [c_324, c_65])).
% 2.12/1.27  tff(c_339, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_219, c_333])).
% 2.12/1.27  tff(c_363, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_339])).
% 2.12/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.27  
% 2.12/1.27  Inference rules
% 2.12/1.27  ----------------------
% 2.12/1.27  #Ref     : 0
% 2.12/1.27  #Sup     : 62
% 2.12/1.27  #Fact    : 0
% 2.12/1.27  #Define  : 0
% 2.12/1.27  #Split   : 0
% 2.12/1.27  #Chain   : 0
% 2.12/1.27  #Close   : 0
% 2.12/1.27  
% 2.12/1.27  Ordering : KBO
% 2.12/1.27  
% 2.12/1.27  Simplification rules
% 2.12/1.27  ----------------------
% 2.12/1.27  #Subsume      : 14
% 2.12/1.27  #Demod        : 14
% 2.12/1.27  #Tautology    : 12
% 2.12/1.27  #SimpNegUnit  : 5
% 2.12/1.27  #BackRed      : 0
% 2.12/1.27  
% 2.12/1.27  #Partial instantiations: 0
% 2.12/1.27  #Strategies tried      : 1
% 2.12/1.27  
% 2.12/1.27  Timing (in seconds)
% 2.12/1.27  ----------------------
% 2.12/1.28  Preprocessing        : 0.29
% 2.12/1.28  Parsing              : 0.16
% 2.12/1.28  CNF conversion       : 0.02
% 2.12/1.28  Main loop            : 0.23
% 2.12/1.28  Inferencing          : 0.10
% 2.12/1.28  Reduction            : 0.06
% 2.12/1.28  Demodulation         : 0.04
% 2.12/1.28  BG Simplification    : 0.01
% 2.12/1.28  Subsumption          : 0.04
% 2.12/1.28  Abstraction          : 0.01
% 2.12/1.28  MUC search           : 0.00
% 2.12/1.28  Cooper               : 0.00
% 2.12/1.28  Total                : 0.54
% 2.12/1.28  Index Insertion      : 0.00
% 2.12/1.28  Index Deletion       : 0.00
% 2.12/1.28  Index Matching       : 0.00
% 2.12/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
