%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:37 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   38 (  50 expanded)
%              Number of leaves         :   15 (  25 expanded)
%              Depth                    :   13
%              Number of atoms          :   75 ( 116 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > #nlpp > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_51,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_setfam_1(A,B)
          & r1_setfam_1(B,C) )
       => r1_setfam_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_setfam_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_16,plain,(
    ~ r1_setfam_1('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    r1_setfam_1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),A_6)
      | r1_setfam_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_18,plain,(
    r1_setfam_1('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [A_6,B_7,C_16] :
      ( r2_hidden('#skF_3'(A_6,B_7,C_16),B_7)
      | ~ r2_hidden(C_16,A_6)
      | ~ r1_setfam_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [C_16,A_6,B_7] :
      ( r1_tarski(C_16,'#skF_3'(A_6,B_7,C_16))
      | ~ r2_hidden(C_16,A_6)
      | ~ r1_setfam_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    ! [C_25,B_26,A_27] :
      ( r2_hidden(C_25,B_26)
      | ~ r2_hidden(C_25,A_27)
      | ~ r1_tarski(A_27,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,(
    ! [A_37,B_38,B_39] :
      ( r2_hidden('#skF_1'(A_37,B_38),B_39)
      | ~ r1_tarski(A_37,B_39)
      | r1_tarski(A_37,B_38) ) ),
    inference(resolution,[status(thm)],[c_6,c_30])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_96,plain,(
    ! [A_55,B_56,B_57,B_58] :
      ( r2_hidden('#skF_1'(A_55,B_56),B_57)
      | ~ r1_tarski(B_58,B_57)
      | ~ r1_tarski(A_55,B_58)
      | r1_tarski(A_55,B_56) ) ),
    inference(resolution,[status(thm)],[c_56,c_2])).

tff(c_205,plain,(
    ! [B_103,A_106,A_104,B_105,C_107] :
      ( r2_hidden('#skF_1'(A_104,B_103),'#skF_3'(A_106,B_105,C_107))
      | ~ r1_tarski(A_104,C_107)
      | r1_tarski(A_104,B_103)
      | ~ r2_hidden(C_107,A_106)
      | ~ r1_setfam_1(A_106,B_105) ) ),
    inference(resolution,[status(thm)],[c_8,c_96])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_214,plain,(
    ! [A_108,C_109,A_110,B_111] :
      ( ~ r1_tarski(A_108,C_109)
      | r1_tarski(A_108,'#skF_3'(A_110,B_111,C_109))
      | ~ r2_hidden(C_109,A_110)
      | ~ r1_setfam_1(A_110,B_111) ) ),
    inference(resolution,[status(thm)],[c_205,c_4])).

tff(c_12,plain,(
    ! [A_6,B_7,D_15] :
      ( ~ r1_tarski('#skF_2'(A_6,B_7),D_15)
      | ~ r2_hidden(D_15,B_7)
      | r1_setfam_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_239,plain,(
    ! [B_115,A_112,A_116,B_114,C_113] :
      ( ~ r2_hidden('#skF_3'(A_112,B_114,C_113),B_115)
      | r1_setfam_1(A_116,B_115)
      | ~ r1_tarski('#skF_2'(A_116,B_115),C_113)
      | ~ r2_hidden(C_113,A_112)
      | ~ r1_setfam_1(A_112,B_114) ) ),
    inference(resolution,[status(thm)],[c_214,c_12])).

tff(c_246,plain,(
    ! [A_117,B_118,C_119,A_120] :
      ( r1_setfam_1(A_117,B_118)
      | ~ r1_tarski('#skF_2'(A_117,B_118),C_119)
      | ~ r2_hidden(C_119,A_120)
      | ~ r1_setfam_1(A_120,B_118) ) ),
    inference(resolution,[status(thm)],[c_10,c_239])).

tff(c_357,plain,(
    ! [B_155,A_156,A_154,A_158,B_157] :
      ( r1_setfam_1(A_158,B_157)
      | ~ r2_hidden('#skF_3'(A_156,B_155,'#skF_2'(A_158,B_157)),A_154)
      | ~ r1_setfam_1(A_154,B_157)
      | ~ r2_hidden('#skF_2'(A_158,B_157),A_156)
      | ~ r1_setfam_1(A_156,B_155) ) ),
    inference(resolution,[status(thm)],[c_8,c_246])).

tff(c_385,plain,(
    ! [A_165,B_166,B_167,A_168] :
      ( r1_setfam_1(A_165,B_166)
      | ~ r1_setfam_1(B_167,B_166)
      | ~ r2_hidden('#skF_2'(A_165,B_166),A_168)
      | ~ r1_setfam_1(A_168,B_167) ) ),
    inference(resolution,[status(thm)],[c_10,c_357])).

tff(c_410,plain,(
    ! [A_169,A_170] :
      ( r1_setfam_1(A_169,'#skF_6')
      | ~ r2_hidden('#skF_2'(A_169,'#skF_6'),A_170)
      | ~ r1_setfam_1(A_170,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_18,c_385])).

tff(c_426,plain,(
    ! [A_171] :
      ( ~ r1_setfam_1(A_171,'#skF_5')
      | r1_setfam_1(A_171,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_14,c_410])).

tff(c_433,plain,(
    r1_setfam_1('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_426])).

tff(c_439,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_433])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:24:50 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.37  
% 2.77/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.37  %$ r2_hidden > r1_tarski > r1_setfam_1 > #nlpp > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.77/1.37  
% 2.77/1.37  %Foreground sorts:
% 2.77/1.37  
% 2.77/1.37  
% 2.77/1.37  %Background operators:
% 2.77/1.37  
% 2.77/1.37  
% 2.77/1.37  %Foreground operators:
% 2.77/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.37  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.77/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.77/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.77/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.77/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.77/1.37  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.77/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.77/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.77/1.37  
% 2.77/1.38  tff(f_51, negated_conjecture, ~(![A, B, C]: ((r1_setfam_1(A, B) & r1_setfam_1(B, C)) => r1_setfam_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_setfam_1)).
% 2.77/1.38  tff(f_44, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_setfam_1)).
% 2.77/1.38  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.77/1.38  tff(c_16, plain, (~r1_setfam_1('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.77/1.38  tff(c_20, plain, (r1_setfam_1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.77/1.38  tff(c_14, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), A_6) | r1_setfam_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.77/1.38  tff(c_18, plain, (r1_setfam_1('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.77/1.38  tff(c_10, plain, (![A_6, B_7, C_16]: (r2_hidden('#skF_3'(A_6, B_7, C_16), B_7) | ~r2_hidden(C_16, A_6) | ~r1_setfam_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.77/1.38  tff(c_8, plain, (![C_16, A_6, B_7]: (r1_tarski(C_16, '#skF_3'(A_6, B_7, C_16)) | ~r2_hidden(C_16, A_6) | ~r1_setfam_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.77/1.38  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.77/1.38  tff(c_30, plain, (![C_25, B_26, A_27]: (r2_hidden(C_25, B_26) | ~r2_hidden(C_25, A_27) | ~r1_tarski(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.77/1.38  tff(c_56, plain, (![A_37, B_38, B_39]: (r2_hidden('#skF_1'(A_37, B_38), B_39) | ~r1_tarski(A_37, B_39) | r1_tarski(A_37, B_38))), inference(resolution, [status(thm)], [c_6, c_30])).
% 2.77/1.38  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.77/1.38  tff(c_96, plain, (![A_55, B_56, B_57, B_58]: (r2_hidden('#skF_1'(A_55, B_56), B_57) | ~r1_tarski(B_58, B_57) | ~r1_tarski(A_55, B_58) | r1_tarski(A_55, B_56))), inference(resolution, [status(thm)], [c_56, c_2])).
% 2.77/1.38  tff(c_205, plain, (![B_103, A_106, A_104, B_105, C_107]: (r2_hidden('#skF_1'(A_104, B_103), '#skF_3'(A_106, B_105, C_107)) | ~r1_tarski(A_104, C_107) | r1_tarski(A_104, B_103) | ~r2_hidden(C_107, A_106) | ~r1_setfam_1(A_106, B_105))), inference(resolution, [status(thm)], [c_8, c_96])).
% 2.77/1.38  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.77/1.38  tff(c_214, plain, (![A_108, C_109, A_110, B_111]: (~r1_tarski(A_108, C_109) | r1_tarski(A_108, '#skF_3'(A_110, B_111, C_109)) | ~r2_hidden(C_109, A_110) | ~r1_setfam_1(A_110, B_111))), inference(resolution, [status(thm)], [c_205, c_4])).
% 2.77/1.38  tff(c_12, plain, (![A_6, B_7, D_15]: (~r1_tarski('#skF_2'(A_6, B_7), D_15) | ~r2_hidden(D_15, B_7) | r1_setfam_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.77/1.38  tff(c_239, plain, (![B_115, A_112, A_116, B_114, C_113]: (~r2_hidden('#skF_3'(A_112, B_114, C_113), B_115) | r1_setfam_1(A_116, B_115) | ~r1_tarski('#skF_2'(A_116, B_115), C_113) | ~r2_hidden(C_113, A_112) | ~r1_setfam_1(A_112, B_114))), inference(resolution, [status(thm)], [c_214, c_12])).
% 2.77/1.38  tff(c_246, plain, (![A_117, B_118, C_119, A_120]: (r1_setfam_1(A_117, B_118) | ~r1_tarski('#skF_2'(A_117, B_118), C_119) | ~r2_hidden(C_119, A_120) | ~r1_setfam_1(A_120, B_118))), inference(resolution, [status(thm)], [c_10, c_239])).
% 2.77/1.38  tff(c_357, plain, (![B_155, A_156, A_154, A_158, B_157]: (r1_setfam_1(A_158, B_157) | ~r2_hidden('#skF_3'(A_156, B_155, '#skF_2'(A_158, B_157)), A_154) | ~r1_setfam_1(A_154, B_157) | ~r2_hidden('#skF_2'(A_158, B_157), A_156) | ~r1_setfam_1(A_156, B_155))), inference(resolution, [status(thm)], [c_8, c_246])).
% 2.77/1.38  tff(c_385, plain, (![A_165, B_166, B_167, A_168]: (r1_setfam_1(A_165, B_166) | ~r1_setfam_1(B_167, B_166) | ~r2_hidden('#skF_2'(A_165, B_166), A_168) | ~r1_setfam_1(A_168, B_167))), inference(resolution, [status(thm)], [c_10, c_357])).
% 2.77/1.38  tff(c_410, plain, (![A_169, A_170]: (r1_setfam_1(A_169, '#skF_6') | ~r2_hidden('#skF_2'(A_169, '#skF_6'), A_170) | ~r1_setfam_1(A_170, '#skF_5'))), inference(resolution, [status(thm)], [c_18, c_385])).
% 2.77/1.38  tff(c_426, plain, (![A_171]: (~r1_setfam_1(A_171, '#skF_5') | r1_setfam_1(A_171, '#skF_6'))), inference(resolution, [status(thm)], [c_14, c_410])).
% 2.77/1.38  tff(c_433, plain, (r1_setfam_1('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_20, c_426])).
% 2.77/1.38  tff(c_439, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_433])).
% 2.77/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.38  
% 2.77/1.38  Inference rules
% 2.77/1.38  ----------------------
% 2.77/1.38  #Ref     : 0
% 2.77/1.38  #Sup     : 100
% 2.77/1.38  #Fact    : 0
% 2.77/1.38  #Define  : 0
% 2.77/1.38  #Split   : 0
% 2.77/1.38  #Chain   : 0
% 2.77/1.38  #Close   : 0
% 2.77/1.38  
% 2.77/1.38  Ordering : KBO
% 2.77/1.38  
% 2.77/1.38  Simplification rules
% 2.77/1.38  ----------------------
% 2.77/1.38  #Subsume      : 17
% 2.77/1.38  #Demod        : 4
% 2.77/1.38  #Tautology    : 6
% 2.77/1.38  #SimpNegUnit  : 1
% 2.77/1.38  #BackRed      : 0
% 2.77/1.38  
% 2.77/1.38  #Partial instantiations: 0
% 2.77/1.38  #Strategies tried      : 1
% 2.77/1.38  
% 2.77/1.38  Timing (in seconds)
% 2.77/1.38  ----------------------
% 2.77/1.39  Preprocessing        : 0.26
% 2.77/1.39  Parsing              : 0.14
% 2.77/1.39  CNF conversion       : 0.02
% 2.77/1.39  Main loop            : 0.36
% 2.77/1.39  Inferencing          : 0.14
% 2.77/1.39  Reduction            : 0.07
% 2.77/1.39  Demodulation         : 0.05
% 2.77/1.39  BG Simplification    : 0.02
% 2.77/1.39  Subsumption          : 0.11
% 2.77/1.39  Abstraction          : 0.01
% 2.77/1.39  MUC search           : 0.00
% 2.77/1.39  Cooper               : 0.00
% 2.77/1.39  Total                : 0.65
% 2.77/1.39  Index Insertion      : 0.00
% 2.77/1.39  Index Deletion       : 0.00
% 2.77/1.39  Index Matching       : 0.00
% 2.77/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
