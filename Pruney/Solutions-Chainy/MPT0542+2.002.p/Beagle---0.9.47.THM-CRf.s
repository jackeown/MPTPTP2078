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
% DateTime   : Thu Dec  3 10:00:32 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   38 (  41 expanded)
%              Number of leaves         :   23 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   49 (  57 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_5 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

tff(f_38,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,(
    ! [A_52] :
      ( r1_tarski(A_52,k2_zfmisc_1(k1_relat_1(A_52),k2_relat_1(A_52)))
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_145,plain,(
    ! [A_105,B_106,D_107] :
      ( r2_hidden(k4_tarski('#skF_5'(A_105,B_106,k9_relat_1(A_105,B_106),D_107),D_107),A_105)
      | ~ r2_hidden(D_107,k9_relat_1(A_105,B_106))
      | ~ v1_relat_1(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_334,plain,(
    ! [A_160,B_161,D_162,B_163] :
      ( r2_hidden(k4_tarski('#skF_5'(A_160,B_161,k9_relat_1(A_160,B_161),D_162),D_162),B_163)
      | ~ r1_tarski(A_160,B_163)
      | ~ r2_hidden(D_162,k9_relat_1(A_160,B_161))
      | ~ v1_relat_1(A_160) ) ),
    inference(resolution,[status(thm)],[c_145,c_2])).

tff(c_10,plain,(
    ! [B_7,D_9,A_6,C_8] :
      ( r2_hidden(B_7,D_9)
      | ~ r2_hidden(k4_tarski(A_6,B_7),k2_zfmisc_1(C_8,D_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_382,plain,(
    ! [C_170,D_168,A_171,D_169,B_167] :
      ( r2_hidden(D_168,D_169)
      | ~ r1_tarski(A_171,k2_zfmisc_1(C_170,D_169))
      | ~ r2_hidden(D_168,k9_relat_1(A_171,B_167))
      | ~ v1_relat_1(A_171) ) ),
    inference(resolution,[status(thm)],[c_334,c_10])).

tff(c_397,plain,(
    ! [D_172,A_173,B_174] :
      ( r2_hidden(D_172,k2_relat_1(A_173))
      | ~ r2_hidden(D_172,k9_relat_1(A_173,B_174))
      | ~ v1_relat_1(A_173) ) ),
    inference(resolution,[status(thm)],[c_32,c_382])).

tff(c_473,plain,(
    ! [A_175,B_176,B_177] :
      ( r2_hidden('#skF_1'(k9_relat_1(A_175,B_176),B_177),k2_relat_1(A_175))
      | ~ v1_relat_1(A_175)
      | r1_tarski(k9_relat_1(A_175,B_176),B_177) ) ),
    inference(resolution,[status(thm)],[c_6,c_397])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_498,plain,(
    ! [A_182,B_183] :
      ( ~ v1_relat_1(A_182)
      | r1_tarski(k9_relat_1(A_182,B_183),k2_relat_1(A_182)) ) ),
    inference(resolution,[status(thm)],[c_473,c_4])).

tff(c_34,plain,(
    ~ r1_tarski(k9_relat_1('#skF_7','#skF_6'),k2_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_505,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_498,c_34])).

tff(c_511,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_505])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:26:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.93/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.47  
% 2.93/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.47  %$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_5 > #skF_3 > #skF_1
% 2.93/1.47  
% 2.93/1.47  %Foreground sorts:
% 2.93/1.47  
% 2.93/1.47  
% 2.93/1.47  %Background operators:
% 2.93/1.47  
% 2.93/1.47  
% 2.93/1.47  %Foreground operators:
% 2.93/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.93/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.93/1.47  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.93/1.47  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.93/1.47  tff('#skF_7', type, '#skF_7': $i).
% 2.93/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.93/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.93/1.47  tff('#skF_6', type, '#skF_6': $i).
% 2.93/1.47  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.93/1.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.93/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.93/1.47  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.93/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.93/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.93/1.47  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.93/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.93/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.93/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.93/1.47  
% 3.08/1.48  tff(f_60, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 3.08/1.48  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.08/1.48  tff(f_55, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 3.08/1.48  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_relat_1)).
% 3.08/1.48  tff(f_38, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.08/1.48  tff(c_36, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.08/1.48  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.08/1.48  tff(c_32, plain, (![A_52]: (r1_tarski(A_52, k2_zfmisc_1(k1_relat_1(A_52), k2_relat_1(A_52))) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.08/1.48  tff(c_145, plain, (![A_105, B_106, D_107]: (r2_hidden(k4_tarski('#skF_5'(A_105, B_106, k9_relat_1(A_105, B_106), D_107), D_107), A_105) | ~r2_hidden(D_107, k9_relat_1(A_105, B_106)) | ~v1_relat_1(A_105))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.08/1.48  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.08/1.48  tff(c_334, plain, (![A_160, B_161, D_162, B_163]: (r2_hidden(k4_tarski('#skF_5'(A_160, B_161, k9_relat_1(A_160, B_161), D_162), D_162), B_163) | ~r1_tarski(A_160, B_163) | ~r2_hidden(D_162, k9_relat_1(A_160, B_161)) | ~v1_relat_1(A_160))), inference(resolution, [status(thm)], [c_145, c_2])).
% 3.08/1.48  tff(c_10, plain, (![B_7, D_9, A_6, C_8]: (r2_hidden(B_7, D_9) | ~r2_hidden(k4_tarski(A_6, B_7), k2_zfmisc_1(C_8, D_9)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.08/1.48  tff(c_382, plain, (![C_170, D_168, A_171, D_169, B_167]: (r2_hidden(D_168, D_169) | ~r1_tarski(A_171, k2_zfmisc_1(C_170, D_169)) | ~r2_hidden(D_168, k9_relat_1(A_171, B_167)) | ~v1_relat_1(A_171))), inference(resolution, [status(thm)], [c_334, c_10])).
% 3.08/1.48  tff(c_397, plain, (![D_172, A_173, B_174]: (r2_hidden(D_172, k2_relat_1(A_173)) | ~r2_hidden(D_172, k9_relat_1(A_173, B_174)) | ~v1_relat_1(A_173))), inference(resolution, [status(thm)], [c_32, c_382])).
% 3.08/1.48  tff(c_473, plain, (![A_175, B_176, B_177]: (r2_hidden('#skF_1'(k9_relat_1(A_175, B_176), B_177), k2_relat_1(A_175)) | ~v1_relat_1(A_175) | r1_tarski(k9_relat_1(A_175, B_176), B_177))), inference(resolution, [status(thm)], [c_6, c_397])).
% 3.08/1.48  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.08/1.48  tff(c_498, plain, (![A_182, B_183]: (~v1_relat_1(A_182) | r1_tarski(k9_relat_1(A_182, B_183), k2_relat_1(A_182)))), inference(resolution, [status(thm)], [c_473, c_4])).
% 3.08/1.48  tff(c_34, plain, (~r1_tarski(k9_relat_1('#skF_7', '#skF_6'), k2_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.08/1.48  tff(c_505, plain, (~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_498, c_34])).
% 3.08/1.48  tff(c_511, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_505])).
% 3.08/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.48  
% 3.08/1.48  Inference rules
% 3.08/1.48  ----------------------
% 3.08/1.48  #Ref     : 0
% 3.08/1.48  #Sup     : 110
% 3.08/1.48  #Fact    : 0
% 3.08/1.48  #Define  : 0
% 3.08/1.48  #Split   : 0
% 3.08/1.48  #Chain   : 0
% 3.08/1.48  #Close   : 0
% 3.08/1.48  
% 3.08/1.48  Ordering : KBO
% 3.08/1.48  
% 3.08/1.48  Simplification rules
% 3.08/1.48  ----------------------
% 3.08/1.48  #Subsume      : 7
% 3.08/1.48  #Demod        : 1
% 3.08/1.48  #Tautology    : 3
% 3.08/1.48  #SimpNegUnit  : 0
% 3.08/1.48  #BackRed      : 0
% 3.08/1.48  
% 3.08/1.48  #Partial instantiations: 0
% 3.08/1.48  #Strategies tried      : 1
% 3.08/1.48  
% 3.08/1.48  Timing (in seconds)
% 3.08/1.48  ----------------------
% 3.08/1.49  Preprocessing        : 0.31
% 3.08/1.49  Parsing              : 0.16
% 3.08/1.49  CNF conversion       : 0.03
% 3.08/1.49  Main loop            : 0.37
% 3.08/1.49  Inferencing          : 0.15
% 3.08/1.49  Reduction            : 0.08
% 3.08/1.49  Demodulation         : 0.06
% 3.08/1.49  BG Simplification    : 0.02
% 3.08/1.49  Subsumption          : 0.10
% 3.08/1.49  Abstraction          : 0.02
% 3.08/1.49  MUC search           : 0.00
% 3.08/1.49  Cooper               : 0.00
% 3.08/1.49  Total                : 0.71
% 3.08/1.49  Index Insertion      : 0.00
% 3.08/1.49  Index Deletion       : 0.00
% 3.08/1.49  Index Matching       : 0.00
% 3.08/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
