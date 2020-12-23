%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:42 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.94s
% Verified   : 
% Statistics : Number of formulae       :   36 (  45 expanded)
%              Number of leaves         :   16 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   83 ( 134 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > #nlpp > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => ! [D] :
                    ( v1_relat_1(D)
                   => ( ( r1_tarski(A,B)
                        & r1_tarski(C,D) )
                     => r1_tarski(k5_relat_1(A,C),k5_relat_1(B,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(A,C),k5_relat_1(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_20,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_18,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_14,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_16,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_8,plain,(
    ! [C_12,A_6,B_10] :
      ( r1_tarski(k5_relat_1(C_12,A_6),k5_relat_1(C_12,B_10))
      | ~ r1_tarski(A_6,B_10)
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_142,plain,(
    ! [A_68,C_69,B_70] :
      ( r1_tarski(k5_relat_1(A_68,C_69),k5_relat_1(B_70,C_69))
      | ~ r1_tarski(A_68,B_70)
      | ~ v1_relat_1(C_69)
      | ~ v1_relat_1(B_70)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,(
    ! [C_35,B_36,A_37] :
      ( r2_hidden(C_35,B_36)
      | ~ r2_hidden(C_35,A_37)
      | ~ r1_tarski(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_37,plain,(
    ! [A_39,B_40,B_41] :
      ( r2_hidden('#skF_1'(A_39,B_40),B_41)
      | ~ r1_tarski(A_39,B_41)
      | r1_tarski(A_39,B_40) ) ),
    inference(resolution,[status(thm)],[c_6,c_32])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_44,plain,(
    ! [A_39,B_40,B_2,B_41] :
      ( r2_hidden('#skF_1'(A_39,B_40),B_2)
      | ~ r1_tarski(B_41,B_2)
      | ~ r1_tarski(A_39,B_41)
      | r1_tarski(A_39,B_40) ) ),
    inference(resolution,[status(thm)],[c_37,c_2])).

tff(c_210,plain,(
    ! [A_85,B_87,A_89,C_88,B_86] :
      ( r2_hidden('#skF_1'(A_85,B_86),k5_relat_1(B_87,C_88))
      | ~ r1_tarski(A_85,k5_relat_1(A_89,C_88))
      | r1_tarski(A_85,B_86)
      | ~ r1_tarski(A_89,B_87)
      | ~ v1_relat_1(C_88)
      | ~ v1_relat_1(B_87)
      | ~ v1_relat_1(A_89) ) ),
    inference(resolution,[status(thm)],[c_142,c_44])).

tff(c_790,plain,(
    ! [C_176,B_172,B_174,A_175,B_173] :
      ( r2_hidden('#skF_1'(k5_relat_1(C_176,A_175),B_172),k5_relat_1(B_173,B_174))
      | r1_tarski(k5_relat_1(C_176,A_175),B_172)
      | ~ r1_tarski(C_176,B_173)
      | ~ v1_relat_1(B_173)
      | ~ r1_tarski(A_175,B_174)
      | ~ v1_relat_1(C_176)
      | ~ v1_relat_1(B_174)
      | ~ v1_relat_1(A_175) ) ),
    inference(resolution,[status(thm)],[c_8,c_210])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_799,plain,(
    ! [C_177,A_178,B_179,B_180] :
      ( r1_tarski(k5_relat_1(C_177,A_178),k5_relat_1(B_179,B_180))
      | ~ r1_tarski(C_177,B_179)
      | ~ v1_relat_1(B_179)
      | ~ r1_tarski(A_178,B_180)
      | ~ v1_relat_1(C_177)
      | ~ v1_relat_1(B_180)
      | ~ v1_relat_1(A_178) ) ),
    inference(resolution,[status(thm)],[c_790,c_4])).

tff(c_12,plain,(
    ~ r1_tarski(k5_relat_1('#skF_2','#skF_4'),k5_relat_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_833,plain,
    ( ~ r1_tarski('#skF_2','#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ r1_tarski('#skF_4','#skF_5')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_799,c_12])).

tff(c_854,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_24,c_14,c_22,c_16,c_833])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:37:09 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.56/1.64  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.65  
% 3.56/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.65  %$ r2_hidden > r1_tarski > v1_relat_1 > k5_relat_1 > #nlpp > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.56/1.65  
% 3.56/1.65  %Foreground sorts:
% 3.56/1.65  
% 3.56/1.65  
% 3.56/1.65  %Background operators:
% 3.56/1.65  
% 3.56/1.65  
% 3.56/1.65  %Foreground operators:
% 3.56/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.56/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.56/1.65  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.56/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.56/1.65  tff('#skF_5', type, '#skF_5': $i).
% 3.56/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.56/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.56/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.56/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.56/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.56/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.56/1.65  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.56/1.65  
% 3.94/1.66  tff(f_74, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k5_relat_1(A, C), k5_relat_1(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_relat_1)).
% 3.94/1.66  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relat_1)).
% 3.94/1.66  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(A, C), k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relat_1)).
% 3.94/1.66  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.94/1.66  tff(c_20, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.94/1.66  tff(c_18, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.94/1.66  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.94/1.66  tff(c_14, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.94/1.66  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.94/1.66  tff(c_16, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.94/1.66  tff(c_8, plain, (![C_12, A_6, B_10]: (r1_tarski(k5_relat_1(C_12, A_6), k5_relat_1(C_12, B_10)) | ~r1_tarski(A_6, B_10) | ~v1_relat_1(C_12) | ~v1_relat_1(B_10) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.94/1.66  tff(c_142, plain, (![A_68, C_69, B_70]: (r1_tarski(k5_relat_1(A_68, C_69), k5_relat_1(B_70, C_69)) | ~r1_tarski(A_68, B_70) | ~v1_relat_1(C_69) | ~v1_relat_1(B_70) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.94/1.66  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.94/1.66  tff(c_32, plain, (![C_35, B_36, A_37]: (r2_hidden(C_35, B_36) | ~r2_hidden(C_35, A_37) | ~r1_tarski(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.94/1.66  tff(c_37, plain, (![A_39, B_40, B_41]: (r2_hidden('#skF_1'(A_39, B_40), B_41) | ~r1_tarski(A_39, B_41) | r1_tarski(A_39, B_40))), inference(resolution, [status(thm)], [c_6, c_32])).
% 3.94/1.66  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.94/1.66  tff(c_44, plain, (![A_39, B_40, B_2, B_41]: (r2_hidden('#skF_1'(A_39, B_40), B_2) | ~r1_tarski(B_41, B_2) | ~r1_tarski(A_39, B_41) | r1_tarski(A_39, B_40))), inference(resolution, [status(thm)], [c_37, c_2])).
% 3.94/1.66  tff(c_210, plain, (![A_85, B_87, A_89, C_88, B_86]: (r2_hidden('#skF_1'(A_85, B_86), k5_relat_1(B_87, C_88)) | ~r1_tarski(A_85, k5_relat_1(A_89, C_88)) | r1_tarski(A_85, B_86) | ~r1_tarski(A_89, B_87) | ~v1_relat_1(C_88) | ~v1_relat_1(B_87) | ~v1_relat_1(A_89))), inference(resolution, [status(thm)], [c_142, c_44])).
% 3.94/1.66  tff(c_790, plain, (![C_176, B_172, B_174, A_175, B_173]: (r2_hidden('#skF_1'(k5_relat_1(C_176, A_175), B_172), k5_relat_1(B_173, B_174)) | r1_tarski(k5_relat_1(C_176, A_175), B_172) | ~r1_tarski(C_176, B_173) | ~v1_relat_1(B_173) | ~r1_tarski(A_175, B_174) | ~v1_relat_1(C_176) | ~v1_relat_1(B_174) | ~v1_relat_1(A_175))), inference(resolution, [status(thm)], [c_8, c_210])).
% 3.94/1.66  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.94/1.66  tff(c_799, plain, (![C_177, A_178, B_179, B_180]: (r1_tarski(k5_relat_1(C_177, A_178), k5_relat_1(B_179, B_180)) | ~r1_tarski(C_177, B_179) | ~v1_relat_1(B_179) | ~r1_tarski(A_178, B_180) | ~v1_relat_1(C_177) | ~v1_relat_1(B_180) | ~v1_relat_1(A_178))), inference(resolution, [status(thm)], [c_790, c_4])).
% 3.94/1.66  tff(c_12, plain, (~r1_tarski(k5_relat_1('#skF_2', '#skF_4'), k5_relat_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.94/1.66  tff(c_833, plain, (~r1_tarski('#skF_2', '#skF_3') | ~v1_relat_1('#skF_3') | ~r1_tarski('#skF_4', '#skF_5') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_799, c_12])).
% 3.94/1.66  tff(c_854, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_24, c_14, c_22, c_16, c_833])).
% 3.94/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.94/1.66  
% 3.94/1.66  Inference rules
% 3.94/1.66  ----------------------
% 3.94/1.66  #Ref     : 0
% 3.94/1.66  #Sup     : 206
% 3.94/1.66  #Fact    : 0
% 3.94/1.66  #Define  : 0
% 3.94/1.66  #Split   : 5
% 3.94/1.66  #Chain   : 0
% 3.94/1.66  #Close   : 0
% 3.94/1.66  
% 3.94/1.66  Ordering : KBO
% 3.94/1.66  
% 3.94/1.66  Simplification rules
% 3.94/1.66  ----------------------
% 3.94/1.66  #Subsume      : 40
% 3.94/1.66  #Demod        : 58
% 3.94/1.66  #Tautology    : 2
% 3.94/1.66  #SimpNegUnit  : 0
% 3.94/1.66  #BackRed      : 0
% 3.94/1.66  
% 3.94/1.66  #Partial instantiations: 0
% 3.94/1.66  #Strategies tried      : 1
% 3.94/1.66  
% 3.94/1.66  Timing (in seconds)
% 3.94/1.66  ----------------------
% 3.94/1.66  Preprocessing        : 0.28
% 3.94/1.67  Parsing              : 0.15
% 3.94/1.67  CNF conversion       : 0.02
% 3.94/1.67  Main loop            : 0.62
% 3.94/1.67  Inferencing          : 0.20
% 3.94/1.67  Reduction            : 0.14
% 3.94/1.67  Demodulation         : 0.09
% 3.94/1.67  BG Simplification    : 0.02
% 3.94/1.67  Subsumption          : 0.23
% 3.94/1.67  Abstraction          : 0.03
% 3.94/1.67  MUC search           : 0.00
% 3.94/1.67  Cooper               : 0.00
% 3.94/1.67  Total                : 0.93
% 3.94/1.67  Index Insertion      : 0.00
% 3.94/1.67  Index Deletion       : 0.00
% 3.94/1.67  Index Matching       : 0.00
% 3.94/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
