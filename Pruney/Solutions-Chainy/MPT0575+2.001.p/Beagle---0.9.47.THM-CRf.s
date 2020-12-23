%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:54 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :   37 (  44 expanded)
%              Number of leaves         :   19 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   57 (  85 expanded)
%              Number of equality atoms :    1 (   3 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_5 > #skF_3 > #skF_1

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_55,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => ( r1_tarski(B,C)
             => r1_tarski(k10_relat_1(B,A),k10_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t179_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_32,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_30,plain,(
    v1_relat_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_140,plain,(
    ! [D_97,A_98,B_99] :
      ( r2_hidden(k4_tarski(D_97,'#skF_5'(A_98,B_99,k10_relat_1(A_98,B_99),D_97)),A_98)
      | ~ r2_hidden(D_97,k10_relat_1(A_98,B_99))
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_146,plain,(
    ! [D_97,A_98,B_99,B_2] :
      ( r2_hidden(k4_tarski(D_97,'#skF_5'(A_98,B_99,k10_relat_1(A_98,B_99),D_97)),B_2)
      | ~ r1_tarski(A_98,B_2)
      | ~ r2_hidden(D_97,k10_relat_1(A_98,B_99))
      | ~ v1_relat_1(A_98) ) ),
    inference(resolution,[status(thm)],[c_140,c_2])).

tff(c_104,plain,(
    ! [A_76,B_77,D_78] :
      ( r2_hidden('#skF_5'(A_76,B_77,k10_relat_1(A_76,B_77),D_78),B_77)
      | ~ r2_hidden(D_78,k10_relat_1(A_76,B_77))
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [D_44,A_6,B_29,E_47] :
      ( r2_hidden(D_44,k10_relat_1(A_6,B_29))
      | ~ r2_hidden(E_47,B_29)
      | ~ r2_hidden(k4_tarski(D_44,E_47),A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_317,plain,(
    ! [D_192,A_194,A_193,B_190,D_191] :
      ( r2_hidden(D_191,k10_relat_1(A_193,B_190))
      | ~ r2_hidden(k4_tarski(D_191,'#skF_5'(A_194,B_190,k10_relat_1(A_194,B_190),D_192)),A_193)
      | ~ v1_relat_1(A_193)
      | ~ r2_hidden(D_192,k10_relat_1(A_194,B_190))
      | ~ v1_relat_1(A_194) ) ),
    inference(resolution,[status(thm)],[c_104,c_8])).

tff(c_417,plain,(
    ! [D_198,B_199,B_200,A_201] :
      ( r2_hidden(D_198,k10_relat_1(B_199,B_200))
      | ~ v1_relat_1(B_199)
      | ~ r1_tarski(A_201,B_199)
      | ~ r2_hidden(D_198,k10_relat_1(A_201,B_200))
      | ~ v1_relat_1(A_201) ) ),
    inference(resolution,[status(thm)],[c_146,c_317])).

tff(c_421,plain,(
    ! [D_198,B_200] :
      ( r2_hidden(D_198,k10_relat_1('#skF_8',B_200))
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_198,k10_relat_1('#skF_7',B_200))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_28,c_417])).

tff(c_426,plain,(
    ! [D_202,B_203] :
      ( r2_hidden(D_202,k10_relat_1('#skF_8',B_203))
      | ~ r2_hidden(D_202,k10_relat_1('#skF_7',B_203)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_421])).

tff(c_560,plain,(
    ! [B_208,B_209] :
      ( r2_hidden('#skF_1'(k10_relat_1('#skF_7',B_208),B_209),k10_relat_1('#skF_8',B_208))
      | r1_tarski(k10_relat_1('#skF_7',B_208),B_209) ) ),
    inference(resolution,[status(thm)],[c_6,c_426])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_576,plain,(
    ! [B_208] : r1_tarski(k10_relat_1('#skF_7',B_208),k10_relat_1('#skF_8',B_208)) ),
    inference(resolution,[status(thm)],[c_560,c_4])).

tff(c_26,plain,(
    ~ r1_tarski(k10_relat_1('#skF_7','#skF_6'),k10_relat_1('#skF_8','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_579,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_576,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:31:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.04/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.48  
% 3.04/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.48  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_5 > #skF_3 > #skF_1
% 3.04/1.48  
% 3.04/1.48  %Foreground sorts:
% 3.04/1.48  
% 3.04/1.48  
% 3.04/1.48  %Background operators:
% 3.04/1.48  
% 3.04/1.48  
% 3.04/1.48  %Foreground operators:
% 3.04/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.04/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.04/1.48  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.04/1.48  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.04/1.48  tff('#skF_7', type, '#skF_7': $i).
% 3.04/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.04/1.48  tff('#skF_6', type, '#skF_6': $i).
% 3.04/1.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.04/1.48  tff('#skF_8', type, '#skF_8': $i).
% 3.04/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.04/1.48  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.04/1.48  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 3.04/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.04/1.48  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.04/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.04/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.04/1.48  
% 3.04/1.49  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.04/1.49  tff(f_55, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k10_relat_1(B, A), k10_relat_1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t179_relat_1)).
% 3.04/1.49  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 3.04/1.49  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.04/1.49  tff(c_32, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.04/1.49  tff(c_30, plain, (v1_relat_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.04/1.49  tff(c_28, plain, (r1_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.04/1.49  tff(c_140, plain, (![D_97, A_98, B_99]: (r2_hidden(k4_tarski(D_97, '#skF_5'(A_98, B_99, k10_relat_1(A_98, B_99), D_97)), A_98) | ~r2_hidden(D_97, k10_relat_1(A_98, B_99)) | ~v1_relat_1(A_98))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.04/1.49  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.04/1.49  tff(c_146, plain, (![D_97, A_98, B_99, B_2]: (r2_hidden(k4_tarski(D_97, '#skF_5'(A_98, B_99, k10_relat_1(A_98, B_99), D_97)), B_2) | ~r1_tarski(A_98, B_2) | ~r2_hidden(D_97, k10_relat_1(A_98, B_99)) | ~v1_relat_1(A_98))), inference(resolution, [status(thm)], [c_140, c_2])).
% 3.04/1.49  tff(c_104, plain, (![A_76, B_77, D_78]: (r2_hidden('#skF_5'(A_76, B_77, k10_relat_1(A_76, B_77), D_78), B_77) | ~r2_hidden(D_78, k10_relat_1(A_76, B_77)) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.04/1.49  tff(c_8, plain, (![D_44, A_6, B_29, E_47]: (r2_hidden(D_44, k10_relat_1(A_6, B_29)) | ~r2_hidden(E_47, B_29) | ~r2_hidden(k4_tarski(D_44, E_47), A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.04/1.49  tff(c_317, plain, (![D_192, A_194, A_193, B_190, D_191]: (r2_hidden(D_191, k10_relat_1(A_193, B_190)) | ~r2_hidden(k4_tarski(D_191, '#skF_5'(A_194, B_190, k10_relat_1(A_194, B_190), D_192)), A_193) | ~v1_relat_1(A_193) | ~r2_hidden(D_192, k10_relat_1(A_194, B_190)) | ~v1_relat_1(A_194))), inference(resolution, [status(thm)], [c_104, c_8])).
% 3.04/1.49  tff(c_417, plain, (![D_198, B_199, B_200, A_201]: (r2_hidden(D_198, k10_relat_1(B_199, B_200)) | ~v1_relat_1(B_199) | ~r1_tarski(A_201, B_199) | ~r2_hidden(D_198, k10_relat_1(A_201, B_200)) | ~v1_relat_1(A_201))), inference(resolution, [status(thm)], [c_146, c_317])).
% 3.04/1.49  tff(c_421, plain, (![D_198, B_200]: (r2_hidden(D_198, k10_relat_1('#skF_8', B_200)) | ~v1_relat_1('#skF_8') | ~r2_hidden(D_198, k10_relat_1('#skF_7', B_200)) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_28, c_417])).
% 3.04/1.49  tff(c_426, plain, (![D_202, B_203]: (r2_hidden(D_202, k10_relat_1('#skF_8', B_203)) | ~r2_hidden(D_202, k10_relat_1('#skF_7', B_203)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_421])).
% 3.04/1.49  tff(c_560, plain, (![B_208, B_209]: (r2_hidden('#skF_1'(k10_relat_1('#skF_7', B_208), B_209), k10_relat_1('#skF_8', B_208)) | r1_tarski(k10_relat_1('#skF_7', B_208), B_209))), inference(resolution, [status(thm)], [c_6, c_426])).
% 3.04/1.49  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.04/1.49  tff(c_576, plain, (![B_208]: (r1_tarski(k10_relat_1('#skF_7', B_208), k10_relat_1('#skF_8', B_208)))), inference(resolution, [status(thm)], [c_560, c_4])).
% 3.04/1.49  tff(c_26, plain, (~r1_tarski(k10_relat_1('#skF_7', '#skF_6'), k10_relat_1('#skF_8', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.04/1.49  tff(c_579, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_576, c_26])).
% 3.04/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.49  
% 3.04/1.49  Inference rules
% 3.04/1.49  ----------------------
% 3.04/1.49  #Ref     : 0
% 3.04/1.49  #Sup     : 132
% 3.04/1.49  #Fact    : 0
% 3.04/1.49  #Define  : 0
% 3.04/1.49  #Split   : 0
% 3.04/1.49  #Chain   : 0
% 3.04/1.49  #Close   : 0
% 3.04/1.49  
% 3.04/1.49  Ordering : KBO
% 3.04/1.49  
% 3.04/1.49  Simplification rules
% 3.04/1.49  ----------------------
% 3.04/1.49  #Subsume      : 10
% 3.04/1.49  #Demod        : 8
% 3.04/1.49  #Tautology    : 4
% 3.04/1.49  #SimpNegUnit  : 0
% 3.04/1.49  #BackRed      : 1
% 3.04/1.49  
% 3.04/1.49  #Partial instantiations: 0
% 3.04/1.49  #Strategies tried      : 1
% 3.04/1.49  
% 3.04/1.49  Timing (in seconds)
% 3.04/1.49  ----------------------
% 3.04/1.49  Preprocessing        : 0.26
% 3.04/1.49  Parsing              : 0.13
% 3.04/1.49  CNF conversion       : 0.03
% 3.04/1.49  Main loop            : 0.40
% 3.04/1.49  Inferencing          : 0.16
% 3.04/1.49  Reduction            : 0.08
% 3.04/1.50  Demodulation         : 0.05
% 3.04/1.50  BG Simplification    : 0.02
% 3.04/1.50  Subsumption          : 0.11
% 3.04/1.50  Abstraction          : 0.02
% 3.04/1.50  MUC search           : 0.00
% 3.04/1.50  Cooper               : 0.00
% 3.04/1.50  Total                : 0.68
% 3.04/1.50  Index Insertion      : 0.00
% 3.04/1.50  Index Deletion       : 0.00
% 3.04/1.50  Index Matching       : 0.00
% 3.04/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
