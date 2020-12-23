%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:40 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   36 (  42 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  71 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v5_relat_1(B,A)
          & v1_funct_1(B) )
       => ! [C] :
            ( r2_hidden(C,k1_relat_1(B))
           => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_38,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_36,plain,(
    v5_relat_1('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_34,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_32,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_82,plain,(
    ! [A_66,D_67] :
      ( r2_hidden(k1_funct_1(A_66,D_67),k2_relat_1(A_66))
      | ~ r2_hidden(D_67,k1_relat_1(A_66))
      | ~ v1_funct_1(A_66)
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_117,plain,(
    ! [A_80,D_81,B_82] :
      ( r2_hidden(k1_funct_1(A_80,D_81),B_82)
      | ~ r1_tarski(k2_relat_1(A_80),B_82)
      | ~ r2_hidden(D_81,k1_relat_1(A_80))
      | ~ v1_funct_1(A_80)
      | ~ v1_relat_1(A_80) ) ),
    inference(resolution,[status(thm)],[c_82,c_2])).

tff(c_30,plain,(
    ~ r2_hidden(k1_funct_1('#skF_7','#skF_8'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_122,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_7'),'#skF_6')
    | ~ r2_hidden('#skF_8',k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_117,c_30])).

tff(c_129,plain,(
    ~ r1_tarski(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_32,c_122])).

tff(c_132,plain,
    ( ~ v5_relat_1('#skF_7','#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_10,c_129])).

tff(c_136,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_132])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:42:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.22  
% 1.94/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.22  %$ v5_relat_1 > r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 1.94/1.22  
% 1.94/1.22  %Foreground sorts:
% 1.94/1.22  
% 1.94/1.22  
% 1.94/1.22  %Background operators:
% 1.94/1.22  
% 1.94/1.22  
% 1.94/1.22  %Foreground operators:
% 1.94/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.94/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.94/1.22  tff('#skF_7', type, '#skF_7': $i).
% 1.94/1.22  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.94/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.94/1.22  tff('#skF_6', type, '#skF_6': $i).
% 1.94/1.22  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 1.94/1.22  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.94/1.22  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.94/1.22  tff('#skF_8', type, '#skF_8': $i).
% 1.94/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.94/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.94/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.94/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.94/1.22  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.94/1.22  
% 1.94/1.23  tff(f_65, negated_conjecture, ~(![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 1.94/1.23  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 1.94/1.23  tff(f_53, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 1.94/1.23  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.94/1.23  tff(c_38, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.94/1.23  tff(c_36, plain, (v5_relat_1('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.94/1.23  tff(c_10, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.94/1.23  tff(c_34, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.94/1.23  tff(c_32, plain, (r2_hidden('#skF_8', k1_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.94/1.23  tff(c_82, plain, (![A_66, D_67]: (r2_hidden(k1_funct_1(A_66, D_67), k2_relat_1(A_66)) | ~r2_hidden(D_67, k1_relat_1(A_66)) | ~v1_funct_1(A_66) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.94/1.23  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.94/1.23  tff(c_117, plain, (![A_80, D_81, B_82]: (r2_hidden(k1_funct_1(A_80, D_81), B_82) | ~r1_tarski(k2_relat_1(A_80), B_82) | ~r2_hidden(D_81, k1_relat_1(A_80)) | ~v1_funct_1(A_80) | ~v1_relat_1(A_80))), inference(resolution, [status(thm)], [c_82, c_2])).
% 1.94/1.23  tff(c_30, plain, (~r2_hidden(k1_funct_1('#skF_7', '#skF_8'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.94/1.23  tff(c_122, plain, (~r1_tarski(k2_relat_1('#skF_7'), '#skF_6') | ~r2_hidden('#skF_8', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_117, c_30])).
% 1.94/1.23  tff(c_129, plain, (~r1_tarski(k2_relat_1('#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_32, c_122])).
% 1.94/1.23  tff(c_132, plain, (~v5_relat_1('#skF_7', '#skF_6') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_10, c_129])).
% 1.94/1.23  tff(c_136, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_132])).
% 1.94/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.23  
% 1.94/1.23  Inference rules
% 1.94/1.23  ----------------------
% 1.94/1.23  #Ref     : 0
% 1.94/1.23  #Sup     : 21
% 1.94/1.23  #Fact    : 0
% 1.94/1.23  #Define  : 0
% 1.94/1.23  #Split   : 0
% 1.94/1.23  #Chain   : 0
% 1.94/1.23  #Close   : 0
% 1.94/1.23  
% 1.94/1.23  Ordering : KBO
% 1.94/1.23  
% 1.94/1.23  Simplification rules
% 1.94/1.23  ----------------------
% 1.94/1.23  #Subsume      : 2
% 1.94/1.23  #Demod        : 6
% 1.94/1.23  #Tautology    : 6
% 1.94/1.23  #SimpNegUnit  : 0
% 1.94/1.23  #BackRed      : 0
% 1.94/1.23  
% 1.94/1.23  #Partial instantiations: 0
% 1.94/1.23  #Strategies tried      : 1
% 1.94/1.23  
% 1.94/1.23  Timing (in seconds)
% 1.94/1.23  ----------------------
% 1.94/1.23  Preprocessing        : 0.30
% 1.94/1.23  Parsing              : 0.16
% 1.94/1.23  CNF conversion       : 0.03
% 1.94/1.23  Main loop            : 0.17
% 1.94/1.23  Inferencing          : 0.07
% 1.94/1.23  Reduction            : 0.04
% 1.94/1.23  Demodulation         : 0.03
% 1.94/1.23  BG Simplification    : 0.02
% 1.94/1.23  Subsumption          : 0.03
% 1.94/1.23  Abstraction          : 0.01
% 1.94/1.23  MUC search           : 0.00
% 1.94/1.23  Cooper               : 0.00
% 1.94/1.23  Total                : 0.49
% 1.94/1.23  Index Insertion      : 0.00
% 1.94/1.23  Index Deletion       : 0.00
% 1.94/1.23  Index Matching       : 0.00
% 1.94/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
