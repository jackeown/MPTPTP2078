%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:36 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   29 (  31 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  41 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => r1_tarski(k1_wellord1(B,A),k3_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_wellord1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k1_wellord1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( D != B
                & r2_hidden(k4_tarski(D,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_48,plain,(
    ! [D_37,B_38,A_39] :
      ( r2_hidden(k4_tarski(D_37,B_38),A_39)
      | ~ r2_hidden(D_37,k1_wellord1(A_39,B_38))
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    ! [A_6,C_8,B_7] :
      ( r2_hidden(A_6,k3_relat_1(C_8))
      | ~ r2_hidden(k4_tarski(A_6,B_7),C_8)
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_79,plain,(
    ! [D_43,A_44,B_45] :
      ( r2_hidden(D_43,k3_relat_1(A_44))
      | ~ r2_hidden(D_43,k1_wellord1(A_44,B_45))
      | ~ v1_relat_1(A_44) ) ),
    inference(resolution,[status(thm)],[c_48,c_10])).

tff(c_216,plain,(
    ! [A_81,B_82,B_83] :
      ( r2_hidden('#skF_1'(k1_wellord1(A_81,B_82),B_83),k3_relat_1(A_81))
      | ~ v1_relat_1(A_81)
      | r1_tarski(k1_wellord1(A_81,B_82),B_83) ) ),
    inference(resolution,[status(thm)],[c_6,c_79])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_231,plain,(
    ! [A_87,B_88] :
      ( ~ v1_relat_1(A_87)
      | r1_tarski(k1_wellord1(A_87,B_88),k3_relat_1(A_87)) ) ),
    inference(resolution,[status(thm)],[c_216,c_4])).

tff(c_30,plain,(
    ~ r1_tarski(k1_wellord1('#skF_5','#skF_4'),k3_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_238,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_231,c_30])).

tff(c_244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_238])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:49:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.22  
% 1.87/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.23  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.87/1.23  
% 1.87/1.23  %Foreground sorts:
% 1.87/1.23  
% 1.87/1.23  
% 1.87/1.23  %Background operators:
% 1.87/1.23  
% 1.87/1.23  
% 1.87/1.23  %Foreground operators:
% 1.87/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.23  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.87/1.23  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.87/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.23  tff('#skF_5', type, '#skF_5': $i).
% 1.87/1.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.87/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.87/1.23  tff('#skF_4', type, '#skF_4': $i).
% 1.87/1.23  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 1.87/1.23  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.87/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.87/1.23  
% 2.13/1.23  tff(f_58, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => r1_tarski(k1_wellord1(B, A), k3_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_wellord1)).
% 2.13/1.23  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.13/1.23  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k1_wellord1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (~(D = B) & r2_hidden(k4_tarski(D, B), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord1)).
% 2.13/1.23  tff(f_40, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relat_1)).
% 2.13/1.23  tff(c_32, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.13/1.23  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.13/1.23  tff(c_48, plain, (![D_37, B_38, A_39]: (r2_hidden(k4_tarski(D_37, B_38), A_39) | ~r2_hidden(D_37, k1_wellord1(A_39, B_38)) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.13/1.23  tff(c_10, plain, (![A_6, C_8, B_7]: (r2_hidden(A_6, k3_relat_1(C_8)) | ~r2_hidden(k4_tarski(A_6, B_7), C_8) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.13/1.23  tff(c_79, plain, (![D_43, A_44, B_45]: (r2_hidden(D_43, k3_relat_1(A_44)) | ~r2_hidden(D_43, k1_wellord1(A_44, B_45)) | ~v1_relat_1(A_44))), inference(resolution, [status(thm)], [c_48, c_10])).
% 2.13/1.23  tff(c_216, plain, (![A_81, B_82, B_83]: (r2_hidden('#skF_1'(k1_wellord1(A_81, B_82), B_83), k3_relat_1(A_81)) | ~v1_relat_1(A_81) | r1_tarski(k1_wellord1(A_81, B_82), B_83))), inference(resolution, [status(thm)], [c_6, c_79])).
% 2.13/1.23  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.13/1.23  tff(c_231, plain, (![A_87, B_88]: (~v1_relat_1(A_87) | r1_tarski(k1_wellord1(A_87, B_88), k3_relat_1(A_87)))), inference(resolution, [status(thm)], [c_216, c_4])).
% 2.13/1.23  tff(c_30, plain, (~r1_tarski(k1_wellord1('#skF_5', '#skF_4'), k3_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.13/1.23  tff(c_238, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_231, c_30])).
% 2.13/1.23  tff(c_244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_238])).
% 2.13/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.23  
% 2.13/1.23  Inference rules
% 2.13/1.23  ----------------------
% 2.13/1.23  #Ref     : 0
% 2.13/1.23  #Sup     : 45
% 2.13/1.23  #Fact    : 0
% 2.13/1.23  #Define  : 0
% 2.13/1.23  #Split   : 0
% 2.13/1.23  #Chain   : 0
% 2.13/1.23  #Close   : 0
% 2.13/1.23  
% 2.13/1.24  Ordering : KBO
% 2.13/1.24  
% 2.13/1.24  Simplification rules
% 2.13/1.24  ----------------------
% 2.13/1.24  #Subsume      : 8
% 2.13/1.24  #Demod        : 3
% 2.13/1.24  #Tautology    : 3
% 2.13/1.24  #SimpNegUnit  : 0
% 2.13/1.24  #BackRed      : 0
% 2.13/1.24  
% 2.13/1.24  #Partial instantiations: 0
% 2.13/1.24  #Strategies tried      : 1
% 2.13/1.24  
% 2.13/1.24  Timing (in seconds)
% 2.13/1.24  ----------------------
% 2.13/1.24  Preprocessing        : 0.27
% 2.13/1.24  Parsing              : 0.14
% 2.13/1.24  CNF conversion       : 0.02
% 2.13/1.24  Main loop            : 0.23
% 2.13/1.24  Inferencing          : 0.09
% 2.13/1.24  Reduction            : 0.06
% 2.13/1.24  Demodulation         : 0.04
% 2.13/1.24  BG Simplification    : 0.02
% 2.13/1.24  Subsumption          : 0.06
% 2.13/1.24  Abstraction          : 0.01
% 2.13/1.24  MUC search           : 0.00
% 2.13/1.24  Cooper               : 0.00
% 2.13/1.24  Total                : 0.52
% 2.13/1.24  Index Insertion      : 0.00
% 2.13/1.24  Index Deletion       : 0.00
% 2.13/1.24  Index Matching       : 0.00
% 2.13/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
