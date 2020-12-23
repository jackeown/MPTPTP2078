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
% DateTime   : Thu Dec  3 10:02:26 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   37 (  42 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   46 (  62 expanded)
%              Number of equality atoms :   15 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_xboole_0(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_59,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_24,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_33,plain,(
    ! [A_15,B_16] :
      ( k3_xboole_0(A_15,B_16) = k1_xboole_0
      | ~ r1_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_41,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_33])).

tff(c_216,plain,(
    ! [C_39,A_40,B_41] :
      ( k7_relat_1(k7_relat_1(C_39,A_40),B_41) = k7_relat_1(C_39,k3_xboole_0(A_40,B_41))
      | ~ v1_relat_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_22,plain,(
    k7_relat_1(k7_relat_1('#skF_4','#skF_2'),'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_225,plain,
    ( k7_relat_1('#skF_4',k3_xboole_0('#skF_2','#skF_3')) != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_22])).

tff(c_234,plain,(
    k7_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_41,c_225])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_68,plain,(
    ! [A_24,B_25,C_26] :
      ( ~ r1_xboole_0(A_24,B_25)
      | ~ r2_hidden(C_26,B_25)
      | ~ r2_hidden(C_26,A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_78,plain,(
    ! [C_27] : ~ r2_hidden(C_27,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_68])).

tff(c_88,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_78])).

tff(c_201,plain,(
    ! [B_37,A_38] :
      ( k7_relat_1(B_37,A_38) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_37),A_38)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_236,plain,(
    ! [B_42] :
      ( k7_relat_1(B_42,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_42) ) ),
    inference(resolution,[status(thm)],[c_88,c_201])).

tff(c_239,plain,(
    k7_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_236])).

tff(c_243,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_234,c_239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:09:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.30  
% 2.00/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.30  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.00/1.30  
% 2.00/1.30  %Foreground sorts:
% 2.00/1.30  
% 2.00/1.30  
% 2.00/1.30  %Background operators:
% 2.00/1.30  
% 2.00/1.30  
% 2.00/1.30  %Foreground operators:
% 2.00/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.00/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.00/1.30  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.00/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.00/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.00/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.00/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.00/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.00/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.00/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.00/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.00/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.00/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.00/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.00/1.30  
% 2.00/1.31  tff(f_76, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 2.00/1.31  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.00/1.31  tff(f_63, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 2.00/1.31  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.00/1.31  tff(f_59, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.00/1.31  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 2.00/1.31  tff(c_26, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.00/1.31  tff(c_24, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.00/1.31  tff(c_33, plain, (![A_15, B_16]: (k3_xboole_0(A_15, B_16)=k1_xboole_0 | ~r1_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.00/1.31  tff(c_41, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_33])).
% 2.00/1.31  tff(c_216, plain, (![C_39, A_40, B_41]: (k7_relat_1(k7_relat_1(C_39, A_40), B_41)=k7_relat_1(C_39, k3_xboole_0(A_40, B_41)) | ~v1_relat_1(C_39))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.00/1.31  tff(c_22, plain, (k7_relat_1(k7_relat_1('#skF_4', '#skF_2'), '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.00/1.31  tff(c_225, plain, (k7_relat_1('#skF_4', k3_xboole_0('#skF_2', '#skF_3'))!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_216, c_22])).
% 2.00/1.31  tff(c_234, plain, (k7_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_41, c_225])).
% 2.00/1.31  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.00/1.31  tff(c_12, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.00/1.31  tff(c_68, plain, (![A_24, B_25, C_26]: (~r1_xboole_0(A_24, B_25) | ~r2_hidden(C_26, B_25) | ~r2_hidden(C_26, A_24))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.00/1.31  tff(c_78, plain, (![C_27]: (~r2_hidden(C_27, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_68])).
% 2.00/1.31  tff(c_88, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_78])).
% 2.00/1.31  tff(c_201, plain, (![B_37, A_38]: (k7_relat_1(B_37, A_38)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_37), A_38) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.00/1.31  tff(c_236, plain, (![B_42]: (k7_relat_1(B_42, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_42))), inference(resolution, [status(thm)], [c_88, c_201])).
% 2.00/1.31  tff(c_239, plain, (k7_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_236])).
% 2.00/1.31  tff(c_243, plain, $false, inference(negUnitSimplification, [status(thm)], [c_234, c_239])).
% 2.00/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.31  
% 2.00/1.31  Inference rules
% 2.00/1.31  ----------------------
% 2.00/1.31  #Ref     : 0
% 2.00/1.31  #Sup     : 49
% 2.00/1.31  #Fact    : 0
% 2.00/1.31  #Define  : 0
% 2.00/1.31  #Split   : 0
% 2.00/1.31  #Chain   : 0
% 2.00/1.31  #Close   : 0
% 2.00/1.31  
% 2.00/1.31  Ordering : KBO
% 2.00/1.31  
% 2.00/1.31  Simplification rules
% 2.00/1.31  ----------------------
% 2.00/1.31  #Subsume      : 3
% 2.00/1.31  #Demod        : 5
% 2.00/1.31  #Tautology    : 25
% 2.00/1.31  #SimpNegUnit  : 1
% 2.00/1.31  #BackRed      : 0
% 2.00/1.31  
% 2.00/1.31  #Partial instantiations: 0
% 2.00/1.31  #Strategies tried      : 1
% 2.00/1.31  
% 2.00/1.31  Timing (in seconds)
% 2.00/1.31  ----------------------
% 2.00/1.31  Preprocessing        : 0.31
% 2.00/1.31  Parsing              : 0.17
% 2.00/1.31  CNF conversion       : 0.02
% 2.00/1.31  Main loop            : 0.19
% 2.00/1.31  Inferencing          : 0.08
% 2.00/1.31  Reduction            : 0.05
% 2.00/1.31  Demodulation         : 0.04
% 2.00/1.31  BG Simplification    : 0.01
% 2.00/1.31  Subsumption          : 0.04
% 2.00/1.31  Abstraction          : 0.01
% 2.00/1.31  MUC search           : 0.00
% 2.00/1.31  Cooper               : 0.00
% 2.00/1.31  Total                : 0.52
% 2.00/1.31  Index Insertion      : 0.00
% 2.00/1.31  Index Deletion       : 0.00
% 2.00/1.31  Index Matching       : 0.00
% 2.00/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
