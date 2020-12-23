%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:28 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   33 (  37 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   41 (  51 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_xboole_0(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_20,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_22,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_25,plain,(
    ! [A_20,B_21,C_22] :
      ( ~ r1_xboole_0(A_20,B_21)
      | ~ r2_hidden(C_22,k3_xboole_0(A_20,B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_34,plain,(
    ! [A_20,B_21,A_1] :
      ( ~ r1_xboole_0(A_20,B_21)
      | r1_xboole_0(A_1,k3_xboole_0(A_20,B_21)) ) ),
    inference(resolution,[status(thm)],[c_4,c_25])).

tff(c_75,plain,(
    ! [B_35,A_36] :
      ( k7_relat_1(B_35,A_36) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_35),A_36)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_80,plain,(
    ! [B_35,A_20,B_21] :
      ( k7_relat_1(B_35,k3_xboole_0(A_20,B_21)) = k1_xboole_0
      | ~ v1_relat_1(B_35)
      | ~ r1_xboole_0(A_20,B_21) ) ),
    inference(resolution,[status(thm)],[c_34,c_75])).

tff(c_103,plain,(
    ! [C_44,A_45,B_46] :
      ( k7_relat_1(k7_relat_1(C_44,A_45),B_46) = k7_relat_1(C_44,k3_xboole_0(A_45,B_46))
      | ~ v1_relat_1(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    k7_relat_1(k7_relat_1('#skF_5','#skF_3'),'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_116,plain,
    ( k7_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_18])).

tff(c_132,plain,(
    k7_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_116])).

tff(c_136,plain,
    ( ~ v1_relat_1('#skF_5')
    | ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_132])).

tff(c_140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22,c_136])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:48:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.17  
% 1.82/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.17  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.82/1.17  
% 1.82/1.17  %Foreground sorts:
% 1.82/1.17  
% 1.82/1.17  
% 1.82/1.17  %Background operators:
% 1.82/1.17  
% 1.82/1.17  
% 1.82/1.17  %Foreground operators:
% 1.82/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.82/1.17  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.82/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.82/1.17  tff('#skF_5', type, '#skF_5': $i).
% 1.82/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.82/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.82/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.82/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.82/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.82/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.82/1.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.82/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.82/1.17  
% 1.82/1.18  tff(f_74, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 1.82/1.18  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.82/1.18  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.82/1.18  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 1.82/1.18  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 1.82/1.18  tff(c_20, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.82/1.18  tff(c_22, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.82/1.18  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.82/1.18  tff(c_25, plain, (![A_20, B_21, C_22]: (~r1_xboole_0(A_20, B_21) | ~r2_hidden(C_22, k3_xboole_0(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.82/1.18  tff(c_34, plain, (![A_20, B_21, A_1]: (~r1_xboole_0(A_20, B_21) | r1_xboole_0(A_1, k3_xboole_0(A_20, B_21)))), inference(resolution, [status(thm)], [c_4, c_25])).
% 1.82/1.18  tff(c_75, plain, (![B_35, A_36]: (k7_relat_1(B_35, A_36)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_35), A_36) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.82/1.18  tff(c_80, plain, (![B_35, A_20, B_21]: (k7_relat_1(B_35, k3_xboole_0(A_20, B_21))=k1_xboole_0 | ~v1_relat_1(B_35) | ~r1_xboole_0(A_20, B_21))), inference(resolution, [status(thm)], [c_34, c_75])).
% 1.82/1.18  tff(c_103, plain, (![C_44, A_45, B_46]: (k7_relat_1(k7_relat_1(C_44, A_45), B_46)=k7_relat_1(C_44, k3_xboole_0(A_45, B_46)) | ~v1_relat_1(C_44))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.82/1.18  tff(c_18, plain, (k7_relat_1(k7_relat_1('#skF_5', '#skF_3'), '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.82/1.18  tff(c_116, plain, (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_103, c_18])).
% 1.82/1.18  tff(c_132, plain, (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_22, c_116])).
% 1.82/1.18  tff(c_136, plain, (~v1_relat_1('#skF_5') | ~r1_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_80, c_132])).
% 1.82/1.18  tff(c_140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_22, c_136])).
% 1.82/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.18  
% 1.82/1.18  Inference rules
% 1.82/1.18  ----------------------
% 1.82/1.18  #Ref     : 0
% 1.82/1.18  #Sup     : 25
% 1.82/1.18  #Fact    : 0
% 1.82/1.18  #Define  : 0
% 1.82/1.18  #Split   : 0
% 1.82/1.18  #Chain   : 0
% 1.82/1.18  #Close   : 0
% 1.82/1.18  
% 1.82/1.18  Ordering : KBO
% 1.82/1.18  
% 1.82/1.18  Simplification rules
% 1.82/1.18  ----------------------
% 1.82/1.18  #Subsume      : 3
% 1.82/1.18  #Demod        : 4
% 1.82/1.18  #Tautology    : 7
% 1.82/1.18  #SimpNegUnit  : 0
% 1.82/1.18  #BackRed      : 0
% 1.82/1.18  
% 1.82/1.18  #Partial instantiations: 0
% 1.82/1.18  #Strategies tried      : 1
% 1.82/1.18  
% 1.82/1.18  Timing (in seconds)
% 1.82/1.18  ----------------------
% 1.82/1.18  Preprocessing        : 0.27
% 1.82/1.18  Parsing              : 0.15
% 1.82/1.18  CNF conversion       : 0.02
% 1.91/1.18  Main loop            : 0.15
% 1.91/1.18  Inferencing          : 0.07
% 1.91/1.18  Reduction            : 0.03
% 1.91/1.18  Demodulation         : 0.03
% 1.91/1.18  BG Simplification    : 0.01
% 1.91/1.18  Subsumption          : 0.03
% 1.91/1.18  Abstraction          : 0.01
% 1.91/1.18  MUC search           : 0.00
% 1.91/1.18  Cooper               : 0.00
% 1.91/1.18  Total                : 0.44
% 1.91/1.18  Index Insertion      : 0.00
% 1.91/1.18  Index Deletion       : 0.00
% 1.91/1.18  Index Matching       : 0.00
% 1.91/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
