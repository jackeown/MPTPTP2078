%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:59 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   30 (  33 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   31 (  41 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_55,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( r1_xboole_0(B,k1_relat_1(A))
           => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(c_12,plain,(
    k7_relat_1('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    r1_xboole_0('#skF_3',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),k3_xboole_0(A_3,B_4))
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_50,plain,(
    ! [A_13,B_14,C_15] :
      ( ~ r1_xboole_0(A_13,B_14)
      | ~ r2_hidden(C_15,k3_xboole_0(A_13,B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_68,plain,(
    ! [A_18,B_19,C_20] :
      ( ~ r1_xboole_0(A_18,B_19)
      | ~ r2_hidden(C_20,k3_xboole_0(B_19,A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_50])).

tff(c_79,plain,(
    ! [B_21,A_22] :
      ( ~ r1_xboole_0(B_21,A_22)
      | r1_xboole_0(A_22,B_21) ) ),
    inference(resolution,[status(thm)],[c_4,c_68])).

tff(c_82,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_79])).

tff(c_87,plain,(
    ! [B_23,A_24] :
      ( k7_relat_1(B_23,A_24) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_23),A_24)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_90,plain,
    ( k7_relat_1('#skF_2','#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_87])).

tff(c_93,plain,(
    k7_relat_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_90])).

tff(c_95,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_93])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 21:07:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.58/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.17  
% 1.58/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.17  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.78/1.17  
% 1.78/1.17  %Foreground sorts:
% 1.78/1.17  
% 1.78/1.17  
% 1.78/1.17  %Background operators:
% 1.78/1.17  
% 1.78/1.17  
% 1.78/1.17  %Foreground operators:
% 1.78/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.78/1.17  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.78/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.78/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.78/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.78/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.78/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.78/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.78/1.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.78/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.78/1.17  
% 1.78/1.18  tff(f_55, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 1.78/1.18  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.78/1.18  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.78/1.18  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 1.78/1.18  tff(c_12, plain, (k7_relat_1('#skF_2', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.78/1.18  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.78/1.18  tff(c_14, plain, (r1_xboole_0('#skF_3', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.78/1.18  tff(c_4, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), k3_xboole_0(A_3, B_4)) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.78/1.18  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.78/1.18  tff(c_50, plain, (![A_13, B_14, C_15]: (~r1_xboole_0(A_13, B_14) | ~r2_hidden(C_15, k3_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.78/1.18  tff(c_68, plain, (![A_18, B_19, C_20]: (~r1_xboole_0(A_18, B_19) | ~r2_hidden(C_20, k3_xboole_0(B_19, A_18)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_50])).
% 1.78/1.18  tff(c_79, plain, (![B_21, A_22]: (~r1_xboole_0(B_21, A_22) | r1_xboole_0(A_22, B_21))), inference(resolution, [status(thm)], [c_4, c_68])).
% 1.78/1.18  tff(c_82, plain, (r1_xboole_0(k1_relat_1('#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_14, c_79])).
% 1.78/1.18  tff(c_87, plain, (![B_23, A_24]: (k7_relat_1(B_23, A_24)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_23), A_24) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.78/1.18  tff(c_90, plain, (k7_relat_1('#skF_2', '#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_82, c_87])).
% 1.78/1.18  tff(c_93, plain, (k7_relat_1('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_90])).
% 1.78/1.18  tff(c_95, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_93])).
% 1.78/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.18  
% 1.78/1.18  Inference rules
% 1.78/1.18  ----------------------
% 1.78/1.18  #Ref     : 0
% 1.78/1.18  #Sup     : 19
% 1.78/1.18  #Fact    : 0
% 1.78/1.18  #Define  : 0
% 1.78/1.18  #Split   : 0
% 1.78/1.18  #Chain   : 0
% 1.78/1.18  #Close   : 0
% 1.78/1.18  
% 1.78/1.18  Ordering : KBO
% 1.78/1.18  
% 1.78/1.18  Simplification rules
% 1.78/1.18  ----------------------
% 1.78/1.18  #Subsume      : 2
% 1.78/1.18  #Demod        : 2
% 1.78/1.18  #Tautology    : 10
% 1.78/1.18  #SimpNegUnit  : 1
% 1.78/1.18  #BackRed      : 0
% 1.78/1.18  
% 1.78/1.18  #Partial instantiations: 0
% 1.78/1.18  #Strategies tried      : 1
% 1.78/1.18  
% 1.78/1.18  Timing (in seconds)
% 1.78/1.18  ----------------------
% 1.78/1.18  Preprocessing        : 0.25
% 1.78/1.18  Parsing              : 0.14
% 1.78/1.18  CNF conversion       : 0.02
% 1.78/1.18  Main loop            : 0.11
% 1.78/1.18  Inferencing          : 0.05
% 1.78/1.18  Reduction            : 0.03
% 1.78/1.18  Demodulation         : 0.02
% 1.78/1.18  BG Simplification    : 0.01
% 1.78/1.18  Subsumption          : 0.02
% 1.78/1.18  Abstraction          : 0.00
% 1.78/1.18  MUC search           : 0.00
% 1.78/1.18  Cooper               : 0.00
% 1.78/1.18  Total                : 0.38
% 1.78/1.18  Index Insertion      : 0.00
% 1.78/1.18  Index Deletion       : 0.00
% 1.78/1.18  Index Matching       : 0.00
% 1.78/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
