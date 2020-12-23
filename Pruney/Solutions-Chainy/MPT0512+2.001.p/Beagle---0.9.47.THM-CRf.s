%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:57 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   29 (  30 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  35 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_50,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(c_18,plain,(
    k7_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_33,plain,(
    ! [A_19,B_20] :
      ( r2_hidden('#skF_2'(A_19,B_20),B_20)
      | r1_xboole_0(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_37,plain,(
    ! [B_20,A_19] :
      ( ~ v1_xboole_0(B_20)
      | r1_xboole_0(A_19,B_20) ) ),
    inference(resolution,[status(thm)],[c_33,c_2])).

tff(c_50,plain,(
    ! [B_28,A_29] :
      ( k7_relat_1(B_28,A_29) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_28),A_29)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_65,plain,(
    ! [B_30,B_31] :
      ( k7_relat_1(B_30,B_31) = k1_xboole_0
      | ~ v1_relat_1(B_30)
      | ~ v1_xboole_0(B_31) ) ),
    inference(resolution,[status(thm)],[c_37,c_50])).

tff(c_69,plain,(
    ! [B_32] :
      ( k7_relat_1('#skF_3',B_32) = k1_xboole_0
      | ~ v1_xboole_0(B_32) ) ),
    inference(resolution,[status(thm)],[c_20,c_65])).

tff(c_72,plain,(
    k7_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_69])).

tff(c_76,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_72])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:42:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.10  
% 1.66/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.11  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.66/1.11  
% 1.66/1.11  %Foreground sorts:
% 1.66/1.11  
% 1.66/1.11  
% 1.66/1.11  %Background operators:
% 1.66/1.11  
% 1.66/1.11  
% 1.66/1.11  %Foreground operators:
% 1.66/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.66/1.11  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.66/1.11  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.66/1.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.66/1.11  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.66/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.66/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.66/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.11  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.66/1.11  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.66/1.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.66/1.11  
% 1.66/1.11  tff(f_61, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_relat_1)).
% 1.66/1.11  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.66/1.11  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.66/1.11  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.66/1.11  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 1.66/1.11  tff(c_18, plain, (k7_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.66/1.11  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.66/1.11  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.66/1.11  tff(c_33, plain, (![A_19, B_20]: (r2_hidden('#skF_2'(A_19, B_20), B_20) | r1_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.66/1.11  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.66/1.11  tff(c_37, plain, (![B_20, A_19]: (~v1_xboole_0(B_20) | r1_xboole_0(A_19, B_20))), inference(resolution, [status(thm)], [c_33, c_2])).
% 1.66/1.11  tff(c_50, plain, (![B_28, A_29]: (k7_relat_1(B_28, A_29)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_28), A_29) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.66/1.11  tff(c_65, plain, (![B_30, B_31]: (k7_relat_1(B_30, B_31)=k1_xboole_0 | ~v1_relat_1(B_30) | ~v1_xboole_0(B_31))), inference(resolution, [status(thm)], [c_37, c_50])).
% 1.66/1.11  tff(c_69, plain, (![B_32]: (k7_relat_1('#skF_3', B_32)=k1_xboole_0 | ~v1_xboole_0(B_32))), inference(resolution, [status(thm)], [c_20, c_65])).
% 1.66/1.11  tff(c_72, plain, (k7_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_69])).
% 1.66/1.11  tff(c_76, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_72])).
% 1.66/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.11  
% 1.66/1.11  Inference rules
% 1.66/1.11  ----------------------
% 1.66/1.11  #Ref     : 0
% 1.66/1.11  #Sup     : 11
% 1.66/1.11  #Fact    : 0
% 1.66/1.11  #Define  : 0
% 1.66/1.11  #Split   : 0
% 1.66/1.11  #Chain   : 0
% 1.66/1.11  #Close   : 0
% 1.66/1.11  
% 1.66/1.11  Ordering : KBO
% 1.66/1.11  
% 1.66/1.11  Simplification rules
% 1.66/1.11  ----------------------
% 1.66/1.11  #Subsume      : 2
% 1.66/1.11  #Demod        : 0
% 1.66/1.11  #Tautology    : 2
% 1.66/1.11  #SimpNegUnit  : 1
% 1.66/1.11  #BackRed      : 0
% 1.66/1.11  
% 1.66/1.11  #Partial instantiations: 0
% 1.66/1.11  #Strategies tried      : 1
% 1.66/1.12  
% 1.66/1.12  Timing (in seconds)
% 1.66/1.12  ----------------------
% 1.66/1.12  Preprocessing        : 0.26
% 1.66/1.12  Parsing              : 0.14
% 1.66/1.12  CNF conversion       : 0.02
% 1.66/1.12  Main loop            : 0.11
% 1.66/1.12  Inferencing          : 0.06
% 1.66/1.12  Reduction            : 0.02
% 1.66/1.12  Demodulation         : 0.01
% 1.66/1.12  BG Simplification    : 0.01
% 1.66/1.12  Subsumption          : 0.02
% 1.66/1.12  Abstraction          : 0.00
% 1.66/1.12  MUC search           : 0.00
% 1.66/1.12  Cooper               : 0.00
% 1.66/1.12  Total                : 0.39
% 1.66/1.12  Index Insertion      : 0.00
% 1.66/1.12  Index Deletion       : 0.00
% 1.66/1.12  Index Matching       : 0.00
% 1.66/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
