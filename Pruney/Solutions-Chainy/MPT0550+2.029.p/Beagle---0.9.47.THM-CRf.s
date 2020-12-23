%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:55 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   34 (  37 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   47 (  59 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k9_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k1_relat_1(B))
            & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_14,plain,(
    k9_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_38,plain,(
    ! [B_18,A_19] :
      ( r1_xboole_0(k1_relat_1(B_18),A_19)
      | k9_relat_1(B_18,A_19) != k1_xboole_0
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_50,plain,(
    ! [A_20,B_21] :
      ( r1_xboole_0(A_20,k1_relat_1(B_21))
      | k9_relat_1(B_21,A_20) != k1_xboole_0
      | ~ v1_relat_1(B_21) ) ),
    inference(resolution,[status(thm)],[c_38,c_4])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( ~ r1_xboole_0(B_4,A_3)
      | ~ r1_tarski(B_4,A_3)
      | v1_xboole_0(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_63,plain,(
    ! [A_22,B_23] :
      ( ~ r1_tarski(A_22,k1_relat_1(B_23))
      | v1_xboole_0(A_22)
      | k9_relat_1(B_23,A_22) != k1_xboole_0
      | ~ v1_relat_1(B_23) ) ),
    inference(resolution,[status(thm)],[c_50,c_6])).

tff(c_66,plain,
    ( v1_xboole_0('#skF_1')
    | k9_relat_1('#skF_2','#skF_1') != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_63])).

tff(c_69,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_14,c_66])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_26,plain,(
    ! [B_11,A_12] :
      ( ~ v1_xboole_0(B_11)
      | B_11 = A_12
      | ~ v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_29,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ v1_xboole_0(A_12) ) ),
    inference(resolution,[status(thm)],[c_2,c_26])).

tff(c_72,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_69,c_29])).

tff(c_78,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_72])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n021.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 20:01:34 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.10  
% 1.65/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.10  %$ r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k9_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.65/1.10  
% 1.65/1.10  %Foreground sorts:
% 1.65/1.10  
% 1.65/1.10  
% 1.65/1.10  %Background operators:
% 1.65/1.10  
% 1.65/1.10  
% 1.65/1.10  %Foreground operators:
% 1.65/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.65/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.65/1.10  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.65/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.10  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.65/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.65/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.10  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.65/1.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.65/1.10  
% 1.65/1.11  tff(f_63, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_relat_1)).
% 1.65/1.11  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 1.65/1.11  tff(f_30, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.65/1.11  tff(f_38, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 1.65/1.11  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.65/1.11  tff(f_46, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 1.65/1.11  tff(c_18, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.65/1.11  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.65/1.11  tff(c_14, plain, (k9_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.65/1.11  tff(c_16, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.65/1.11  tff(c_38, plain, (![B_18, A_19]: (r1_xboole_0(k1_relat_1(B_18), A_19) | k9_relat_1(B_18, A_19)!=k1_xboole_0 | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.65/1.11  tff(c_4, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.65/1.11  tff(c_50, plain, (![A_20, B_21]: (r1_xboole_0(A_20, k1_relat_1(B_21)) | k9_relat_1(B_21, A_20)!=k1_xboole_0 | ~v1_relat_1(B_21))), inference(resolution, [status(thm)], [c_38, c_4])).
% 1.65/1.11  tff(c_6, plain, (![B_4, A_3]: (~r1_xboole_0(B_4, A_3) | ~r1_tarski(B_4, A_3) | v1_xboole_0(B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.65/1.11  tff(c_63, plain, (![A_22, B_23]: (~r1_tarski(A_22, k1_relat_1(B_23)) | v1_xboole_0(A_22) | k9_relat_1(B_23, A_22)!=k1_xboole_0 | ~v1_relat_1(B_23))), inference(resolution, [status(thm)], [c_50, c_6])).
% 1.65/1.11  tff(c_66, plain, (v1_xboole_0('#skF_1') | k9_relat_1('#skF_2', '#skF_1')!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_63])).
% 1.65/1.11  tff(c_69, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_14, c_66])).
% 1.65/1.11  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.65/1.11  tff(c_26, plain, (![B_11, A_12]: (~v1_xboole_0(B_11) | B_11=A_12 | ~v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.65/1.11  tff(c_29, plain, (![A_12]: (k1_xboole_0=A_12 | ~v1_xboole_0(A_12))), inference(resolution, [status(thm)], [c_2, c_26])).
% 1.65/1.11  tff(c_72, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_69, c_29])).
% 1.65/1.11  tff(c_78, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_72])).
% 1.65/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.11  
% 1.65/1.11  Inference rules
% 1.65/1.11  ----------------------
% 1.65/1.11  #Ref     : 0
% 1.65/1.11  #Sup     : 13
% 1.65/1.11  #Fact    : 0
% 1.65/1.11  #Define  : 0
% 1.65/1.11  #Split   : 0
% 1.65/1.11  #Chain   : 0
% 1.65/1.11  #Close   : 0
% 1.65/1.11  
% 1.65/1.11  Ordering : KBO
% 1.65/1.11  
% 1.65/1.11  Simplification rules
% 1.65/1.11  ----------------------
% 1.65/1.11  #Subsume      : 1
% 1.65/1.11  #Demod        : 2
% 1.65/1.11  #Tautology    : 4
% 1.65/1.11  #SimpNegUnit  : 1
% 1.65/1.11  #BackRed      : 0
% 1.65/1.11  
% 1.65/1.11  #Partial instantiations: 0
% 1.65/1.11  #Strategies tried      : 1
% 1.65/1.11  
% 1.65/1.11  Timing (in seconds)
% 1.65/1.11  ----------------------
% 1.65/1.12  Preprocessing        : 0.27
% 1.65/1.12  Parsing              : 0.15
% 1.65/1.12  CNF conversion       : 0.02
% 1.65/1.12  Main loop            : 0.11
% 1.65/1.12  Inferencing          : 0.05
% 1.65/1.12  Reduction            : 0.03
% 1.65/1.12  Demodulation         : 0.02
% 1.65/1.12  BG Simplification    : 0.01
% 1.65/1.12  Subsumption          : 0.02
% 1.65/1.12  Abstraction          : 0.00
% 1.65/1.12  MUC search           : 0.00
% 1.65/1.12  Cooper               : 0.00
% 1.65/1.12  Total                : 0.40
% 1.65/1.12  Index Insertion      : 0.00
% 1.65/1.12  Index Deletion       : 0.00
% 1.65/1.12  Index Matching       : 0.00
% 1.65/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
