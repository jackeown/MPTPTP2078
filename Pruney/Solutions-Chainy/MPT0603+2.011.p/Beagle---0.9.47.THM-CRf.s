%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:25 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   34 (  38 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   37 (  47 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_55,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_xboole_0(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_30,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_xboole_0(B) )
     => ( v1_xboole_0(k7_relat_1(A,B))
        & v1_relat_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc16_relat_1)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_52,plain,(
    ! [A_18,B_19] :
      ( v1_xboole_0(k7_relat_1(A_18,B_19))
      | ~ v1_xboole_0(B_19)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_58,plain,(
    ! [A_22,B_23] :
      ( k7_relat_1(A_22,B_23) = k1_xboole_0
      | ~ v1_xboole_0(B_23)
      | ~ v1_relat_1(A_22) ) ),
    inference(resolution,[status(thm)],[c_52,c_8])).

tff(c_65,plain,(
    ! [A_24] :
      ( k7_relat_1(A_24,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_24) ) ),
    inference(resolution,[status(thm)],[c_6,c_58])).

tff(c_73,plain,(
    k7_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_65])).

tff(c_20,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_29,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = k1_xboole_0
      | ~ r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_33,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_29])).

tff(c_92,plain,(
    ! [C_25,A_26,B_27] :
      ( k7_relat_1(k7_relat_1(C_25,A_26),B_27) = k7_relat_1(C_25,k3_xboole_0(A_26,B_27))
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_18,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_107,plain,
    ( k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_18])).

tff(c_120,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_73,c_33,c_107])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:48:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.18  
% 1.76/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.18  %$ r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.76/1.18  
% 1.76/1.18  %Foreground sorts:
% 1.76/1.18  
% 1.76/1.18  
% 1.76/1.18  %Background operators:
% 1.76/1.18  
% 1.76/1.18  
% 1.76/1.18  %Foreground operators:
% 1.76/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.76/1.18  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.76/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.76/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.76/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.76/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.76/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.76/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.76/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.76/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.76/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.76/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.76/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.76/1.18  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.76/1.18  
% 1.76/1.19  tff(f_55, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 1.76/1.19  tff(f_30, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.76/1.19  tff(f_44, axiom, (![A, B]: ((v1_relat_1(A) & v1_xboole_0(B)) => (v1_xboole_0(k7_relat_1(A, B)) & v1_relat_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc16_relat_1)).
% 1.76/1.19  tff(f_34, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.76/1.19  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.76/1.19  tff(f_48, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 1.76/1.19  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.76/1.19  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.76/1.19  tff(c_52, plain, (![A_18, B_19]: (v1_xboole_0(k7_relat_1(A_18, B_19)) | ~v1_xboole_0(B_19) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.76/1.19  tff(c_8, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.76/1.19  tff(c_58, plain, (![A_22, B_23]: (k7_relat_1(A_22, B_23)=k1_xboole_0 | ~v1_xboole_0(B_23) | ~v1_relat_1(A_22))), inference(resolution, [status(thm)], [c_52, c_8])).
% 1.76/1.19  tff(c_65, plain, (![A_24]: (k7_relat_1(A_24, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_24))), inference(resolution, [status(thm)], [c_6, c_58])).
% 1.76/1.19  tff(c_73, plain, (k7_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_65])).
% 1.76/1.19  tff(c_20, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.76/1.19  tff(c_29, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=k1_xboole_0 | ~r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.88/1.19  tff(c_33, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_29])).
% 1.88/1.19  tff(c_92, plain, (![C_25, A_26, B_27]: (k7_relat_1(k7_relat_1(C_25, A_26), B_27)=k7_relat_1(C_25, k3_xboole_0(A_26, B_27)) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.88/1.19  tff(c_18, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.88/1.19  tff(c_107, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_92, c_18])).
% 1.88/1.19  tff(c_120, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_73, c_33, c_107])).
% 1.88/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.19  
% 1.88/1.19  Inference rules
% 1.88/1.19  ----------------------
% 1.88/1.19  #Ref     : 0
% 1.88/1.19  #Sup     : 25
% 1.88/1.19  #Fact    : 0
% 1.88/1.19  #Define  : 0
% 1.88/1.19  #Split   : 0
% 1.88/1.19  #Chain   : 0
% 1.88/1.19  #Close   : 0
% 1.88/1.19  
% 1.88/1.19  Ordering : KBO
% 1.88/1.19  
% 1.88/1.19  Simplification rules
% 1.88/1.19  ----------------------
% 1.88/1.19  #Subsume      : 0
% 1.88/1.19  #Demod        : 8
% 1.88/1.19  #Tautology    : 10
% 1.88/1.19  #SimpNegUnit  : 0
% 1.88/1.19  #BackRed      : 0
% 1.88/1.19  
% 1.88/1.19  #Partial instantiations: 0
% 1.88/1.19  #Strategies tried      : 1
% 1.88/1.19  
% 1.88/1.19  Timing (in seconds)
% 1.88/1.19  ----------------------
% 1.88/1.19  Preprocessing        : 0.26
% 1.88/1.19  Parsing              : 0.14
% 1.88/1.19  CNF conversion       : 0.02
% 1.88/1.19  Main loop            : 0.13
% 1.88/1.19  Inferencing          : 0.06
% 1.88/1.19  Reduction            : 0.03
% 1.88/1.19  Demodulation         : 0.02
% 1.88/1.19  BG Simplification    : 0.01
% 1.88/1.19  Subsumption          : 0.02
% 1.88/1.19  Abstraction          : 0.01
% 1.88/1.19  MUC search           : 0.00
% 1.88/1.19  Cooper               : 0.00
% 1.88/1.19  Total                : 0.41
% 1.88/1.19  Index Insertion      : 0.00
% 1.88/1.19  Index Deletion       : 0.00
% 1.88/1.19  Index Matching       : 0.00
% 1.88/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
