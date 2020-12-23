%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:59 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   34 (  38 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   46 (  56 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( r1_xboole_0(B,k1_relat_1(A))
           => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_16,plain,(
    k7_relat_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    r1_xboole_0('#skF_2',k1_relat_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_22,plain,(
    ! [B_13,A_14] :
      ( r1_xboole_0(B_13,A_14)
      | ~ r1_xboole_0(A_14,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_25,plain,(
    r1_xboole_0(k1_relat_1('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_22])).

tff(c_59,plain,(
    ! [B_19,A_20] :
      ( k9_relat_1(B_19,A_20) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_19),A_20)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_62,plain,
    ( k9_relat_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_25,c_59])).

tff(c_65,plain,(
    k9_relat_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_62])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( k2_relat_1(k7_relat_1(B_6,A_5)) = k9_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( v1_relat_1(k7_relat_1(A_3,B_4))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_40,plain,(
    ! [A_16] :
      ( k2_relat_1(A_16) != k1_xboole_0
      | k1_xboole_0 = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_87,plain,(
    ! [A_25,B_26] :
      ( k2_relat_1(k7_relat_1(A_25,B_26)) != k1_xboole_0
      | k7_relat_1(A_25,B_26) = k1_xboole_0
      | ~ v1_relat_1(A_25) ) ),
    inference(resolution,[status(thm)],[c_4,c_40])).

tff(c_92,plain,(
    ! [B_29,A_30] :
      ( k9_relat_1(B_29,A_30) != k1_xboole_0
      | k7_relat_1(B_29,A_30) = k1_xboole_0
      | ~ v1_relat_1(B_29)
      | ~ v1_relat_1(B_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_87])).

tff(c_94,plain,
    ( k7_relat_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_92])).

tff(c_97,plain,(
    k7_relat_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_94])).

tff(c_99,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_97])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n005.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 19:54:47 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.17  
% 1.77/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.17  %$ r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.77/1.17  
% 1.77/1.17  %Foreground sorts:
% 1.77/1.17  
% 1.77/1.17  
% 1.77/1.17  %Background operators:
% 1.77/1.17  
% 1.77/1.17  
% 1.77/1.17  %Foreground operators:
% 1.77/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.17  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.77/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.77/1.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.77/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.77/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.77/1.17  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.77/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.77/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.77/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.77/1.17  
% 1.77/1.18  tff(f_59, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 1.77/1.18  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.77/1.18  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 1.77/1.18  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.77/1.18  tff(f_33, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.77/1.18  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 1.77/1.18  tff(c_16, plain, (k7_relat_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.77/1.18  tff(c_20, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.77/1.18  tff(c_18, plain, (r1_xboole_0('#skF_2', k1_relat_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.77/1.18  tff(c_22, plain, (![B_13, A_14]: (r1_xboole_0(B_13, A_14) | ~r1_xboole_0(A_14, B_13))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.77/1.18  tff(c_25, plain, (r1_xboole_0(k1_relat_1('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_18, c_22])).
% 1.77/1.18  tff(c_59, plain, (![B_19, A_20]: (k9_relat_1(B_19, A_20)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_19), A_20) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.77/1.18  tff(c_62, plain, (k9_relat_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_25, c_59])).
% 1.77/1.18  tff(c_65, plain, (k9_relat_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_62])).
% 1.77/1.18  tff(c_6, plain, (![B_6, A_5]: (k2_relat_1(k7_relat_1(B_6, A_5))=k9_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.77/1.18  tff(c_4, plain, (![A_3, B_4]: (v1_relat_1(k7_relat_1(A_3, B_4)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.77/1.18  tff(c_40, plain, (![A_16]: (k2_relat_1(A_16)!=k1_xboole_0 | k1_xboole_0=A_16 | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.77/1.18  tff(c_87, plain, (![A_25, B_26]: (k2_relat_1(k7_relat_1(A_25, B_26))!=k1_xboole_0 | k7_relat_1(A_25, B_26)=k1_xboole_0 | ~v1_relat_1(A_25))), inference(resolution, [status(thm)], [c_4, c_40])).
% 1.77/1.18  tff(c_92, plain, (![B_29, A_30]: (k9_relat_1(B_29, A_30)!=k1_xboole_0 | k7_relat_1(B_29, A_30)=k1_xboole_0 | ~v1_relat_1(B_29) | ~v1_relat_1(B_29))), inference(superposition, [status(thm), theory('equality')], [c_6, c_87])).
% 1.77/1.18  tff(c_94, plain, (k7_relat_1('#skF_1', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_65, c_92])).
% 1.77/1.18  tff(c_97, plain, (k7_relat_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_94])).
% 1.77/1.18  tff(c_99, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_97])).
% 1.77/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.18  
% 1.77/1.18  Inference rules
% 1.77/1.18  ----------------------
% 1.77/1.18  #Ref     : 0
% 1.77/1.18  #Sup     : 17
% 1.77/1.18  #Fact    : 0
% 1.77/1.18  #Define  : 0
% 1.77/1.18  #Split   : 2
% 1.77/1.18  #Chain   : 0
% 1.77/1.18  #Close   : 0
% 1.77/1.18  
% 1.77/1.18  Ordering : KBO
% 1.77/1.18  
% 1.77/1.18  Simplification rules
% 1.77/1.18  ----------------------
% 1.77/1.18  #Subsume      : 1
% 1.77/1.18  #Demod        : 3
% 1.77/1.18  #Tautology    : 6
% 1.77/1.18  #SimpNegUnit  : 1
% 1.77/1.18  #BackRed      : 0
% 1.77/1.18  
% 1.77/1.18  #Partial instantiations: 0
% 1.77/1.18  #Strategies tried      : 1
% 1.77/1.18  
% 1.77/1.18  Timing (in seconds)
% 1.77/1.18  ----------------------
% 1.77/1.18  Preprocessing        : 0.28
% 1.77/1.18  Parsing              : 0.16
% 1.77/1.18  CNF conversion       : 0.02
% 1.77/1.18  Main loop            : 0.13
% 1.77/1.18  Inferencing          : 0.05
% 1.77/1.18  Reduction            : 0.03
% 1.77/1.18  Demodulation         : 0.02
% 1.77/1.18  BG Simplification    : 0.01
% 1.77/1.18  Subsumption          : 0.02
% 1.77/1.18  Abstraction          : 0.00
% 1.77/1.18  MUC search           : 0.00
% 1.77/1.18  Cooper               : 0.00
% 1.77/1.18  Total                : 0.43
% 1.77/1.18  Index Insertion      : 0.00
% 1.77/1.18  Index Deletion       : 0.00
% 1.77/1.18  Index Matching       : 0.00
% 1.77/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
