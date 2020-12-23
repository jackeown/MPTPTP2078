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
% DateTime   : Thu Dec  3 10:00:36 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   36 (  42 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   38 (  47 expanded)
%              Number of equality atoms :   14 (  16 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_43,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_32,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_30,plain,(
    ! [A_10] :
      ( v1_relat_1(A_10)
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_34,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_30])).

tff(c_12,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_35,plain,(
    ! [B_11,A_12] :
      ( r1_xboole_0(B_11,A_12)
      | ~ r1_xboole_0(A_12,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_38,plain,(
    ! [A_3] : r1_xboole_0(k1_xboole_0,A_3) ),
    inference(resolution,[status(thm)],[c_6,c_35])).

tff(c_14,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_53,plain,(
    ! [B_16,A_17] :
      ( k7_relat_1(B_16,A_17) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_16),A_17)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_60,plain,(
    ! [A_17] :
      ( k7_relat_1(k1_xboole_0,A_17) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_17)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_53])).

tff(c_64,plain,(
    ! [A_18] : k7_relat_1(k1_xboole_0,A_18) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_38,c_60])).

tff(c_10,plain,(
    ! [B_6,A_5] :
      ( k2_relat_1(k7_relat_1(B_6,A_5)) = k9_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_69,plain,(
    ! [A_18] :
      ( k9_relat_1(k1_xboole_0,A_18) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_10])).

tff(c_74,plain,(
    ! [A_18] : k9_relat_1(k1_xboole_0,A_18) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_12,c_69])).

tff(c_20,plain,(
    k9_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_78,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:36:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.15  
% 1.74/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.15  %$ r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.74/1.15  
% 1.74/1.15  %Foreground sorts:
% 1.74/1.15  
% 1.74/1.15  
% 1.74/1.15  %Background operators:
% 1.74/1.15  
% 1.74/1.15  
% 1.74/1.15  %Foreground operators:
% 1.74/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.74/1.15  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.74/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.74/1.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.74/1.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.74/1.15  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.74/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.74/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.74/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.74/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.74/1.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.74/1.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.74/1.15  
% 1.74/1.16  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.74/1.16  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.74/1.16  tff(f_43, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.74/1.16  tff(f_32, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.74/1.16  tff(f_30, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.74/1.16  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 1.74/1.16  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.74/1.16  tff(f_52, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 1.74/1.16  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.74/1.16  tff(c_30, plain, (![A_10]: (v1_relat_1(A_10) | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.74/1.16  tff(c_34, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_30])).
% 1.74/1.16  tff(c_12, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.74/1.16  tff(c_6, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.74/1.16  tff(c_35, plain, (![B_11, A_12]: (r1_xboole_0(B_11, A_12) | ~r1_xboole_0(A_12, B_11))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.74/1.16  tff(c_38, plain, (![A_3]: (r1_xboole_0(k1_xboole_0, A_3))), inference(resolution, [status(thm)], [c_6, c_35])).
% 1.74/1.16  tff(c_14, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.74/1.16  tff(c_53, plain, (![B_16, A_17]: (k7_relat_1(B_16, A_17)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_16), A_17) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.74/1.16  tff(c_60, plain, (![A_17]: (k7_relat_1(k1_xboole_0, A_17)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_17) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_53])).
% 1.74/1.16  tff(c_64, plain, (![A_18]: (k7_relat_1(k1_xboole_0, A_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_38, c_60])).
% 1.74/1.16  tff(c_10, plain, (![B_6, A_5]: (k2_relat_1(k7_relat_1(B_6, A_5))=k9_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.74/1.16  tff(c_69, plain, (![A_18]: (k9_relat_1(k1_xboole_0, A_18)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_64, c_10])).
% 1.74/1.16  tff(c_74, plain, (![A_18]: (k9_relat_1(k1_xboole_0, A_18)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_12, c_69])).
% 1.74/1.16  tff(c_20, plain, (k9_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.74/1.16  tff(c_78, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_20])).
% 1.74/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.16  
% 1.74/1.16  Inference rules
% 1.74/1.16  ----------------------
% 1.74/1.16  #Ref     : 0
% 1.74/1.16  #Sup     : 14
% 1.74/1.16  #Fact    : 0
% 1.74/1.16  #Define  : 0
% 1.74/1.16  #Split   : 0
% 1.74/1.16  #Chain   : 0
% 1.74/1.16  #Close   : 0
% 1.74/1.16  
% 1.74/1.16  Ordering : KBO
% 1.74/1.16  
% 1.74/1.16  Simplification rules
% 1.74/1.16  ----------------------
% 1.74/1.16  #Subsume      : 0
% 1.74/1.16  #Demod        : 6
% 1.74/1.16  #Tautology    : 9
% 1.74/1.16  #SimpNegUnit  : 0
% 1.74/1.16  #BackRed      : 1
% 1.74/1.16  
% 1.74/1.16  #Partial instantiations: 0
% 1.74/1.16  #Strategies tried      : 1
% 1.74/1.16  
% 1.74/1.16  Timing (in seconds)
% 1.74/1.16  ----------------------
% 1.74/1.17  Preprocessing        : 0.26
% 1.74/1.17  Parsing              : 0.14
% 1.74/1.17  CNF conversion       : 0.01
% 1.74/1.17  Main loop            : 0.10
% 1.74/1.17  Inferencing          : 0.05
% 1.74/1.17  Reduction            : 0.03
% 1.74/1.17  Demodulation         : 0.02
% 1.74/1.17  BG Simplification    : 0.01
% 1.74/1.17  Subsumption          : 0.02
% 1.74/1.17  Abstraction          : 0.00
% 1.74/1.17  MUC search           : 0.00
% 1.74/1.17  Cooper               : 0.00
% 1.74/1.17  Total                : 0.39
% 1.74/1.17  Index Insertion      : 0.00
% 1.74/1.17  Index Deletion       : 0.00
% 1.74/1.17  Index Matching       : 0.00
% 1.74/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
