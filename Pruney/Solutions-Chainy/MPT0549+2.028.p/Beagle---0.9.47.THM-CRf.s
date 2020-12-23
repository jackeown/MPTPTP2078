%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:51 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   43 (  64 expanded)
%              Number of leaves         :   18 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   60 ( 107 expanded)
%              Number of equality atoms :   30 (  47 expanded)
%              Maximal formula depth    :    7 (   3 average)
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

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k9_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_36,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_116,plain,(
    ! [B_20,A_21] :
      ( r1_xboole_0(k1_relat_1(B_20),A_21)
      | k7_relat_1(B_20,A_21) != k1_xboole_0
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_26,plain,
    ( k9_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_56,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_20,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | k9_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_58,plain,(
    k9_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_20])).

tff(c_6,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_72,plain,(
    ! [B_16,A_17] :
      ( k7_relat_1(B_16,A_17) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_16),A_17)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_78,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_72])).

tff(c_85,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_78])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( k2_relat_1(k7_relat_1(B_4,A_3)) = k9_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_89,plain,
    ( k9_relat_1('#skF_2','#skF_1') = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_4])).

tff(c_96,plain,(
    k9_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_6,c_89])).

tff(c_98,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_96])).

tff(c_99,plain,(
    k9_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_106,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_20])).

tff(c_119,plain,
    ( k7_relat_1('#skF_2','#skF_1') != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_116,c_106])).

tff(c_125,plain,(
    k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_119])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k7_relat_1(A_1,B_2))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_45,plain,(
    ! [A_11] :
      ( k2_relat_1(A_11) != k1_xboole_0
      | k1_xboole_0 = A_11
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_135,plain,(
    ! [A_24,B_25] :
      ( k2_relat_1(k7_relat_1(A_24,B_25)) != k1_xboole_0
      | k7_relat_1(A_24,B_25) = k1_xboole_0
      | ~ v1_relat_1(A_24) ) ),
    inference(resolution,[status(thm)],[c_2,c_45])).

tff(c_140,plain,(
    ! [B_28,A_29] :
      ( k9_relat_1(B_28,A_29) != k1_xboole_0
      | k7_relat_1(B_28,A_29) = k1_xboole_0
      | ~ v1_relat_1(B_28)
      | ~ v1_relat_1(B_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_135])).

tff(c_142,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_140])).

tff(c_145,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_142])).

tff(c_147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_145])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:55:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.13  
% 1.66/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.13  %$ r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.66/1.13  
% 1.66/1.13  %Foreground sorts:
% 1.66/1.13  
% 1.66/1.13  
% 1.66/1.13  %Background operators:
% 1.66/1.13  
% 1.66/1.13  
% 1.66/1.13  %Foreground operators:
% 1.66/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.13  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.66/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.66/1.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.66/1.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.66/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.66/1.13  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.66/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.66/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.66/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.66/1.13  
% 1.66/1.14  tff(f_57, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 1.66/1.14  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 1.66/1.14  tff(f_36, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.66/1.14  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.66/1.14  tff(f_29, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.66/1.14  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 1.66/1.14  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.66/1.14  tff(c_116, plain, (![B_20, A_21]: (r1_xboole_0(k1_relat_1(B_20), A_21) | k7_relat_1(B_20, A_21)!=k1_xboole_0 | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.66/1.14  tff(c_26, plain, (k9_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.66/1.14  tff(c_56, plain, (r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_26])).
% 1.66/1.14  tff(c_20, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | k9_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.66/1.14  tff(c_58, plain, (k9_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_56, c_20])).
% 1.66/1.14  tff(c_6, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.66/1.14  tff(c_72, plain, (![B_16, A_17]: (k7_relat_1(B_16, A_17)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_16), A_17) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.66/1.14  tff(c_78, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_72])).
% 1.66/1.14  tff(c_85, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_18, c_78])).
% 1.66/1.14  tff(c_4, plain, (![B_4, A_3]: (k2_relat_1(k7_relat_1(B_4, A_3))=k9_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.66/1.14  tff(c_89, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_85, c_4])).
% 1.66/1.14  tff(c_96, plain, (k9_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_18, c_6, c_89])).
% 1.66/1.14  tff(c_98, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_96])).
% 1.66/1.14  tff(c_99, plain, (k9_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_26])).
% 1.66/1.14  tff(c_106, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_20])).
% 1.66/1.14  tff(c_119, plain, (k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_116, c_106])).
% 1.66/1.14  tff(c_125, plain, (k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_18, c_119])).
% 1.66/1.14  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k7_relat_1(A_1, B_2)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.66/1.14  tff(c_45, plain, (![A_11]: (k2_relat_1(A_11)!=k1_xboole_0 | k1_xboole_0=A_11 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.66/1.14  tff(c_135, plain, (![A_24, B_25]: (k2_relat_1(k7_relat_1(A_24, B_25))!=k1_xboole_0 | k7_relat_1(A_24, B_25)=k1_xboole_0 | ~v1_relat_1(A_24))), inference(resolution, [status(thm)], [c_2, c_45])).
% 1.66/1.14  tff(c_140, plain, (![B_28, A_29]: (k9_relat_1(B_28, A_29)!=k1_xboole_0 | k7_relat_1(B_28, A_29)=k1_xboole_0 | ~v1_relat_1(B_28) | ~v1_relat_1(B_28))), inference(superposition, [status(thm), theory('equality')], [c_4, c_135])).
% 1.66/1.14  tff(c_142, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_99, c_140])).
% 1.66/1.14  tff(c_145, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_18, c_142])).
% 1.66/1.14  tff(c_147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_125, c_145])).
% 1.66/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.66/1.14  
% 1.66/1.14  Inference rules
% 1.66/1.14  ----------------------
% 1.66/1.14  #Ref     : 0
% 1.66/1.14  #Sup     : 28
% 1.66/1.14  #Fact    : 0
% 1.66/1.14  #Define  : 0
% 1.66/1.14  #Split   : 4
% 1.66/1.14  #Chain   : 0
% 1.66/1.14  #Close   : 0
% 1.66/1.14  
% 1.66/1.14  Ordering : KBO
% 1.66/1.14  
% 1.66/1.14  Simplification rules
% 1.66/1.14  ----------------------
% 1.66/1.14  #Subsume      : 2
% 1.66/1.14  #Demod        : 7
% 1.66/1.14  #Tautology    : 15
% 1.66/1.14  #SimpNegUnit  : 2
% 1.66/1.14  #BackRed      : 0
% 1.66/1.14  
% 1.66/1.14  #Partial instantiations: 0
% 1.66/1.14  #Strategies tried      : 1
% 1.66/1.14  
% 1.66/1.14  Timing (in seconds)
% 1.66/1.14  ----------------------
% 1.66/1.14  Preprocessing        : 0.25
% 1.66/1.14  Parsing              : 0.14
% 1.66/1.14  CNF conversion       : 0.02
% 1.66/1.14  Main loop            : 0.14
% 1.66/1.14  Inferencing          : 0.06
% 1.66/1.14  Reduction            : 0.04
% 1.66/1.14  Demodulation         : 0.03
% 1.66/1.14  BG Simplification    : 0.01
% 1.66/1.14  Subsumption          : 0.03
% 1.66/1.14  Abstraction          : 0.01
% 1.66/1.14  MUC search           : 0.00
% 1.66/1.14  Cooper               : 0.00
% 1.66/1.14  Total                : 0.41
% 1.66/1.14  Index Insertion      : 0.00
% 1.66/1.14  Index Deletion       : 0.00
% 1.66/1.14  Index Matching       : 0.00
% 1.66/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
