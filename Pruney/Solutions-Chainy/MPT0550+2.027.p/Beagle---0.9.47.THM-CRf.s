%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:55 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   43 (  85 expanded)
%              Number of leaves         :   18 (  36 expanded)
%              Depth                    :   10
%              Number of atoms          :   55 ( 165 expanded)
%              Number of equality atoms :   27 (  75 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k1_relat_1(B))
            & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

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

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_36,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    k9_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( k2_relat_1(k7_relat_1(B_4,A_3)) = k9_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k7_relat_1(A_1,B_2))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_65,plain,(
    ! [B_14,A_15] :
      ( k1_relat_1(k7_relat_1(B_14,A_15)) = A_15
      | ~ r1_tarski(A_15,k1_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_68,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_65])).

tff(c_74,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_68])).

tff(c_14,plain,(
    ! [B_7,A_6] :
      ( k1_relat_1(k7_relat_1(B_7,A_6)) = A_6
      | ~ r1_tarski(A_6,k1_relat_1(B_7))
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_78,plain,(
    ! [A_6] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_6)) = A_6
      | ~ r1_tarski(A_6,'#skF_1')
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_14])).

tff(c_160,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_163,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_160])).

tff(c_167,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_163])).

tff(c_169,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_10,plain,(
    ! [A_5] :
      ( k2_relat_1(A_5) != k1_xboole_0
      | k1_xboole_0 = A_5
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_176,plain,
    ( k2_relat_1(k7_relat_1('#skF_2','#skF_1')) != k1_xboole_0
    | k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_169,c_10])).

tff(c_179,plain,(
    k2_relat_1(k7_relat_1('#skF_2','#skF_1')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_182,plain,
    ( k9_relat_1('#skF_2','#skF_1') != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_179])).

tff(c_185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_16,c_182])).

tff(c_186,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_189,plain,(
    k1_relat_1(k1_xboole_0) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_74])).

tff(c_8,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_219,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_8])).

tff(c_221,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_219])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:53:50 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.20  
% 1.88/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.20  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.88/1.20  
% 1.88/1.20  %Foreground sorts:
% 1.88/1.20  
% 1.88/1.20  
% 1.88/1.20  %Background operators:
% 1.88/1.20  
% 1.88/1.20  
% 1.88/1.20  %Foreground operators:
% 1.88/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.20  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.88/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.88/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.88/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.20  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.88/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.88/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.88/1.20  
% 1.88/1.21  tff(f_61, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_relat_1)).
% 1.88/1.21  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.88/1.21  tff(f_29, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.88/1.21  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 1.88/1.21  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 1.88/1.21  tff(f_36, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.88/1.21  tff(c_20, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.88/1.21  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.88/1.21  tff(c_16, plain, (k9_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.88/1.21  tff(c_4, plain, (![B_4, A_3]: (k2_relat_1(k7_relat_1(B_4, A_3))=k9_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.88/1.21  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k7_relat_1(A_1, B_2)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.88/1.21  tff(c_18, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.88/1.21  tff(c_65, plain, (![B_14, A_15]: (k1_relat_1(k7_relat_1(B_14, A_15))=A_15 | ~r1_tarski(A_15, k1_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.88/1.21  tff(c_68, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_18, c_65])).
% 1.88/1.21  tff(c_74, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_68])).
% 1.88/1.21  tff(c_14, plain, (![B_7, A_6]: (k1_relat_1(k7_relat_1(B_7, A_6))=A_6 | ~r1_tarski(A_6, k1_relat_1(B_7)) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.88/1.21  tff(c_78, plain, (![A_6]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_6))=A_6 | ~r1_tarski(A_6, '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_74, c_14])).
% 1.88/1.21  tff(c_160, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_78])).
% 1.88/1.21  tff(c_163, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2, c_160])).
% 1.88/1.21  tff(c_167, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_163])).
% 1.88/1.21  tff(c_169, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_78])).
% 1.88/1.21  tff(c_10, plain, (![A_5]: (k2_relat_1(A_5)!=k1_xboole_0 | k1_xboole_0=A_5 | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.88/1.21  tff(c_176, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))!=k1_xboole_0 | k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_169, c_10])).
% 1.88/1.21  tff(c_179, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_176])).
% 1.88/1.21  tff(c_182, plain, (k9_relat_1('#skF_2', '#skF_1')!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4, c_179])).
% 1.88/1.21  tff(c_185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_16, c_182])).
% 1.88/1.21  tff(c_186, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_176])).
% 1.88/1.21  tff(c_189, plain, (k1_relat_1(k1_xboole_0)='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_186, c_74])).
% 1.88/1.21  tff(c_8, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.88/1.21  tff(c_219, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_189, c_8])).
% 1.88/1.21  tff(c_221, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_219])).
% 1.88/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.21  
% 1.88/1.21  Inference rules
% 1.88/1.21  ----------------------
% 1.88/1.21  #Ref     : 0
% 1.88/1.21  #Sup     : 40
% 1.88/1.21  #Fact    : 0
% 1.88/1.21  #Define  : 0
% 1.88/1.21  #Split   : 7
% 1.88/1.21  #Chain   : 0
% 1.88/1.21  #Close   : 0
% 1.88/1.21  
% 1.88/1.21  Ordering : KBO
% 1.88/1.21  
% 1.88/1.21  Simplification rules
% 1.88/1.21  ----------------------
% 1.88/1.21  #Subsume      : 3
% 1.88/1.21  #Demod        : 30
% 1.88/1.21  #Tautology    : 21
% 1.88/1.21  #SimpNegUnit  : 2
% 1.88/1.21  #BackRed      : 5
% 1.88/1.21  
% 1.88/1.21  #Partial instantiations: 0
% 1.88/1.21  #Strategies tried      : 1
% 1.88/1.21  
% 1.88/1.21  Timing (in seconds)
% 1.88/1.21  ----------------------
% 1.88/1.21  Preprocessing        : 0.27
% 1.88/1.21  Parsing              : 0.15
% 1.88/1.21  CNF conversion       : 0.02
% 1.88/1.21  Main loop            : 0.17
% 1.88/1.21  Inferencing          : 0.06
% 1.88/1.21  Reduction            : 0.05
% 1.88/1.21  Demodulation         : 0.04
% 1.88/1.21  BG Simplification    : 0.01
% 1.88/1.21  Subsumption          : 0.04
% 1.88/1.21  Abstraction          : 0.01
% 1.88/1.21  MUC search           : 0.00
% 1.88/1.21  Cooper               : 0.00
% 1.88/1.22  Total                : 0.47
% 1.88/1.22  Index Insertion      : 0.00
% 1.88/1.22  Index Deletion       : 0.00
% 1.88/1.22  Index Matching       : 0.00
% 1.88/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
