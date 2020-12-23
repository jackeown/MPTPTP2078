%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:48 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   38 (  44 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   41 (  50 expanded)
%              Number of equality atoms :   25 (  31 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_46,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_55,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_10,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_57,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_59,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_57])).

tff(c_18,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( r1_xboole_0(A_2,B_3)
      | k4_xboole_0(A_2,B_3) != A_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_96,plain,(
    ! [B_25,A_26] :
      ( k7_relat_1(B_25,A_26) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_25),A_26)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_103,plain,(
    ! [A_26] :
      ( k7_relat_1(k1_xboole_0,A_26) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_26)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_96])).

tff(c_107,plain,(
    ! [A_27] :
      ( k7_relat_1(k1_xboole_0,A_27) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_103])).

tff(c_111,plain,(
    ! [B_3] :
      ( k7_relat_1(k1_xboole_0,B_3) = k1_xboole_0
      | k4_xboole_0(k1_xboole_0,B_3) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_107])).

tff(c_130,plain,(
    ! [B_30] : k7_relat_1(k1_xboole_0,B_30) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_111])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( k2_relat_1(k7_relat_1(B_9,A_8)) = k9_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_135,plain,(
    ! [B_30] :
      ( k9_relat_1(k1_xboole_0,B_30) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_16])).

tff(c_140,plain,(
    ! [B_30] : k9_relat_1(k1_xboole_0,B_30) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_18,c_135])).

tff(c_26,plain,(
    k9_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:04:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.12  
% 1.77/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.13  %$ r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.77/1.13  
% 1.77/1.13  %Foreground sorts:
% 1.77/1.13  
% 1.77/1.13  
% 1.77/1.13  %Background operators:
% 1.77/1.13  
% 1.77/1.13  
% 1.77/1.13  %Foreground operators:
% 1.77/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.77/1.13  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.77/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.77/1.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.77/1.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.77/1.13  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.77/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.77/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.77/1.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.77/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.77/1.13  
% 1.77/1.14  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.77/1.14  tff(f_39, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.77/1.14  tff(f_46, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.77/1.14  tff(f_27, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.77/1.14  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.77/1.14  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 1.77/1.14  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.77/1.14  tff(f_55, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 1.77/1.14  tff(c_10, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.77/1.14  tff(c_57, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.77/1.14  tff(c_59, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_57])).
% 1.77/1.14  tff(c_18, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.77/1.14  tff(c_2, plain, (![A_1]: (k4_xboole_0(k1_xboole_0, A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.77/1.14  tff(c_6, plain, (![A_2, B_3]: (r1_xboole_0(A_2, B_3) | k4_xboole_0(A_2, B_3)!=A_2)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.77/1.14  tff(c_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.77/1.14  tff(c_96, plain, (![B_25, A_26]: (k7_relat_1(B_25, A_26)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_25), A_26) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.77/1.14  tff(c_103, plain, (![A_26]: (k7_relat_1(k1_xboole_0, A_26)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_26) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_96])).
% 1.77/1.14  tff(c_107, plain, (![A_27]: (k7_relat_1(k1_xboole_0, A_27)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_27))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_103])).
% 1.77/1.14  tff(c_111, plain, (![B_3]: (k7_relat_1(k1_xboole_0, B_3)=k1_xboole_0 | k4_xboole_0(k1_xboole_0, B_3)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_107])).
% 1.77/1.14  tff(c_130, plain, (![B_30]: (k7_relat_1(k1_xboole_0, B_30)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_111])).
% 1.77/1.14  tff(c_16, plain, (![B_9, A_8]: (k2_relat_1(k7_relat_1(B_9, A_8))=k9_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.77/1.14  tff(c_135, plain, (![B_30]: (k9_relat_1(k1_xboole_0, B_30)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_130, c_16])).
% 1.77/1.14  tff(c_140, plain, (![B_30]: (k9_relat_1(k1_xboole_0, B_30)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_59, c_18, c_135])).
% 1.77/1.14  tff(c_26, plain, (k9_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.77/1.14  tff(c_144, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_26])).
% 1.77/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.14  
% 1.77/1.14  Inference rules
% 1.77/1.14  ----------------------
% 1.77/1.14  #Ref     : 0
% 1.77/1.14  #Sup     : 28
% 1.77/1.14  #Fact    : 0
% 1.77/1.14  #Define  : 0
% 1.77/1.14  #Split   : 0
% 1.77/1.14  #Chain   : 0
% 1.77/1.14  #Close   : 0
% 1.77/1.14  
% 1.77/1.14  Ordering : KBO
% 1.77/1.14  
% 1.77/1.14  Simplification rules
% 1.77/1.14  ----------------------
% 1.77/1.14  #Subsume      : 0
% 1.77/1.14  #Demod        : 8
% 1.77/1.14  #Tautology    : 22
% 1.77/1.14  #SimpNegUnit  : 0
% 1.77/1.14  #BackRed      : 1
% 1.77/1.14  
% 1.77/1.14  #Partial instantiations: 0
% 1.77/1.14  #Strategies tried      : 1
% 1.77/1.14  
% 1.77/1.14  Timing (in seconds)
% 1.77/1.14  ----------------------
% 1.77/1.14  Preprocessing        : 0.26
% 1.77/1.14  Parsing              : 0.14
% 1.77/1.14  CNF conversion       : 0.01
% 1.77/1.14  Main loop            : 0.12
% 1.77/1.14  Inferencing          : 0.05
% 1.77/1.14  Reduction            : 0.03
% 1.77/1.14  Demodulation         : 0.03
% 1.77/1.14  BG Simplification    : 0.01
% 1.77/1.14  Subsumption          : 0.02
% 1.77/1.14  Abstraction          : 0.01
% 1.77/1.14  MUC search           : 0.00
% 1.77/1.14  Cooper               : 0.00
% 1.77/1.14  Total                : 0.40
% 1.77/1.14  Index Insertion      : 0.00
% 1.77/1.14  Index Deletion       : 0.00
% 1.77/1.14  Index Matching       : 0.00
% 1.77/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
