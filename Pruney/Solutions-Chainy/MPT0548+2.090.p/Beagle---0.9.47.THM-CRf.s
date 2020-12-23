%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:47 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   36 (  44 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   33 (  45 expanded)
%              Number of equality atoms :   23 (  32 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_48,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k9_relat_1(B,A) = k9_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).

tff(f_51,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_10,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_60,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_62,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_60])).

tff(c_18,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_20,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_102,plain,(
    ! [A_19] :
      ( k9_relat_1(A_19,k1_relat_1(A_19)) = k2_relat_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_111,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_102])).

tff(c_115,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_18,c_111])).

tff(c_66,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_76,plain,(
    ! [B_17] : k3_xboole_0(k1_xboole_0,B_17) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_4])).

tff(c_158,plain,(
    ! [B_24,A_25] :
      ( k9_relat_1(B_24,k3_xboole_0(k1_relat_1(B_24),A_25)) = k9_relat_1(B_24,A_25)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_167,plain,(
    ! [A_25] :
      ( k9_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,A_25)) = k9_relat_1(k1_xboole_0,A_25)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_158])).

tff(c_171,plain,(
    ! [A_25] : k9_relat_1(k1_xboole_0,A_25) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_115,c_76,c_167])).

tff(c_22,plain,(
    k9_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:15:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.18  
% 1.74/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.19  %$ v1_relat_1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.74/1.19  
% 1.74/1.19  %Foreground sorts:
% 1.74/1.19  
% 1.74/1.19  
% 1.74/1.19  %Background operators:
% 1.74/1.19  
% 1.74/1.19  
% 1.74/1.19  %Foreground operators:
% 1.74/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.74/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.74/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.74/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.74/1.19  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.74/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.74/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.74/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.74/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.74/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.74/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.74/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.74/1.19  
% 1.74/1.20  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.74/1.20  tff(f_37, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.74/1.20  tff(f_48, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.74/1.20  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 1.74/1.20  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.74/1.20  tff(f_29, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.74/1.20  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k9_relat_1(B, A) = k9_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_relat_1)).
% 1.74/1.20  tff(f_51, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 1.74/1.20  tff(c_10, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.74/1.20  tff(c_60, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.74/1.20  tff(c_62, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_60])).
% 1.74/1.20  tff(c_18, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.74/1.20  tff(c_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.74/1.20  tff(c_102, plain, (![A_19]: (k9_relat_1(A_19, k1_relat_1(A_19))=k2_relat_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.74/1.20  tff(c_111, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_102])).
% 1.74/1.20  tff(c_115, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_62, c_18, c_111])).
% 1.74/1.20  tff(c_66, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.74/1.20  tff(c_4, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.74/1.20  tff(c_76, plain, (![B_17]: (k3_xboole_0(k1_xboole_0, B_17)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_66, c_4])).
% 1.74/1.20  tff(c_158, plain, (![B_24, A_25]: (k9_relat_1(B_24, k3_xboole_0(k1_relat_1(B_24), A_25))=k9_relat_1(B_24, A_25) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.74/1.20  tff(c_167, plain, (![A_25]: (k9_relat_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, A_25))=k9_relat_1(k1_xboole_0, A_25) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_158])).
% 1.74/1.20  tff(c_171, plain, (![A_25]: (k9_relat_1(k1_xboole_0, A_25)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_115, c_76, c_167])).
% 1.74/1.20  tff(c_22, plain, (k9_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.74/1.20  tff(c_227, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_171, c_22])).
% 1.74/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.20  
% 1.74/1.20  Inference rules
% 1.74/1.20  ----------------------
% 1.74/1.20  #Ref     : 0
% 1.74/1.20  #Sup     : 52
% 1.74/1.20  #Fact    : 0
% 1.74/1.20  #Define  : 0
% 1.74/1.20  #Split   : 0
% 1.74/1.20  #Chain   : 0
% 1.74/1.20  #Close   : 0
% 1.74/1.20  
% 1.74/1.20  Ordering : KBO
% 1.74/1.20  
% 1.74/1.20  Simplification rules
% 1.74/1.20  ----------------------
% 1.74/1.20  #Subsume      : 0
% 1.74/1.20  #Demod        : 31
% 1.74/1.20  #Tautology    : 42
% 1.74/1.20  #SimpNegUnit  : 0
% 1.74/1.20  #BackRed      : 1
% 1.74/1.20  
% 1.74/1.20  #Partial instantiations: 0
% 1.74/1.20  #Strategies tried      : 1
% 1.74/1.20  
% 1.74/1.20  Timing (in seconds)
% 1.74/1.20  ----------------------
% 1.74/1.20  Preprocessing        : 0.27
% 1.74/1.20  Parsing              : 0.15
% 1.74/1.20  CNF conversion       : 0.02
% 1.74/1.20  Main loop            : 0.17
% 1.74/1.20  Inferencing          : 0.07
% 1.74/1.20  Reduction            : 0.06
% 1.74/1.20  Demodulation         : 0.05
% 1.74/1.20  BG Simplification    : 0.01
% 1.74/1.20  Subsumption          : 0.02
% 1.74/1.20  Abstraction          : 0.01
% 1.74/1.20  MUC search           : 0.00
% 1.74/1.20  Cooper               : 0.00
% 1.74/1.20  Total                : 0.46
% 1.74/1.20  Index Insertion      : 0.00
% 1.74/1.20  Index Deletion       : 0.00
% 1.74/1.20  Index Matching       : 0.00
% 1.74/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
