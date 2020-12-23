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
% DateTime   : Thu Dec  3 10:00:47 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   41 (  54 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  59 expanded)
%              Number of equality atoms :   27 (  40 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_48,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k9_relat_1(B,A) = k9_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_relat_1)).

tff(f_55,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_8,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_62,plain,(
    ! [A_16,B_17] : v1_relat_1(k2_zfmisc_1(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_64,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_62])).

tff(c_18,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_20,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_68,plain,(
    ! [A_18] :
      ( k7_relat_1(A_18,k1_relat_1(A_18)) = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_77,plain,
    ( k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_68])).

tff(c_81,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_77])).

tff(c_132,plain,(
    ! [B_24,A_25] :
      ( k2_relat_1(k7_relat_1(B_24,A_25)) = k9_relat_1(B_24,A_25)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_141,plain,
    ( k9_relat_1(k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_132])).

tff(c_148,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_18,c_141])).

tff(c_97,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k4_xboole_0(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_107,plain,(
    ! [B_22] : k3_xboole_0(k1_xboole_0,B_22) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_4])).

tff(c_180,plain,(
    ! [B_28,A_29] :
      ( k9_relat_1(B_28,k3_xboole_0(k1_relat_1(B_28),A_29)) = k9_relat_1(B_28,A_29)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_189,plain,(
    ! [A_29] :
      ( k9_relat_1(k1_xboole_0,k3_xboole_0(k1_xboole_0,A_29)) = k9_relat_1(k1_xboole_0,A_29)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_180])).

tff(c_193,plain,(
    ! [A_29] : k9_relat_1(k1_xboole_0,A_29) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_148,c_107,c_189])).

tff(c_24,plain,(
    k9_relat_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:54:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.23  
% 1.88/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.24  %$ v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.88/1.24  
% 1.88/1.24  %Foreground sorts:
% 1.88/1.24  
% 1.88/1.24  
% 1.88/1.24  %Background operators:
% 1.88/1.24  
% 1.88/1.24  
% 1.88/1.24  %Foreground operators:
% 1.88/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.88/1.24  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.88/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.88/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.88/1.24  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.88/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.88/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.88/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.88/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.88/1.24  
% 1.88/1.25  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.88/1.25  tff(f_37, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.88/1.25  tff(f_48, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.88/1.25  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 1.88/1.25  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.88/1.25  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.88/1.25  tff(f_29, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 1.88/1.25  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k9_relat_1(B, A) = k9_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_relat_1)).
% 1.88/1.25  tff(f_55, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 1.88/1.25  tff(c_8, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.88/1.25  tff(c_62, plain, (![A_16, B_17]: (v1_relat_1(k2_zfmisc_1(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.88/1.25  tff(c_64, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_62])).
% 1.88/1.25  tff(c_18, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.88/1.25  tff(c_20, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.88/1.25  tff(c_68, plain, (![A_18]: (k7_relat_1(A_18, k1_relat_1(A_18))=A_18 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.88/1.25  tff(c_77, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_68])).
% 1.88/1.25  tff(c_81, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_64, c_77])).
% 1.88/1.25  tff(c_132, plain, (![B_24, A_25]: (k2_relat_1(k7_relat_1(B_24, A_25))=k9_relat_1(B_24, A_25) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.88/1.25  tff(c_141, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_81, c_132])).
% 1.88/1.25  tff(c_148, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_64, c_18, c_141])).
% 1.88/1.25  tff(c_97, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k4_xboole_0(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.88/1.25  tff(c_4, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.88/1.25  tff(c_107, plain, (![B_22]: (k3_xboole_0(k1_xboole_0, B_22)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_97, c_4])).
% 1.88/1.25  tff(c_180, plain, (![B_28, A_29]: (k9_relat_1(B_28, k3_xboole_0(k1_relat_1(B_28), A_29))=k9_relat_1(B_28, A_29) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.88/1.25  tff(c_189, plain, (![A_29]: (k9_relat_1(k1_xboole_0, k3_xboole_0(k1_xboole_0, A_29))=k9_relat_1(k1_xboole_0, A_29) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_180])).
% 1.88/1.25  tff(c_193, plain, (![A_29]: (k9_relat_1(k1_xboole_0, A_29)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_148, c_107, c_189])).
% 1.88/1.25  tff(c_24, plain, (k9_relat_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.88/1.25  tff(c_197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_193, c_24])).
% 1.88/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.25  
% 1.88/1.25  Inference rules
% 1.88/1.25  ----------------------
% 1.88/1.25  #Ref     : 0
% 1.88/1.25  #Sup     : 45
% 1.88/1.25  #Fact    : 0
% 1.88/1.25  #Define  : 0
% 1.88/1.25  #Split   : 0
% 1.88/1.25  #Chain   : 0
% 1.88/1.25  #Close   : 0
% 1.88/1.25  
% 1.88/1.25  Ordering : KBO
% 1.88/1.25  
% 1.88/1.25  Simplification rules
% 1.88/1.25  ----------------------
% 1.88/1.25  #Subsume      : 0
% 1.88/1.25  #Demod        : 19
% 1.88/1.25  #Tautology    : 37
% 1.88/1.25  #SimpNegUnit  : 0
% 1.88/1.25  #BackRed      : 1
% 1.88/1.25  
% 1.88/1.25  #Partial instantiations: 0
% 1.88/1.25  #Strategies tried      : 1
% 1.88/1.25  
% 1.88/1.25  Timing (in seconds)
% 1.88/1.25  ----------------------
% 1.88/1.25  Preprocessing        : 0.29
% 1.88/1.25  Parsing              : 0.16
% 1.88/1.25  CNF conversion       : 0.02
% 1.88/1.25  Main loop            : 0.13
% 1.88/1.25  Inferencing          : 0.06
% 1.88/1.25  Reduction            : 0.04
% 1.88/1.25  Demodulation         : 0.03
% 1.88/1.25  BG Simplification    : 0.01
% 1.88/1.25  Subsumption          : 0.02
% 1.88/1.25  Abstraction          : 0.01
% 1.88/1.25  MUC search           : 0.00
% 1.88/1.25  Cooper               : 0.00
% 1.88/1.25  Total                : 0.46
% 1.88/1.25  Index Insertion      : 0.00
% 1.88/1.25  Index Deletion       : 0.00
% 1.88/1.25  Index Matching       : 0.00
% 1.88/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
