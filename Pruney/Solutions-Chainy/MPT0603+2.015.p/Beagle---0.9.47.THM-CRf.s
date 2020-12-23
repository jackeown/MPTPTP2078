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
% DateTime   : Thu Dec  3 10:02:25 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   35 (  39 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   33 (  43 expanded)
%              Number of equality atoms :   19 (  22 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_xboole_0(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k3_xboole_0(B,k2_zfmisc_1(A,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_88,plain,(
    ! [B_24,A_25] :
      ( k3_xboole_0(B_24,k2_zfmisc_1(A_25,k2_relat_1(B_24))) = k7_relat_1(B_24,A_25)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_98,plain,(
    ! [B_24] :
      ( k7_relat_1(B_24,k1_xboole_0) = k3_xboole_0(B_24,k1_xboole_0)
      | ~ v1_relat_1(B_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_88])).

tff(c_102,plain,(
    ! [B_26] :
      ( k7_relat_1(B_26,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_98])).

tff(c_106,plain,(
    k7_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_102])).

tff(c_22,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_64,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,B_21) = k1_xboole_0
      | ~ r1_xboole_0(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_72,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_64])).

tff(c_111,plain,(
    ! [C_27,A_28,B_29] :
      ( k7_relat_1(k7_relat_1(C_27,A_28),B_29) = k7_relat_1(C_27,k3_xboole_0(A_28,B_29))
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_120,plain,
    ( k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_20])).

tff(c_133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_106,c_72,c_120])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:42:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.20  
% 1.81/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.21  %$ r1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.81/1.21  
% 1.81/1.21  %Foreground sorts:
% 1.81/1.21  
% 1.81/1.21  
% 1.81/1.21  %Background operators:
% 1.81/1.21  
% 1.81/1.21  
% 1.81/1.21  %Foreground operators:
% 1.81/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.21  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.81/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.81/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.81/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.81/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.81/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.81/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.81/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.81/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.81/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.81/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.81/1.21  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.81/1.21  
% 1.81/1.22  tff(f_54, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 1.81/1.22  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 1.81/1.22  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.81/1.22  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k3_xboole_0(B, k2_zfmisc_1(A, k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_relat_1)).
% 1.81/1.22  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.81/1.22  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 1.81/1.22  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.81/1.22  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.81/1.22  tff(c_12, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.81/1.22  tff(c_88, plain, (![B_24, A_25]: (k3_xboole_0(B_24, k2_zfmisc_1(A_25, k2_relat_1(B_24)))=k7_relat_1(B_24, A_25) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.81/1.22  tff(c_98, plain, (![B_24]: (k7_relat_1(B_24, k1_xboole_0)=k3_xboole_0(B_24, k1_xboole_0) | ~v1_relat_1(B_24))), inference(superposition, [status(thm), theory('equality')], [c_12, c_88])).
% 1.81/1.22  tff(c_102, plain, (![B_26]: (k7_relat_1(B_26, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_26))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_98])).
% 1.81/1.22  tff(c_106, plain, (k7_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_102])).
% 1.81/1.22  tff(c_22, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.81/1.22  tff(c_64, plain, (![A_20, B_21]: (k3_xboole_0(A_20, B_21)=k1_xboole_0 | ~r1_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.81/1.22  tff(c_72, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_64])).
% 1.81/1.22  tff(c_111, plain, (![C_27, A_28, B_29]: (k7_relat_1(k7_relat_1(C_27, A_28), B_29)=k7_relat_1(C_27, k3_xboole_0(A_28, B_29)) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.81/1.22  tff(c_20, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.81/1.22  tff(c_120, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_111, c_20])).
% 1.81/1.22  tff(c_133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_106, c_72, c_120])).
% 1.81/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.22  
% 1.81/1.22  Inference rules
% 1.81/1.22  ----------------------
% 1.81/1.22  #Ref     : 0
% 1.81/1.22  #Sup     : 28
% 1.81/1.22  #Fact    : 0
% 1.81/1.22  #Define  : 0
% 1.81/1.22  #Split   : 0
% 1.81/1.22  #Chain   : 0
% 1.81/1.22  #Close   : 0
% 1.81/1.22  
% 1.81/1.22  Ordering : KBO
% 1.81/1.22  
% 1.81/1.22  Simplification rules
% 1.81/1.22  ----------------------
% 1.81/1.22  #Subsume      : 0
% 1.81/1.22  #Demod        : 4
% 1.81/1.22  #Tautology    : 20
% 1.81/1.22  #SimpNegUnit  : 0
% 1.81/1.22  #BackRed      : 0
% 1.81/1.22  
% 1.81/1.22  #Partial instantiations: 0
% 1.81/1.22  #Strategies tried      : 1
% 1.81/1.22  
% 1.81/1.22  Timing (in seconds)
% 1.81/1.22  ----------------------
% 1.81/1.22  Preprocessing        : 0.30
% 1.81/1.22  Parsing              : 0.17
% 1.81/1.22  CNF conversion       : 0.02
% 1.81/1.22  Main loop            : 0.12
% 1.81/1.22  Inferencing          : 0.05
% 1.81/1.22  Reduction            : 0.03
% 1.81/1.22  Demodulation         : 0.03
% 1.81/1.22  BG Simplification    : 0.01
% 1.81/1.22  Subsumption          : 0.02
% 1.81/1.22  Abstraction          : 0.01
% 1.81/1.22  MUC search           : 0.00
% 1.81/1.22  Cooper               : 0.00
% 1.81/1.22  Total                : 0.44
% 1.81/1.22  Index Insertion      : 0.00
% 1.81/1.22  Index Deletion       : 0.00
% 1.81/1.22  Index Matching       : 0.00
% 1.81/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
