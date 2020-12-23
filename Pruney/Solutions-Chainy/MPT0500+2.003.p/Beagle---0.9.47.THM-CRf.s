%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:47 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   27 (  28 expanded)
%              Number of leaves         :   20 (  21 expanded)
%              Depth                    :    4
%              Number of atoms          :   17 (  19 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k3_xboole_0(B,k2_zfmisc_1(A,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_88,plain,(
    ! [B_34,A_35] :
      ( k3_xboole_0(B_34,k2_zfmisc_1(A_35,k2_relat_1(B_34))) = k7_relat_1(B_34,A_35)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    ! [A_19] :
      ( k3_xboole_0(A_19,k2_zfmisc_1(k1_relat_1(A_19),k2_relat_1(A_19))) = A_19
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_107,plain,(
    ! [B_36] :
      ( k7_relat_1(B_36,k1_relat_1(B_36)) = B_36
      | ~ v1_relat_1(B_36)
      | ~ v1_relat_1(B_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_14])).

tff(c_18,plain,(
    k7_relat_1('#skF_1',k1_relat_1('#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_113,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_18])).

tff(c_121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_113])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:09:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.20  
% 1.74/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.21  %$ v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_1
% 1.74/1.21  
% 1.74/1.21  %Foreground sorts:
% 1.74/1.21  
% 1.74/1.21  
% 1.74/1.21  %Background operators:
% 1.74/1.21  
% 1.74/1.21  
% 1.74/1.21  %Foreground operators:
% 1.74/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.74/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.74/1.21  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.74/1.21  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.74/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.74/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.74/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.74/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.74/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.74/1.21  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.74/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.74/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.74/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.74/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.74/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.74/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.74/1.21  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.74/1.21  
% 1.74/1.21  tff(f_50, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 1.74/1.21  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k3_xboole_0(B, k2_zfmisc_1(A, k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_relat_1)).
% 1.74/1.21  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 1.74/1.21  tff(c_20, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.74/1.21  tff(c_88, plain, (![B_34, A_35]: (k3_xboole_0(B_34, k2_zfmisc_1(A_35, k2_relat_1(B_34)))=k7_relat_1(B_34, A_35) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.74/1.21  tff(c_14, plain, (![A_19]: (k3_xboole_0(A_19, k2_zfmisc_1(k1_relat_1(A_19), k2_relat_1(A_19)))=A_19 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.74/1.21  tff(c_107, plain, (![B_36]: (k7_relat_1(B_36, k1_relat_1(B_36))=B_36 | ~v1_relat_1(B_36) | ~v1_relat_1(B_36))), inference(superposition, [status(thm), theory('equality')], [c_88, c_14])).
% 1.74/1.21  tff(c_18, plain, (k7_relat_1('#skF_1', k1_relat_1('#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.74/1.21  tff(c_113, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_107, c_18])).
% 1.74/1.21  tff(c_121, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_113])).
% 1.74/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.21  
% 1.74/1.21  Inference rules
% 1.74/1.21  ----------------------
% 1.74/1.21  #Ref     : 0
% 1.74/1.21  #Sup     : 24
% 1.74/1.21  #Fact    : 0
% 1.74/1.21  #Define  : 0
% 1.74/1.21  #Split   : 0
% 1.74/1.21  #Chain   : 0
% 1.74/1.21  #Close   : 0
% 1.74/1.21  
% 1.74/1.21  Ordering : KBO
% 1.74/1.21  
% 1.74/1.21  Simplification rules
% 1.74/1.21  ----------------------
% 1.74/1.21  #Subsume      : 0
% 1.74/1.21  #Demod        : 2
% 1.74/1.21  #Tautology    : 16
% 1.74/1.21  #SimpNegUnit  : 0
% 1.74/1.21  #BackRed      : 0
% 1.74/1.21  
% 1.74/1.21  #Partial instantiations: 0
% 1.74/1.21  #Strategies tried      : 1
% 1.74/1.21  
% 1.74/1.21  Timing (in seconds)
% 1.74/1.21  ----------------------
% 1.74/1.22  Preprocessing        : 0.26
% 1.74/1.22  Parsing              : 0.14
% 1.74/1.22  CNF conversion       : 0.02
% 1.74/1.22  Main loop            : 0.10
% 1.74/1.22  Inferencing          : 0.05
% 1.74/1.22  Reduction            : 0.03
% 1.74/1.22  Demodulation         : 0.02
% 1.74/1.22  BG Simplification    : 0.01
% 1.84/1.22  Subsumption          : 0.01
% 1.84/1.22  Abstraction          : 0.01
% 1.84/1.22  MUC search           : 0.00
% 1.84/1.22  Cooper               : 0.00
% 1.84/1.22  Total                : 0.38
% 1.84/1.22  Index Insertion      : 0.00
% 1.84/1.22  Index Deletion       : 0.00
% 1.84/1.22  Index Matching       : 0.00
% 1.84/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
