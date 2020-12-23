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
% DateTime   : Thu Dec  3 10:00:34 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   41 (  42 expanded)
%              Number of leaves         :   28 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 (  43 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > v1_relat_1 > k5_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k2_xboole_0 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k9_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_54,axiom,(
    ! [A] :
      ( r1_setfam_1(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_setfam_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( r2_hidden('#skF_1'(A_15,B_16),A_15)
      | r1_setfam_1(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_108,plain,(
    ! [A_67,B_68,C_69] :
      ( r2_hidden('#skF_3'(A_67,B_68,C_69),B_68)
      | ~ r2_hidden(A_67,k9_relat_1(C_69,B_68))
      | ~ v1_relat_1(C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_45,plain,(
    ! [A_41,B_42] :
      ( k2_xboole_0(k1_tarski(A_41),B_42) = B_42
      | ~ r2_hidden(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_13,B_14] : k2_xboole_0(k1_tarski(A_13),B_14) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_50,plain,(
    ! [B_42,A_41] :
      ( k1_xboole_0 != B_42
      | ~ r2_hidden(A_41,B_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_10])).

tff(c_117,plain,(
    ! [B_70,A_71,C_72] :
      ( k1_xboole_0 != B_70
      | ~ r2_hidden(A_71,k9_relat_1(C_72,B_70))
      | ~ v1_relat_1(C_72) ) ),
    inference(resolution,[status(thm)],[c_108,c_50])).

tff(c_134,plain,(
    ! [B_73,C_74,B_75] :
      ( k1_xboole_0 != B_73
      | ~ v1_relat_1(C_74)
      | r1_setfam_1(k9_relat_1(C_74,B_73),B_75) ) ),
    inference(resolution,[status(thm)],[c_18,c_117])).

tff(c_20,plain,(
    ! [A_27] :
      ( k1_xboole_0 = A_27
      | ~ r1_setfam_1(A_27,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_155,plain,(
    ! [C_79,B_80] :
      ( k9_relat_1(C_79,B_80) = k1_xboole_0
      | k1_xboole_0 != B_80
      | ~ v1_relat_1(C_79) ) ),
    inference(resolution,[status(thm)],[c_134,c_20])).

tff(c_159,plain,(
    k9_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_155])).

tff(c_30,plain,(
    k9_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:04:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.21  
% 1.99/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.21  %$ r2_hidden > r1_tarski > r1_setfam_1 > v1_relat_1 > k5_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k2_xboole_0 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.99/1.21  
% 1.99/1.21  %Foreground sorts:
% 1.99/1.21  
% 1.99/1.21  
% 1.99/1.21  %Background operators:
% 1.99/1.21  
% 1.99/1.21  
% 1.99/1.21  %Foreground operators:
% 1.99/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.21  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.99/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.99/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.99/1.21  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.99/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.99/1.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.99/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.99/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.99/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.99/1.21  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.99/1.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.99/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.99/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.99/1.21  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.99/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.99/1.21  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.99/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.99/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.99/1.21  
% 1.99/1.22  tff(f_70, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_relat_1)).
% 1.99/1.22  tff(f_50, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 1.99/1.22  tff(f_65, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 1.99/1.22  tff(f_35, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 1.99/1.22  tff(f_38, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.99/1.22  tff(f_54, axiom, (![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_setfam_1)).
% 1.99/1.22  tff(c_32, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.99/1.22  tff(c_18, plain, (![A_15, B_16]: (r2_hidden('#skF_1'(A_15, B_16), A_15) | r1_setfam_1(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.99/1.22  tff(c_108, plain, (![A_67, B_68, C_69]: (r2_hidden('#skF_3'(A_67, B_68, C_69), B_68) | ~r2_hidden(A_67, k9_relat_1(C_69, B_68)) | ~v1_relat_1(C_69))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.99/1.22  tff(c_45, plain, (![A_41, B_42]: (k2_xboole_0(k1_tarski(A_41), B_42)=B_42 | ~r2_hidden(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.99/1.22  tff(c_10, plain, (![A_13, B_14]: (k2_xboole_0(k1_tarski(A_13), B_14)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.99/1.22  tff(c_50, plain, (![B_42, A_41]: (k1_xboole_0!=B_42 | ~r2_hidden(A_41, B_42))), inference(superposition, [status(thm), theory('equality')], [c_45, c_10])).
% 1.99/1.22  tff(c_117, plain, (![B_70, A_71, C_72]: (k1_xboole_0!=B_70 | ~r2_hidden(A_71, k9_relat_1(C_72, B_70)) | ~v1_relat_1(C_72))), inference(resolution, [status(thm)], [c_108, c_50])).
% 1.99/1.22  tff(c_134, plain, (![B_73, C_74, B_75]: (k1_xboole_0!=B_73 | ~v1_relat_1(C_74) | r1_setfam_1(k9_relat_1(C_74, B_73), B_75))), inference(resolution, [status(thm)], [c_18, c_117])).
% 1.99/1.22  tff(c_20, plain, (![A_27]: (k1_xboole_0=A_27 | ~r1_setfam_1(A_27, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.99/1.22  tff(c_155, plain, (![C_79, B_80]: (k9_relat_1(C_79, B_80)=k1_xboole_0 | k1_xboole_0!=B_80 | ~v1_relat_1(C_79))), inference(resolution, [status(thm)], [c_134, c_20])).
% 1.99/1.22  tff(c_159, plain, (k9_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_155])).
% 1.99/1.22  tff(c_30, plain, (k9_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.99/1.22  tff(c_162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_159, c_30])).
% 1.99/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.22  
% 1.99/1.22  Inference rules
% 1.99/1.22  ----------------------
% 1.99/1.22  #Ref     : 0
% 1.99/1.22  #Sup     : 26
% 1.99/1.22  #Fact    : 0
% 1.99/1.22  #Define  : 0
% 1.99/1.22  #Split   : 0
% 1.99/1.22  #Chain   : 0
% 1.99/1.22  #Close   : 0
% 1.99/1.22  
% 1.99/1.22  Ordering : KBO
% 1.99/1.22  
% 1.99/1.22  Simplification rules
% 1.99/1.22  ----------------------
% 1.99/1.22  #Subsume      : 3
% 1.99/1.22  #Demod        : 1
% 1.99/1.22  #Tautology    : 7
% 1.99/1.22  #SimpNegUnit  : 0
% 1.99/1.22  #BackRed      : 1
% 1.99/1.22  
% 1.99/1.22  #Partial instantiations: 0
% 1.99/1.22  #Strategies tried      : 1
% 1.99/1.22  
% 1.99/1.22  Timing (in seconds)
% 1.99/1.22  ----------------------
% 2.08/1.23  Preprocessing        : 0.31
% 2.08/1.23  Parsing              : 0.16
% 2.08/1.23  CNF conversion       : 0.02
% 2.08/1.23  Main loop            : 0.15
% 2.08/1.23  Inferencing          : 0.06
% 2.08/1.23  Reduction            : 0.04
% 2.08/1.23  Demodulation         : 0.03
% 2.08/1.23  BG Simplification    : 0.01
% 2.08/1.23  Subsumption          : 0.03
% 2.08/1.23  Abstraction          : 0.01
% 2.08/1.23  MUC search           : 0.00
% 2.08/1.23  Cooper               : 0.00
% 2.08/1.23  Total                : 0.49
% 2.08/1.23  Index Insertion      : 0.00
% 2.08/1.23  Index Deletion       : 0.00
% 2.08/1.23  Index Matching       : 0.00
% 2.08/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
