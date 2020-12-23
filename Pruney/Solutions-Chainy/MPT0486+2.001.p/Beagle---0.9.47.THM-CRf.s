%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:33 EST 2020

% Result     : Theorem 5.62s
% Output     : CNFRefutation 5.62s
% Verified   : 
% Statistics : Number of formulae       :   59 (  68 expanded)
%              Number of leaves         :   47 (  51 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  45 expanded)
%              Number of equality atoms :   13 (  21 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k3_setfam_1 > k2_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_4 > #skF_1 > #skF_3 > #skF_14 > #skF_12 > #skF_10 > #skF_8 > #skF_13 > #skF_2 > #skF_7 > #skF_9 > #skF_5 > #skF_15

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff(k3_setfam_1,type,(
    k3_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_15',type,(
    '#skF_15': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_182,negated_conjecture,(
    k6_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_180,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_59,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_145,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_170,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k6_relat_1(A)
      <=> ! [C,D] :
            ( r2_hidden(k4_tarski(C,D),B)
          <=> ( r2_hidden(C,A)
              & C = D ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_relat_1)).

tff(c_134,plain,(
    k6_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_132,plain,(
    ! [A_147] :
      ( r2_hidden('#skF_13'(A_147),A_147)
      | v1_relat_1(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_26,plain,(
    ! [A_18] : k4_xboole_0(k1_xboole_0,A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_464,plain,(
    ! [B_207,A_208] :
      ( ~ r2_hidden(B_207,A_208)
      | k4_xboole_0(A_208,k1_tarski(B_207)) != A_208 ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_470,plain,(
    ! [B_209] : ~ r2_hidden(B_209,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_464])).

tff(c_481,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_132,c_470])).

tff(c_4584,plain,(
    ! [A_401,B_402] :
      ( r2_hidden('#skF_9'(A_401,B_402),A_401)
      | r2_hidden(k4_tarski('#skF_11'(A_401,B_402),'#skF_12'(A_401,B_402)),B_402)
      | k6_relat_1(A_401) = B_402
      | ~ v1_relat_1(B_402) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_469,plain,(
    ! [B_207] : ~ r2_hidden(B_207,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_464])).

tff(c_4614,plain,(
    ! [A_401] :
      ( r2_hidden('#skF_9'(A_401,k1_xboole_0),A_401)
      | k6_relat_1(A_401) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_4584,c_469])).

tff(c_4630,plain,(
    ! [A_403] :
      ( r2_hidden('#skF_9'(A_403,k1_xboole_0),A_403)
      | k6_relat_1(A_403) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_4614])).

tff(c_4652,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4630,c_469])).

tff(c_4665,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_4652])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n017.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 14:23:01 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.62/2.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.62/2.13  
% 5.62/2.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.62/2.13  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k3_setfam_1 > k2_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_11 > #skF_6 > #skF_4 > #skF_1 > #skF_3 > #skF_14 > #skF_12 > #skF_10 > #skF_8 > #skF_13 > #skF_2 > #skF_7 > #skF_9 > #skF_5 > #skF_15
% 5.62/2.13  
% 5.62/2.13  %Foreground sorts:
% 5.62/2.13  
% 5.62/2.13  
% 5.62/2.13  %Background operators:
% 5.62/2.13  
% 5.62/2.13  
% 5.62/2.13  %Foreground operators:
% 5.62/2.13  tff('#skF_11', type, '#skF_11': ($i * $i) > $i).
% 5.62/2.13  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.62/2.13  tff('#skF_4', type, '#skF_4': $i > $i).
% 5.62/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.62/2.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.62/2.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.62/2.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.62/2.13  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.62/2.13  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.62/2.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.62/2.13  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.62/2.13  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.62/2.13  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.62/2.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.62/2.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.62/2.13  tff('#skF_14', type, '#skF_14': ($i * $i) > $i).
% 5.62/2.13  tff('#skF_12', type, '#skF_12': ($i * $i) > $i).
% 5.62/2.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.62/2.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.62/2.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.62/2.13  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 5.62/2.13  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 5.62/2.13  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 5.62/2.13  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.62/2.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.62/2.13  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.62/2.13  tff('#skF_13', type, '#skF_13': $i > $i).
% 5.62/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.62/2.13  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.62/2.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.62/2.13  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.62/2.13  tff(k3_setfam_1, type, k3_setfam_1: ($i * $i) > $i).
% 5.62/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.62/2.13  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.62/2.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.62/2.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.62/2.13  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 5.62/2.13  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.62/2.13  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 5.62/2.13  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 5.62/2.13  tff('#skF_15', type, '#skF_15': ($i * $i) > $i).
% 5.62/2.13  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.62/2.13  
% 5.62/2.14  tff(f_182, negated_conjecture, ~(k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 5.62/2.14  tff(f_180, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 5.62/2.14  tff(f_59, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 5.62/2.14  tff(f_145, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 5.62/2.14  tff(f_170, axiom, (![A, B]: (v1_relat_1(B) => ((B = k6_relat_1(A)) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), B) <=> (r2_hidden(C, A) & (C = D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_relat_1)).
% 5.62/2.14  tff(c_134, plain, (k6_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_182])).
% 5.62/2.14  tff(c_132, plain, (![A_147]: (r2_hidden('#skF_13'(A_147), A_147) | v1_relat_1(A_147))), inference(cnfTransformation, [status(thm)], [f_180])).
% 5.62/2.14  tff(c_26, plain, (![A_18]: (k4_xboole_0(k1_xboole_0, A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.62/2.14  tff(c_464, plain, (![B_207, A_208]: (~r2_hidden(B_207, A_208) | k4_xboole_0(A_208, k1_tarski(B_207))!=A_208)), inference(cnfTransformation, [status(thm)], [f_145])).
% 5.62/2.14  tff(c_470, plain, (![B_209]: (~r2_hidden(B_209, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_464])).
% 5.62/2.14  tff(c_481, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_132, c_470])).
% 5.62/2.14  tff(c_4584, plain, (![A_401, B_402]: (r2_hidden('#skF_9'(A_401, B_402), A_401) | r2_hidden(k4_tarski('#skF_11'(A_401, B_402), '#skF_12'(A_401, B_402)), B_402) | k6_relat_1(A_401)=B_402 | ~v1_relat_1(B_402))), inference(cnfTransformation, [status(thm)], [f_170])).
% 5.62/2.14  tff(c_469, plain, (![B_207]: (~r2_hidden(B_207, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_464])).
% 5.62/2.14  tff(c_4614, plain, (![A_401]: (r2_hidden('#skF_9'(A_401, k1_xboole_0), A_401) | k6_relat_1(A_401)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_4584, c_469])).
% 5.62/2.14  tff(c_4630, plain, (![A_403]: (r2_hidden('#skF_9'(A_403, k1_xboole_0), A_403) | k6_relat_1(A_403)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_481, c_4614])).
% 5.62/2.14  tff(c_4652, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_4630, c_469])).
% 5.62/2.14  tff(c_4665, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134, c_4652])).
% 5.62/2.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.62/2.14  
% 5.62/2.14  Inference rules
% 5.62/2.14  ----------------------
% 5.62/2.14  #Ref     : 1
% 5.62/2.14  #Sup     : 1083
% 5.62/2.14  #Fact    : 0
% 5.62/2.14  #Define  : 0
% 5.62/2.14  #Split   : 0
% 5.62/2.14  #Chain   : 0
% 5.62/2.14  #Close   : 0
% 5.62/2.14  
% 5.62/2.14  Ordering : KBO
% 5.62/2.14  
% 5.62/2.14  Simplification rules
% 5.62/2.14  ----------------------
% 5.62/2.14  #Subsume      : 99
% 5.62/2.14  #Demod        : 810
% 5.62/2.14  #Tautology    : 652
% 5.62/2.14  #SimpNegUnit  : 39
% 5.62/2.14  #BackRed      : 10
% 5.62/2.14  
% 5.62/2.14  #Partial instantiations: 0
% 5.62/2.14  #Strategies tried      : 1
% 5.62/2.14  
% 5.62/2.14  Timing (in seconds)
% 5.62/2.14  ----------------------
% 5.62/2.14  Preprocessing        : 0.50
% 5.62/2.14  Parsing              : 0.29
% 5.62/2.14  CNF conversion       : 0.03
% 5.62/2.14  Main loop            : 0.83
% 5.62/2.14  Inferencing          : 0.26
% 5.62/2.14  Reduction            : 0.35
% 5.62/2.14  Demodulation         : 0.28
% 5.62/2.14  BG Simplification    : 0.04
% 5.62/2.14  Subsumption          : 0.13
% 5.62/2.14  Abstraction          : 0.05
% 5.62/2.14  MUC search           : 0.00
% 5.62/2.14  Cooper               : 0.00
% 5.62/2.14  Total                : 1.35
% 5.62/2.14  Index Insertion      : 0.00
% 5.62/2.14  Index Deletion       : 0.00
% 5.62/2.14  Index Matching       : 0.00
% 5.62/2.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
