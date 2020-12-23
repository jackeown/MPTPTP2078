%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:41 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   34 (  39 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  39 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_6 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_57,plain,(
    ! [A_36] :
      ( r2_hidden('#skF_2'(A_36),A_36)
      | v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_49,plain,(
    ! [A_33,B_34] : ~ r2_hidden(A_33,k2_zfmisc_1(A_33,B_34)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_52,plain,(
    ! [A_3] : ~ r2_hidden(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_49])).

tff(c_62,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_57,c_52])).

tff(c_286,plain,(
    ! [A_70,B_71,C_72] :
      ( r2_hidden(k4_tarski('#skF_5'(A_70,B_71,C_72),A_70),C_72)
      | ~ r2_hidden(A_70,k9_relat_1(C_72,B_71))
      | ~ v1_relat_1(C_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_298,plain,(
    ! [A_70,B_71] :
      ( ~ r2_hidden(A_70,k9_relat_1(k1_xboole_0,B_71))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_286,c_52])).

tff(c_304,plain,(
    ! [A_73,B_74] : ~ r2_hidden(A_73,k9_relat_1(k1_xboole_0,B_74)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_298])).

tff(c_331,plain,(
    ! [B_74] : k9_relat_1(k1_xboole_0,B_74) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_304])).

tff(c_26,plain,(
    k9_relat_1(k1_xboole_0,'#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_337,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.08/0.27  % Computer   : n016.cluster.edu
% 0.08/0.27  % Model      : x86_64 x86_64
% 0.08/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.27  % Memory     : 8042.1875MB
% 0.08/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.27  % CPULimit   : 60
% 0.08/0.27  % DateTime   : Tue Dec  1 11:06:04 EST 2020
% 0.08/0.27  % CPUTime    : 
% 0.08/0.27  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.08  
% 1.80/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.08  %$ r2_hidden > v1_relat_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_3 > #skF_6 > #skF_5 > #skF_4
% 1.80/1.08  
% 1.80/1.08  %Foreground sorts:
% 1.80/1.08  
% 1.80/1.08  
% 1.80/1.08  %Background operators:
% 1.80/1.08  
% 1.80/1.08  
% 1.80/1.08  %Foreground operators:
% 1.80/1.08  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.80/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.80/1.08  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.80/1.08  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.80/1.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.80/1.08  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.80/1.08  tff('#skF_6', type, '#skF_6': $i).
% 1.80/1.08  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 1.80/1.08  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.80/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.80/1.08  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.80/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.80/1.08  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.80/1.08  
% 1.89/1.09  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.89/1.09  tff(f_52, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 1.89/1.09  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.89/1.09  tff(f_42, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.89/1.09  tff(f_63, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 1.89/1.09  tff(f_66, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 1.89/1.09  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.89/1.09  tff(c_57, plain, (![A_36]: (r2_hidden('#skF_2'(A_36), A_36) | v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.89/1.09  tff(c_6, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.89/1.09  tff(c_49, plain, (![A_33, B_34]: (~r2_hidden(A_33, k2_zfmisc_1(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.89/1.09  tff(c_52, plain, (![A_3]: (~r2_hidden(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_49])).
% 1.89/1.09  tff(c_62, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_57, c_52])).
% 1.89/1.09  tff(c_286, plain, (![A_70, B_71, C_72]: (r2_hidden(k4_tarski('#skF_5'(A_70, B_71, C_72), A_70), C_72) | ~r2_hidden(A_70, k9_relat_1(C_72, B_71)) | ~v1_relat_1(C_72))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.89/1.09  tff(c_298, plain, (![A_70, B_71]: (~r2_hidden(A_70, k9_relat_1(k1_xboole_0, B_71)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_286, c_52])).
% 1.89/1.09  tff(c_304, plain, (![A_73, B_74]: (~r2_hidden(A_73, k9_relat_1(k1_xboole_0, B_74)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_298])).
% 1.89/1.09  tff(c_331, plain, (![B_74]: (k9_relat_1(k1_xboole_0, B_74)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_304])).
% 1.89/1.09  tff(c_26, plain, (k9_relat_1(k1_xboole_0, '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.89/1.09  tff(c_337, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_331, c_26])).
% 1.89/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.09  
% 1.89/1.09  Inference rules
% 1.89/1.09  ----------------------
% 1.89/1.09  #Ref     : 1
% 1.89/1.09  #Sup     : 69
% 1.89/1.09  #Fact    : 0
% 1.89/1.09  #Define  : 0
% 1.89/1.09  #Split   : 0
% 1.89/1.09  #Chain   : 0
% 1.89/1.09  #Close   : 0
% 1.89/1.09  
% 1.89/1.09  Ordering : KBO
% 1.89/1.09  
% 1.89/1.09  Simplification rules
% 1.89/1.09  ----------------------
% 1.89/1.09  #Subsume      : 21
% 1.89/1.09  #Demod        : 21
% 1.89/1.09  #Tautology    : 30
% 1.89/1.09  #SimpNegUnit  : 0
% 1.89/1.09  #BackRed      : 2
% 1.89/1.09  
% 1.89/1.09  #Partial instantiations: 0
% 1.89/1.09  #Strategies tried      : 1
% 1.89/1.09  
% 1.89/1.09  Timing (in seconds)
% 1.89/1.09  ----------------------
% 1.89/1.09  Preprocessing        : 0.28
% 1.89/1.09  Parsing              : 0.16
% 1.89/1.10  CNF conversion       : 0.02
% 1.89/1.10  Main loop            : 0.19
% 1.89/1.10  Inferencing          : 0.08
% 1.89/1.10  Reduction            : 0.05
% 1.89/1.10  Demodulation         : 0.03
% 1.89/1.10  BG Simplification    : 0.01
% 1.89/1.10  Subsumption          : 0.04
% 1.89/1.10  Abstraction          : 0.01
% 1.89/1.10  MUC search           : 0.00
% 1.89/1.10  Cooper               : 0.00
% 1.89/1.10  Total                : 0.50
% 1.89/1.10  Index Insertion      : 0.00
% 1.89/1.10  Index Deletion       : 0.00
% 1.89/1.10  Index Matching       : 0.00
% 1.89/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
