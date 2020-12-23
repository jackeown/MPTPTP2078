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
% DateTime   : Thu Dec  3 10:00:43 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   34 (  34 expanded)
%              Number of leaves         :   21 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  31 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k6_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_56,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_44,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_59,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_22,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_29,plain,(
    ! [A_14] : v1_relat_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_31,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_29])).

tff(c_174,plain,(
    ! [A_38,B_39,C_40] :
      ( r2_hidden(k4_tarski('#skF_2'(A_38,B_39,C_40),A_38),C_40)
      | ~ r2_hidden(A_38,k9_relat_1(C_40,B_39))
      | ~ v1_relat_1(C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_54,plain,(
    ! [A_17,B_18] : ~ r2_hidden(A_17,k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_60,plain,(
    ! [A_3] : ~ r2_hidden(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_54])).

tff(c_186,plain,(
    ! [A_38,B_39] :
      ( ~ r2_hidden(A_38,k9_relat_1(k1_xboole_0,B_39))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_174,c_60])).

tff(c_192,plain,(
    ! [A_41,B_42] : ~ r2_hidden(A_41,k9_relat_1(k1_xboole_0,B_42)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_186])).

tff(c_215,plain,(
    ! [B_42] : k9_relat_1(k1_xboole_0,B_42) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_192])).

tff(c_24,plain,(
    k9_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_220,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:02:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.31  
% 2.02/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.31  %$ r2_hidden > v1_relat_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k6_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.02/1.31  
% 2.02/1.31  %Foreground sorts:
% 2.02/1.31  
% 2.02/1.31  
% 2.02/1.31  %Background operators:
% 2.02/1.31  
% 2.02/1.31  
% 2.02/1.31  %Foreground operators:
% 2.02/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.31  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.02/1.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.02/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.31  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.02/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.02/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.02/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.02/1.31  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.02/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.02/1.32  
% 2.02/1.32  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.02/1.32  tff(f_56, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.02/1.32  tff(f_44, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.02/1.32  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 2.02/1.32  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.02/1.32  tff(f_42, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.02/1.32  tff(f_59, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 2.02/1.32  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.02/1.32  tff(c_22, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.02/1.32  tff(c_29, plain, (![A_14]: (v1_relat_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.02/1.32  tff(c_31, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_22, c_29])).
% 2.02/1.32  tff(c_174, plain, (![A_38, B_39, C_40]: (r2_hidden(k4_tarski('#skF_2'(A_38, B_39, C_40), A_38), C_40) | ~r2_hidden(A_38, k9_relat_1(C_40, B_39)) | ~v1_relat_1(C_40))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.02/1.32  tff(c_6, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.02/1.32  tff(c_54, plain, (![A_17, B_18]: (~r2_hidden(A_17, k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.02/1.32  tff(c_60, plain, (![A_3]: (~r2_hidden(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_54])).
% 2.02/1.32  tff(c_186, plain, (![A_38, B_39]: (~r2_hidden(A_38, k9_relat_1(k1_xboole_0, B_39)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_174, c_60])).
% 2.02/1.32  tff(c_192, plain, (![A_41, B_42]: (~r2_hidden(A_41, k9_relat_1(k1_xboole_0, B_42)))), inference(demodulation, [status(thm), theory('equality')], [c_31, c_186])).
% 2.02/1.32  tff(c_215, plain, (![B_42]: (k9_relat_1(k1_xboole_0, B_42)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_192])).
% 2.02/1.32  tff(c_24, plain, (k9_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.02/1.32  tff(c_220, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_215, c_24])).
% 2.02/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.32  
% 2.02/1.32  Inference rules
% 2.02/1.32  ----------------------
% 2.02/1.32  #Ref     : 0
% 2.02/1.32  #Sup     : 43
% 2.02/1.32  #Fact    : 0
% 2.02/1.32  #Define  : 0
% 2.02/1.32  #Split   : 0
% 2.02/1.32  #Chain   : 0
% 2.02/1.32  #Close   : 0
% 2.02/1.32  
% 2.02/1.32  Ordering : KBO
% 2.02/1.32  
% 2.02/1.32  Simplification rules
% 2.02/1.32  ----------------------
% 2.02/1.32  #Subsume      : 11
% 2.02/1.32  #Demod        : 12
% 2.02/1.32  #Tautology    : 19
% 2.02/1.32  #SimpNegUnit  : 0
% 2.02/1.32  #BackRed      : 2
% 2.02/1.32  
% 2.02/1.32  #Partial instantiations: 0
% 2.02/1.32  #Strategies tried      : 1
% 2.02/1.32  
% 2.02/1.32  Timing (in seconds)
% 2.02/1.32  ----------------------
% 2.10/1.33  Preprocessing        : 0.30
% 2.10/1.33  Parsing              : 0.16
% 2.10/1.33  CNF conversion       : 0.02
% 2.10/1.33  Main loop            : 0.16
% 2.10/1.33  Inferencing          : 0.07
% 2.10/1.33  Reduction            : 0.04
% 2.10/1.33  Demodulation         : 0.03
% 2.10/1.33  BG Simplification    : 0.01
% 2.10/1.33  Subsumption          : 0.03
% 2.10/1.33  Abstraction          : 0.01
% 2.10/1.33  MUC search           : 0.00
% 2.10/1.33  Cooper               : 0.00
% 2.10/1.33  Total                : 0.49
% 2.10/1.33  Index Insertion      : 0.00
% 2.10/1.33  Index Deletion       : 0.00
% 2.10/1.33  Index Matching       : 0.00
% 2.10/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
