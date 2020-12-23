%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:28 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   31 (  31 expanded)
%              Number of leaves         :   20 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   27 (  27 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_55,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_16,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_1'(A_6),A_6)
      | v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_44,plain,(
    ! [A_29,B_30] : ~ r2_hidden(A_29,k2_zfmisc_1(A_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_52,plain,(
    ! [A_32] : ~ r2_hidden(A_32,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_44])).

tff(c_57,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_52])).

tff(c_58,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(k8_relat_1(A_33,B_34),B_34)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_62,plain,(
    ! [A_33] :
      ( k8_relat_1(A_33,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_58,c_2])).

tff(c_65,plain,(
    ! [A_33] : k8_relat_1(A_33,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_62])).

tff(c_20,plain,(
    k8_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_68,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 18:56:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.18  
% 1.73/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.19  %$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.73/1.19  
% 1.73/1.19  %Foreground sorts:
% 1.73/1.19  
% 1.73/1.19  
% 1.73/1.19  %Background operators:
% 1.73/1.19  
% 1.73/1.19  
% 1.73/1.19  %Foreground operators:
% 1.73/1.19  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.73/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.73/1.19  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.73/1.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.73/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.73/1.19  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.73/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.73/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.73/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.73/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.73/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.19  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.73/1.19  
% 1.73/1.20  tff(f_48, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 1.73/1.20  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.73/1.20  tff(f_38, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.73/1.20  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 1.73/1.20  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.73/1.20  tff(f_55, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_relat_1)).
% 1.73/1.20  tff(c_16, plain, (![A_6]: (r2_hidden('#skF_1'(A_6), A_6) | v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.73/1.20  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.73/1.20  tff(c_44, plain, (![A_29, B_30]: (~r2_hidden(A_29, k2_zfmisc_1(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.73/1.20  tff(c_52, plain, (![A_32]: (~r2_hidden(A_32, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_44])).
% 1.73/1.20  tff(c_57, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_52])).
% 1.73/1.20  tff(c_58, plain, (![A_33, B_34]: (r1_tarski(k8_relat_1(A_33, B_34), B_34) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.73/1.20  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.73/1.20  tff(c_62, plain, (![A_33]: (k8_relat_1(A_33, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_58, c_2])).
% 1.73/1.20  tff(c_65, plain, (![A_33]: (k8_relat_1(A_33, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_57, c_62])).
% 1.73/1.20  tff(c_20, plain, (k8_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.73/1.20  tff(c_68, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_65, c_20])).
% 1.73/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.20  
% 1.73/1.20  Inference rules
% 1.73/1.20  ----------------------
% 1.73/1.20  #Ref     : 0
% 1.73/1.20  #Sup     : 10
% 1.73/1.20  #Fact    : 0
% 1.73/1.20  #Define  : 0
% 1.73/1.20  #Split   : 0
% 1.73/1.20  #Chain   : 0
% 1.73/1.20  #Close   : 0
% 1.73/1.20  
% 1.73/1.20  Ordering : KBO
% 1.73/1.20  
% 1.73/1.20  Simplification rules
% 1.73/1.20  ----------------------
% 1.73/1.20  #Subsume      : 1
% 1.73/1.20  #Demod        : 2
% 1.73/1.20  #Tautology    : 6
% 1.73/1.20  #SimpNegUnit  : 0
% 1.73/1.20  #BackRed      : 1
% 1.73/1.20  
% 1.73/1.20  #Partial instantiations: 0
% 1.73/1.20  #Strategies tried      : 1
% 1.73/1.20  
% 1.73/1.20  Timing (in seconds)
% 1.73/1.20  ----------------------
% 1.73/1.21  Preprocessing        : 0.28
% 1.73/1.21  Parsing              : 0.15
% 1.73/1.21  CNF conversion       : 0.02
% 1.73/1.21  Main loop            : 0.08
% 1.73/1.21  Inferencing          : 0.03
% 1.73/1.21  Reduction            : 0.02
% 1.73/1.21  Demodulation         : 0.02
% 1.73/1.21  BG Simplification    : 0.01
% 1.73/1.21  Subsumption          : 0.01
% 1.73/1.21  Abstraction          : 0.00
% 1.73/1.21  MUC search           : 0.00
% 1.73/1.21  Cooper               : 0.00
% 1.73/1.21  Total                : 0.39
% 1.73/1.21  Index Insertion      : 0.00
% 1.73/1.21  Index Deletion       : 0.00
% 1.73/1.21  Index Matching       : 0.00
% 1.73/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
