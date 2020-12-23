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
% DateTime   : Thu Dec  3 10:01:33 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   38 (  38 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   37 (  37 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_59,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_44,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_58,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_66,plain,(
    ! [A_17,B_18] : ~ r2_hidden(A_17,k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_72,plain,(
    ! [A_3] : ~ r2_hidden(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_66])).

tff(c_26,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_37,plain,(
    ! [A_14] : v1_relat_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_39,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_37])).

tff(c_22,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_109,plain,(
    ! [A_28,B_29,C_30] :
      ( r2_hidden('#skF_2'(A_28,B_29,C_30),k2_relat_1(C_30))
      | ~ r2_hidden(A_28,k10_relat_1(C_30,B_29))
      | ~ v1_relat_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_112,plain,(
    ! [A_28,B_29] :
      ( r2_hidden('#skF_2'(A_28,B_29,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_28,k10_relat_1(k1_xboole_0,B_29))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_109])).

tff(c_114,plain,(
    ! [A_28,B_29] :
      ( r2_hidden('#skF_2'(A_28,B_29,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_28,k10_relat_1(k1_xboole_0,B_29)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_112])).

tff(c_116,plain,(
    ! [A_31,B_32] : ~ r2_hidden(A_31,k10_relat_1(k1_xboole_0,B_32)) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_114])).

tff(c_126,plain,(
    ! [B_32] : k10_relat_1(k1_xboole_0,B_32) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_116])).

tff(c_28,plain,(
    k10_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:41:46 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.11  
% 1.71/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.12  %$ r2_hidden > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.71/1.12  
% 1.71/1.12  %Foreground sorts:
% 1.71/1.12  
% 1.71/1.12  
% 1.71/1.12  %Background operators:
% 1.71/1.12  
% 1.71/1.12  
% 1.71/1.12  %Foreground operators:
% 1.71/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.71/1.12  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.71/1.12  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.71/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.71/1.12  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.71/1.12  tff('#skF_3', type, '#skF_3': $i).
% 1.71/1.12  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.71/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.12  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.71/1.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.71/1.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.71/1.12  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.71/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.71/1.12  
% 1.71/1.13  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.71/1.13  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.71/1.13  tff(f_42, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.71/1.13  tff(f_59, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 1.71/1.13  tff(f_44, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.71/1.13  tff(f_58, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.71/1.13  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 1.71/1.13  tff(f_62, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 1.71/1.13  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.71/1.13  tff(c_6, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.71/1.13  tff(c_66, plain, (![A_17, B_18]: (~r2_hidden(A_17, k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.71/1.13  tff(c_72, plain, (![A_3]: (~r2_hidden(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_66])).
% 1.71/1.13  tff(c_26, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.71/1.13  tff(c_37, plain, (![A_14]: (v1_relat_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.71/1.13  tff(c_39, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_37])).
% 1.71/1.13  tff(c_22, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.71/1.13  tff(c_109, plain, (![A_28, B_29, C_30]: (r2_hidden('#skF_2'(A_28, B_29, C_30), k2_relat_1(C_30)) | ~r2_hidden(A_28, k10_relat_1(C_30, B_29)) | ~v1_relat_1(C_30))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.71/1.13  tff(c_112, plain, (![A_28, B_29]: (r2_hidden('#skF_2'(A_28, B_29, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_28, k10_relat_1(k1_xboole_0, B_29)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_109])).
% 1.71/1.13  tff(c_114, plain, (![A_28, B_29]: (r2_hidden('#skF_2'(A_28, B_29, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_28, k10_relat_1(k1_xboole_0, B_29)))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_112])).
% 1.71/1.13  tff(c_116, plain, (![A_31, B_32]: (~r2_hidden(A_31, k10_relat_1(k1_xboole_0, B_32)))), inference(negUnitSimplification, [status(thm)], [c_72, c_114])).
% 1.71/1.13  tff(c_126, plain, (![B_32]: (k10_relat_1(k1_xboole_0, B_32)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_116])).
% 1.71/1.13  tff(c_28, plain, (k10_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.71/1.13  tff(c_130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_28])).
% 1.71/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.13  
% 1.71/1.13  Inference rules
% 1.71/1.13  ----------------------
% 1.71/1.13  #Ref     : 0
% 1.71/1.13  #Sup     : 24
% 1.71/1.13  #Fact    : 0
% 1.71/1.13  #Define  : 0
% 1.71/1.13  #Split   : 0
% 1.71/1.13  #Chain   : 0
% 1.71/1.13  #Close   : 0
% 1.71/1.13  
% 1.71/1.13  Ordering : KBO
% 1.71/1.13  
% 1.71/1.13  Simplification rules
% 1.71/1.13  ----------------------
% 1.71/1.13  #Subsume      : 2
% 1.71/1.13  #Demod        : 3
% 1.71/1.13  #Tautology    : 15
% 1.71/1.13  #SimpNegUnit  : 1
% 1.71/1.13  #BackRed      : 2
% 1.71/1.13  
% 1.71/1.13  #Partial instantiations: 0
% 1.71/1.13  #Strategies tried      : 1
% 1.71/1.13  
% 1.71/1.13  Timing (in seconds)
% 1.71/1.13  ----------------------
% 1.71/1.13  Preprocessing        : 0.27
% 1.71/1.13  Parsing              : 0.15
% 1.71/1.13  CNF conversion       : 0.02
% 1.71/1.13  Main loop            : 0.11
% 1.71/1.13  Inferencing          : 0.04
% 1.71/1.13  Reduction            : 0.03
% 1.71/1.13  Demodulation         : 0.02
% 1.71/1.13  BG Simplification    : 0.01
% 1.71/1.13  Subsumption          : 0.02
% 1.71/1.13  Abstraction          : 0.00
% 1.71/1.13  MUC search           : 0.00
% 1.71/1.13  Cooper               : 0.00
% 1.71/1.13  Total                : 0.41
% 1.71/1.13  Index Insertion      : 0.00
% 1.71/1.13  Index Deletion       : 0.00
% 1.71/1.13  Index Matching       : 0.00
% 1.71/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
