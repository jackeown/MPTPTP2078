%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:27 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   43 (  56 expanded)
%              Number of leaves         :   25 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  70 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > v5_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v5_ordinal1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_ordinal1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_funct_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v4_relat_1(k1_xboole_0,A)
      & v5_relat_1(k1_xboole_0,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l222_relat_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(k1_xboole_0)
        & v5_relat_1(k1_xboole_0,A)
        & v1_funct_1(k1_xboole_0)
        & v5_ordinal1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_24,plain,(
    ! [A_26] :
      ( v5_ordinal1(A_26)
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_38,plain,(
    ! [A_30] :
      ( v1_funct_1(A_30)
      | ~ v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_42,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_38])).

tff(c_20,plain,(
    ! [B_24] : v5_relat_1(k1_xboole_0,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,'#skF_4')
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_28,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_26])).

tff(c_67,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ v5_ordinal1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_28])).

tff(c_68,plain,(
    ~ v5_ordinal1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_71,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_68])).

tff(c_75,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_71])).

tff(c_76,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_79,plain,(
    ! [A_36] :
      ( r2_hidden('#skF_1'(A_36),A_36)
      | v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_59,plain,(
    ! [A_33,B_34] : ~ r2_hidden(A_33,k2_zfmisc_1(A_33,B_34)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_65,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_59])).

tff(c_83,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_79,c_65])).

tff(c_87,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_83])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:39:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.17  
% 1.73/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.18  %$ v5_relat_1 > v4_relat_1 > r2_hidden > v5_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.73/1.18  
% 1.73/1.18  %Foreground sorts:
% 1.73/1.18  
% 1.73/1.18  
% 1.73/1.18  %Background operators:
% 1.73/1.18  
% 1.73/1.18  
% 1.73/1.18  %Foreground operators:
% 1.73/1.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.73/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.73/1.18  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.73/1.18  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.73/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.73/1.18  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.73/1.18  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 1.73/1.18  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.73/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.73/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.73/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.73/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.73/1.18  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.73/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.73/1.18  
% 1.73/1.18  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.73/1.18  tff(f_57, axiom, (![A]: (v1_xboole_0(A) => v5_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_ordinal1)).
% 1.73/1.18  tff(f_53, axiom, (![A]: (v1_xboole_0(A) => v1_funct_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_1)).
% 1.73/1.18  tff(f_49, axiom, (![A, B]: (v4_relat_1(k1_xboole_0, A) & v5_relat_1(k1_xboole_0, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l222_relat_1)).
% 1.73/1.18  tff(f_66, negated_conjecture, ~(![A]: (((v1_relat_1(k1_xboole_0) & v5_relat_1(k1_xboole_0, A)) & v1_funct_1(k1_xboole_0)) & v5_ordinal1(k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_ordinal1)).
% 1.73/1.18  tff(f_45, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 1.73/1.18  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.73/1.18  tff(f_35, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.73/1.18  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.73/1.18  tff(c_24, plain, (![A_26]: (v5_ordinal1(A_26) | ~v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.73/1.18  tff(c_38, plain, (![A_30]: (v1_funct_1(A_30) | ~v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.73/1.18  tff(c_42, plain, (v1_funct_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_38])).
% 1.73/1.18  tff(c_20, plain, (![B_24]: (v5_relat_1(k1_xboole_0, B_24))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.73/1.18  tff(c_26, plain, (~v1_relat_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0, '#skF_4') | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.73/1.18  tff(c_28, plain, (~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_26])).
% 1.73/1.18  tff(c_67, plain, (~v1_relat_1(k1_xboole_0) | ~v5_ordinal1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_28])).
% 1.73/1.18  tff(c_68, plain, (~v5_ordinal1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_67])).
% 1.73/1.18  tff(c_71, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_68])).
% 1.73/1.18  tff(c_75, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_71])).
% 1.73/1.18  tff(c_76, plain, (~v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_67])).
% 1.73/1.18  tff(c_79, plain, (![A_36]: (r2_hidden('#skF_1'(A_36), A_36) | v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.73/1.18  tff(c_6, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.73/1.18  tff(c_59, plain, (![A_33, B_34]: (~r2_hidden(A_33, k2_zfmisc_1(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.73/1.18  tff(c_65, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_59])).
% 1.73/1.18  tff(c_83, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_79, c_65])).
% 1.73/1.18  tff(c_87, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_83])).
% 1.73/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.18  
% 1.73/1.18  Inference rules
% 1.73/1.18  ----------------------
% 1.73/1.18  #Ref     : 0
% 1.73/1.18  #Sup     : 11
% 1.73/1.18  #Fact    : 0
% 1.73/1.18  #Define  : 0
% 1.73/1.18  #Split   : 1
% 1.73/1.18  #Chain   : 0
% 1.73/1.19  #Close   : 0
% 1.73/1.19  
% 1.73/1.19  Ordering : KBO
% 1.73/1.19  
% 1.73/1.19  Simplification rules
% 1.73/1.19  ----------------------
% 1.73/1.19  #Subsume      : 1
% 1.73/1.19  #Demod        : 3
% 1.73/1.19  #Tautology    : 6
% 1.73/1.19  #SimpNegUnit  : 1
% 1.73/1.19  #BackRed      : 0
% 1.73/1.19  
% 1.73/1.19  #Partial instantiations: 0
% 1.73/1.19  #Strategies tried      : 1
% 1.73/1.19  
% 1.73/1.19  Timing (in seconds)
% 1.73/1.19  ----------------------
% 1.73/1.19  Preprocessing        : 0.26
% 1.73/1.19  Parsing              : 0.14
% 1.73/1.19  CNF conversion       : 0.02
% 1.73/1.19  Main loop            : 0.10
% 1.73/1.19  Inferencing          : 0.04
% 1.73/1.19  Reduction            : 0.03
% 1.73/1.19  Demodulation         : 0.02
% 1.73/1.19  BG Simplification    : 0.01
% 1.73/1.19  Subsumption          : 0.01
% 1.73/1.19  Abstraction          : 0.00
% 1.73/1.19  MUC search           : 0.00
% 1.73/1.19  Cooper               : 0.00
% 1.73/1.19  Total                : 0.39
% 1.73/1.19  Index Insertion      : 0.00
% 1.73/1.19  Index Deletion       : 0.00
% 1.73/1.19  Index Matching       : 0.00
% 1.73/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
