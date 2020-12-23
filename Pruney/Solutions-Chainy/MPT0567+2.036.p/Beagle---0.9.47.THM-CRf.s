%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:19 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   47 (  48 expanded)
%              Number of leaves         :   28 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   49 (  51 expanded)
%              Number of equality atoms :   15 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_51,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_36,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_38,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_287,plain,(
    ! [A_57,B_58,C_59] :
      ( r2_hidden('#skF_2'(A_57,B_58,C_59),B_58)
      | ~ r2_hidden(A_57,k10_relat_1(C_59,B_58))
      | ~ v1_relat_1(C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_14,plain,(
    ! [A_10] : r1_xboole_0(A_10,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_100,plain,(
    ! [A_35,B_36] :
      ( ~ r2_hidden(A_35,B_36)
      | ~ r1_xboole_0(k1_tarski(A_35),B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_105,plain,(
    ! [A_35] : ~ r2_hidden(A_35,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_100])).

tff(c_293,plain,(
    ! [A_60,C_61] :
      ( ~ r2_hidden(A_60,k10_relat_1(C_61,k1_xboole_0))
      | ~ v1_relat_1(C_61) ) ),
    inference(resolution,[status(thm)],[c_287,c_105])).

tff(c_317,plain,(
    ! [C_64,A_65] :
      ( ~ v1_relat_1(C_64)
      | r1_xboole_0(A_65,k10_relat_1(C_64,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_4,c_293])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = A_11
      | ~ r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_331,plain,(
    ! [A_69,C_70] :
      ( k4_xboole_0(A_69,k10_relat_1(C_70,k1_xboole_0)) = A_69
      | ~ v1_relat_1(C_70) ) ),
    inference(resolution,[status(thm)],[c_317,c_16])).

tff(c_8,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_133,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k4_xboole_0(A_44,B_45)) = k3_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_148,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_133])).

tff(c_151,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_148])).

tff(c_362,plain,(
    ! [C_71] :
      ( k10_relat_1(C_71,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(C_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_151])).

tff(c_365,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_362])).

tff(c_369,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_365])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:25:27 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.19  
% 1.97/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.19  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 1.97/1.19  
% 1.97/1.19  %Foreground sorts:
% 1.97/1.19  
% 1.97/1.19  
% 1.97/1.19  %Background operators:
% 1.97/1.19  
% 1.97/1.19  
% 1.97/1.19  %Foreground operators:
% 1.97/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.97/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.97/1.19  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.97/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.97/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.97/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.97/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.97/1.19  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.97/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.19  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.97/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.97/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.97/1.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.97/1.19  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.97/1.19  
% 1.97/1.20  tff(f_82, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_relat_1)).
% 1.97/1.20  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.97/1.20  tff(f_77, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 1.97/1.20  tff(f_51, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.97/1.20  tff(f_64, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.97/1.20  tff(f_55, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.97/1.20  tff(f_45, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.97/1.20  tff(f_47, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.97/1.20  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.97/1.20  tff(c_36, plain, (k10_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.97/1.20  tff(c_38, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 1.97/1.20  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.97/1.20  tff(c_287, plain, (![A_57, B_58, C_59]: (r2_hidden('#skF_2'(A_57, B_58, C_59), B_58) | ~r2_hidden(A_57, k10_relat_1(C_59, B_58)) | ~v1_relat_1(C_59))), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.97/1.20  tff(c_14, plain, (![A_10]: (r1_xboole_0(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.97/1.20  tff(c_100, plain, (![A_35, B_36]: (~r2_hidden(A_35, B_36) | ~r1_xboole_0(k1_tarski(A_35), B_36))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.97/1.20  tff(c_105, plain, (![A_35]: (~r2_hidden(A_35, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_100])).
% 1.97/1.20  tff(c_293, plain, (![A_60, C_61]: (~r2_hidden(A_60, k10_relat_1(C_61, k1_xboole_0)) | ~v1_relat_1(C_61))), inference(resolution, [status(thm)], [c_287, c_105])).
% 1.97/1.20  tff(c_317, plain, (![C_64, A_65]: (~v1_relat_1(C_64) | r1_xboole_0(A_65, k10_relat_1(C_64, k1_xboole_0)))), inference(resolution, [status(thm)], [c_4, c_293])).
% 1.97/1.20  tff(c_16, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=A_11 | ~r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.97/1.20  tff(c_331, plain, (![A_69, C_70]: (k4_xboole_0(A_69, k10_relat_1(C_70, k1_xboole_0))=A_69 | ~v1_relat_1(C_70))), inference(resolution, [status(thm)], [c_317, c_16])).
% 1.97/1.20  tff(c_8, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.97/1.20  tff(c_10, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.97/1.20  tff(c_133, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k4_xboole_0(A_44, B_45))=k3_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.97/1.20  tff(c_148, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_133])).
% 1.97/1.20  tff(c_151, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_148])).
% 1.97/1.20  tff(c_362, plain, (![C_71]: (k10_relat_1(C_71, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(C_71))), inference(superposition, [status(thm), theory('equality')], [c_331, c_151])).
% 1.97/1.20  tff(c_365, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_362])).
% 1.97/1.20  tff(c_369, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_365])).
% 1.97/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.20  
% 1.97/1.20  Inference rules
% 1.97/1.20  ----------------------
% 1.97/1.20  #Ref     : 0
% 1.97/1.20  #Sup     : 73
% 1.97/1.20  #Fact    : 0
% 1.97/1.20  #Define  : 0
% 1.97/1.20  #Split   : 0
% 1.97/1.20  #Chain   : 0
% 1.97/1.20  #Close   : 0
% 1.97/1.20  
% 1.97/1.20  Ordering : KBO
% 1.97/1.20  
% 1.97/1.20  Simplification rules
% 1.97/1.20  ----------------------
% 1.97/1.20  #Subsume      : 5
% 1.97/1.20  #Demod        : 9
% 1.97/1.20  #Tautology    : 47
% 1.97/1.20  #SimpNegUnit  : 1
% 1.97/1.20  #BackRed      : 1
% 1.97/1.20  
% 1.97/1.20  #Partial instantiations: 0
% 1.97/1.20  #Strategies tried      : 1
% 1.97/1.20  
% 1.97/1.20  Timing (in seconds)
% 1.97/1.20  ----------------------
% 1.97/1.20  Preprocessing        : 0.30
% 1.97/1.20  Parsing              : 0.17
% 1.97/1.20  CNF conversion       : 0.02
% 1.97/1.20  Main loop            : 0.17
% 1.97/1.20  Inferencing          : 0.07
% 1.97/1.20  Reduction            : 0.05
% 1.97/1.20  Demodulation         : 0.04
% 1.97/1.20  BG Simplification    : 0.01
% 1.97/1.20  Subsumption          : 0.02
% 1.97/1.20  Abstraction          : 0.01
% 1.97/1.20  MUC search           : 0.00
% 1.97/1.20  Cooper               : 0.00
% 1.97/1.20  Total                : 0.50
% 1.97/1.20  Index Insertion      : 0.00
% 1.97/1.20  Index Deletion       : 0.00
% 1.97/1.20  Index Matching       : 0.00
% 1.97/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
