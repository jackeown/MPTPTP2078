%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:18 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   42 (  43 expanded)
%              Number of leaves         :   25 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 (  52 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > o_1_5_relat_1 > k2_relat_1 > k1_xboole_0 > #skF_1 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(o_1_5_relat_1,type,(
    o_1_5_relat_1: $i > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_69,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => m1_subset_1(o_1_5_relat_1(A),k10_relat_1(A,k1_xboole_0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_1_5_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_28,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(c_24,plain,(
    k10_relat_1('#skF_2',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_14,plain,(
    ! [A_11] :
      ( m1_subset_1(o_1_5_relat_1(A_11),k10_relat_1(A_11,k1_xboole_0))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( r2_hidden(A_9,B_10)
      | v1_xboole_0(B_10)
      | ~ m1_subset_1(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_62,plain,(
    ! [A_31,B_32,C_33] :
      ( r2_hidden('#skF_1'(A_31,B_32,C_33),B_32)
      | ~ r2_hidden(A_31,k10_relat_1(C_33,B_32))
      | ~ v1_relat_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_49,plain,(
    ! [A_27,C_28,B_29] :
      ( ~ r2_hidden(A_27,C_28)
      | ~ r1_xboole_0(k2_tarski(A_27,B_29),C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_54,plain,(
    ! [A_27] : ~ r2_hidden(A_27,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_49])).

tff(c_68,plain,(
    ! [A_34,C_35] :
      ( ~ r2_hidden(A_34,k10_relat_1(C_35,k1_xboole_0))
      | ~ v1_relat_1(C_35) ) ),
    inference(resolution,[status(thm)],[c_62,c_54])).

tff(c_90,plain,(
    ! [C_39,A_40] :
      ( ~ v1_relat_1(C_39)
      | v1_xboole_0(k10_relat_1(C_39,k1_xboole_0))
      | ~ m1_subset_1(A_40,k10_relat_1(C_39,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_12,c_68])).

tff(c_96,plain,(
    ! [A_44] :
      ( v1_xboole_0(k10_relat_1(A_44,k1_xboole_0))
      | ~ v1_relat_1(A_44) ) ),
    inference(resolution,[status(thm)],[c_14,c_90])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_28,plain,(
    ! [B_19,A_20] :
      ( ~ v1_xboole_0(B_19)
      | B_19 = A_20
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_31,plain,(
    ! [A_20] :
      ( k1_xboole_0 = A_20
      | ~ v1_xboole_0(A_20) ) ),
    inference(resolution,[status(thm)],[c_2,c_28])).

tff(c_104,plain,(
    ! [A_45] :
      ( k10_relat_1(A_45,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_45) ) ),
    inference(resolution,[status(thm)],[c_96,c_31])).

tff(c_107,plain,(
    k10_relat_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_104])).

tff(c_111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_107])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:12:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.26  
% 1.97/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.26  %$ r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k1_enumset1 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > o_1_5_relat_1 > k2_relat_1 > k1_xboole_0 > #skF_1 > #skF_2
% 1.97/1.26  
% 1.97/1.26  %Foreground sorts:
% 1.97/1.26  
% 1.97/1.26  
% 1.97/1.26  %Background operators:
% 1.97/1.26  
% 1.97/1.26  
% 1.97/1.26  %Foreground operators:
% 1.97/1.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.97/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.26  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.97/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.26  tff(o_1_5_relat_1, type, o_1_5_relat_1: $i > $i).
% 1.97/1.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.97/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.97/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.97/1.26  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.26  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.97/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.97/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.97/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.97/1.26  
% 1.97/1.27  tff(f_69, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_relat_1)).
% 1.97/1.27  tff(f_53, axiom, (![A]: (v1_relat_1(A) => m1_subset_1(o_1_5_relat_1(A), k10_relat_1(A, k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_o_1_5_relat_1)).
% 1.97/1.27  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 1.97/1.27  tff(f_64, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 1.97/1.27  tff(f_28, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.97/1.27  tff(f_43, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 1.97/1.27  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.97/1.27  tff(f_36, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 1.97/1.27  tff(c_24, plain, (k10_relat_1('#skF_2', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.97/1.27  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.97/1.27  tff(c_14, plain, (![A_11]: (m1_subset_1(o_1_5_relat_1(A_11), k10_relat_1(A_11, k1_xboole_0)) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.97/1.27  tff(c_12, plain, (![A_9, B_10]: (r2_hidden(A_9, B_10) | v1_xboole_0(B_10) | ~m1_subset_1(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.97/1.27  tff(c_62, plain, (![A_31, B_32, C_33]: (r2_hidden('#skF_1'(A_31, B_32, C_33), B_32) | ~r2_hidden(A_31, k10_relat_1(C_33, B_32)) | ~v1_relat_1(C_33))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.97/1.27  tff(c_4, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.97/1.27  tff(c_49, plain, (![A_27, C_28, B_29]: (~r2_hidden(A_27, C_28) | ~r1_xboole_0(k2_tarski(A_27, B_29), C_28))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.97/1.27  tff(c_54, plain, (![A_27]: (~r2_hidden(A_27, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_49])).
% 1.97/1.27  tff(c_68, plain, (![A_34, C_35]: (~r2_hidden(A_34, k10_relat_1(C_35, k1_xboole_0)) | ~v1_relat_1(C_35))), inference(resolution, [status(thm)], [c_62, c_54])).
% 1.97/1.27  tff(c_90, plain, (![C_39, A_40]: (~v1_relat_1(C_39) | v1_xboole_0(k10_relat_1(C_39, k1_xboole_0)) | ~m1_subset_1(A_40, k10_relat_1(C_39, k1_xboole_0)))), inference(resolution, [status(thm)], [c_12, c_68])).
% 1.97/1.27  tff(c_96, plain, (![A_44]: (v1_xboole_0(k10_relat_1(A_44, k1_xboole_0)) | ~v1_relat_1(A_44))), inference(resolution, [status(thm)], [c_14, c_90])).
% 1.97/1.27  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.97/1.27  tff(c_28, plain, (![B_19, A_20]: (~v1_xboole_0(B_19) | B_19=A_20 | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.97/1.27  tff(c_31, plain, (![A_20]: (k1_xboole_0=A_20 | ~v1_xboole_0(A_20))), inference(resolution, [status(thm)], [c_2, c_28])).
% 1.97/1.27  tff(c_104, plain, (![A_45]: (k10_relat_1(A_45, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_45))), inference(resolution, [status(thm)], [c_96, c_31])).
% 1.97/1.27  tff(c_107, plain, (k10_relat_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_104])).
% 1.97/1.27  tff(c_111, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_107])).
% 1.97/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.27  
% 1.97/1.27  Inference rules
% 1.97/1.27  ----------------------
% 1.97/1.27  #Ref     : 0
% 1.97/1.27  #Sup     : 15
% 1.97/1.27  #Fact    : 0
% 1.97/1.27  #Define  : 0
% 1.97/1.27  #Split   : 0
% 1.97/1.27  #Chain   : 0
% 1.97/1.27  #Close   : 0
% 1.97/1.27  
% 1.97/1.27  Ordering : KBO
% 1.97/1.27  
% 1.97/1.27  Simplification rules
% 1.97/1.27  ----------------------
% 1.97/1.27  #Subsume      : 1
% 1.97/1.27  #Demod        : 1
% 1.97/1.27  #Tautology    : 4
% 1.97/1.27  #SimpNegUnit  : 1
% 1.97/1.27  #BackRed      : 0
% 1.97/1.27  
% 1.97/1.27  #Partial instantiations: 0
% 1.97/1.27  #Strategies tried      : 1
% 1.97/1.27  
% 1.97/1.27  Timing (in seconds)
% 1.97/1.27  ----------------------
% 1.97/1.28  Preprocessing        : 0.33
% 1.97/1.28  Parsing              : 0.18
% 1.97/1.28  CNF conversion       : 0.02
% 1.97/1.28  Main loop            : 0.12
% 1.97/1.28  Inferencing          : 0.05
% 1.97/1.28  Reduction            : 0.03
% 1.97/1.28  Demodulation         : 0.02
% 1.97/1.28  BG Simplification    : 0.01
% 1.97/1.28  Subsumption          : 0.02
% 1.97/1.28  Abstraction          : 0.01
% 1.97/1.28  MUC search           : 0.00
% 1.97/1.28  Cooper               : 0.00
% 1.97/1.28  Total                : 0.48
% 1.97/1.28  Index Insertion      : 0.00
% 1.97/1.28  Index Deletion       : 0.00
% 1.97/1.28  Index Matching       : 0.00
% 1.97/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
