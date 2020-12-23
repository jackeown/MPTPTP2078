%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:19 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   31 (  37 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  42 expanded)
%              Number of equality atoms :   11 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_57,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(c_26,plain,(
    k10_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_28,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_70,plain,(
    ! [A_21,B_22] :
      ( r2_hidden('#skF_1'(A_21,B_22),B_22)
      | r2_hidden('#skF_2'(A_21,B_22),A_21)
      | B_22 = A_21 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_51,plain,(
    ! [A_16,B_17] : ~ r2_hidden(A_16,k2_zfmisc_1(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_54,plain,(
    ! [A_4] : ~ r2_hidden(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_51])).

tff(c_77,plain,(
    ! [B_22] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_22),B_22)
      | k1_xboole_0 = B_22 ) ),
    inference(resolution,[status(thm)],[c_70,c_54])).

tff(c_110,plain,(
    ! [A_30,B_31,C_32] :
      ( r2_hidden('#skF_3'(A_30,B_31,C_32),B_31)
      | ~ r2_hidden(A_30,k10_relat_1(C_32,B_31))
      | ~ v1_relat_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_116,plain,(
    ! [A_33,C_34] :
      ( ~ r2_hidden(A_33,k10_relat_1(C_34,k1_xboole_0))
      | ~ v1_relat_1(C_34) ) ),
    inference(resolution,[status(thm)],[c_110,c_54])).

tff(c_143,plain,(
    ! [C_38] :
      ( ~ v1_relat_1(C_38)
      | k10_relat_1(C_38,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_77,c_116])).

tff(c_146,plain,(
    k10_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_143])).

tff(c_150,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_146])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:46:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.14  
% 1.74/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.14  %$ r2_hidden > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 1.74/1.14  
% 1.74/1.14  %Foreground sorts:
% 1.74/1.14  
% 1.74/1.14  
% 1.74/1.14  %Background operators:
% 1.74/1.14  
% 1.74/1.14  
% 1.74/1.14  %Foreground operators:
% 1.74/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.74/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.74/1.14  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.74/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.74/1.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.74/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.74/1.14  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.74/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.74/1.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.74/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.74/1.14  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.74/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.74/1.14  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.74/1.14  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.74/1.14  
% 1.74/1.15  tff(f_57, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_relat_1)).
% 1.74/1.15  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 1.74/1.15  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.74/1.15  tff(f_41, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.74/1.15  tff(f_52, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 1.74/1.15  tff(c_26, plain, (k10_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.74/1.15  tff(c_28, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.74/1.15  tff(c_70, plain, (![A_21, B_22]: (r2_hidden('#skF_1'(A_21, B_22), B_22) | r2_hidden('#skF_2'(A_21, B_22), A_21) | B_22=A_21)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.74/1.15  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.74/1.15  tff(c_51, plain, (![A_16, B_17]: (~r2_hidden(A_16, k2_zfmisc_1(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.74/1.15  tff(c_54, plain, (![A_4]: (~r2_hidden(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_51])).
% 1.74/1.15  tff(c_77, plain, (![B_22]: (r2_hidden('#skF_1'(k1_xboole_0, B_22), B_22) | k1_xboole_0=B_22)), inference(resolution, [status(thm)], [c_70, c_54])).
% 1.74/1.15  tff(c_110, plain, (![A_30, B_31, C_32]: (r2_hidden('#skF_3'(A_30, B_31, C_32), B_31) | ~r2_hidden(A_30, k10_relat_1(C_32, B_31)) | ~v1_relat_1(C_32))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.74/1.15  tff(c_116, plain, (![A_33, C_34]: (~r2_hidden(A_33, k10_relat_1(C_34, k1_xboole_0)) | ~v1_relat_1(C_34))), inference(resolution, [status(thm)], [c_110, c_54])).
% 1.74/1.15  tff(c_143, plain, (![C_38]: (~v1_relat_1(C_38) | k10_relat_1(C_38, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_77, c_116])).
% 1.74/1.15  tff(c_146, plain, (k10_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_143])).
% 1.74/1.15  tff(c_150, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_146])).
% 1.74/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.15  
% 1.74/1.15  Inference rules
% 1.74/1.15  ----------------------
% 1.74/1.15  #Ref     : 0
% 1.74/1.15  #Sup     : 23
% 1.74/1.15  #Fact    : 0
% 1.74/1.15  #Define  : 0
% 1.74/1.15  #Split   : 0
% 1.74/1.15  #Chain   : 0
% 1.74/1.15  #Close   : 0
% 1.74/1.15  
% 1.74/1.15  Ordering : KBO
% 1.74/1.15  
% 1.74/1.15  Simplification rules
% 1.74/1.15  ----------------------
% 1.74/1.15  #Subsume      : 4
% 1.74/1.15  #Demod        : 0
% 1.74/1.15  #Tautology    : 11
% 1.74/1.15  #SimpNegUnit  : 1
% 1.74/1.15  #BackRed      : 0
% 1.74/1.15  
% 1.74/1.15  #Partial instantiations: 0
% 1.74/1.15  #Strategies tried      : 1
% 1.74/1.15  
% 1.74/1.15  Timing (in seconds)
% 1.74/1.15  ----------------------
% 1.74/1.15  Preprocessing        : 0.27
% 1.74/1.15  Parsing              : 0.15
% 1.74/1.15  CNF conversion       : 0.02
% 1.74/1.15  Main loop            : 0.13
% 1.74/1.15  Inferencing          : 0.06
% 1.74/1.15  Reduction            : 0.03
% 1.74/1.15  Demodulation         : 0.02
% 1.74/1.15  BG Simplification    : 0.01
% 1.74/1.15  Subsumption          : 0.02
% 1.74/1.15  Abstraction          : 0.01
% 1.74/1.15  MUC search           : 0.00
% 1.74/1.15  Cooper               : 0.00
% 1.74/1.15  Total                : 0.42
% 1.81/1.15  Index Insertion      : 0.00
% 1.81/1.15  Index Deletion       : 0.00
% 1.81/1.15  Index Matching       : 0.00
% 1.81/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
