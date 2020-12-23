%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:15 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   36 (  43 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   43 (  55 expanded)
%              Number of equality atoms :   11 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_63,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_30,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_117,plain,(
    ! [A_37,B_38,C_39] :
      ( r2_hidden('#skF_2'(A_37,B_38,C_39),B_38)
      | ~ r2_hidden(A_37,k10_relat_1(C_39,B_38))
      | ~ v1_relat_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_16,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_57,plain,(
    ! [A_21,B_22] : ~ r2_hidden(A_21,k2_zfmisc_1(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_60,plain,(
    ! [A_8] : ~ r2_hidden(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_57])).

tff(c_126,plain,(
    ! [A_40,C_41] :
      ( ~ r2_hidden(A_40,k10_relat_1(C_41,k1_xboole_0))
      | ~ v1_relat_1(C_41) ) ),
    inference(resolution,[status(thm)],[c_117,c_60])).

tff(c_137,plain,(
    ! [C_42,B_43] :
      ( ~ v1_relat_1(C_42)
      | r1_tarski(k10_relat_1(C_42,k1_xboole_0),B_43) ) ),
    inference(resolution,[status(thm)],[c_6,c_126])).

tff(c_76,plain,(
    ! [A_26,B_27] :
      ( r2_hidden('#skF_1'(A_26,B_27),A_26)
      | r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_81,plain,(
    ! [B_27] : r1_tarski(k1_xboole_0,B_27) ),
    inference(resolution,[status(thm)],[c_76,c_60])).

tff(c_83,plain,(
    ! [B_29,A_30] :
      ( B_29 = A_30
      | ~ r1_tarski(B_29,A_30)
      | ~ r1_tarski(A_30,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_88,plain,(
    ! [B_27] :
      ( k1_xboole_0 = B_27
      | ~ r1_tarski(B_27,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_81,c_83])).

tff(c_146,plain,(
    ! [C_44] :
      ( k10_relat_1(C_44,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(C_44) ) ),
    inference(resolution,[status(thm)],[c_137,c_88])).

tff(c_149,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_146])).

tff(c_153,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_149])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n007.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 09:36:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.17  
% 1.80/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.17  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 1.90/1.17  
% 1.90/1.17  %Foreground sorts:
% 1.90/1.17  
% 1.90/1.17  
% 1.90/1.17  %Background operators:
% 1.90/1.17  
% 1.90/1.17  
% 1.90/1.17  %Foreground operators:
% 1.90/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.90/1.17  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.90/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.90/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.90/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.90/1.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.90/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.17  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.90/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.90/1.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.90/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.90/1.17  
% 1.90/1.18  tff(f_63, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_relat_1)).
% 1.90/1.18  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.90/1.18  tff(f_58, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 1.90/1.18  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.90/1.18  tff(f_47, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.90/1.18  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.90/1.18  tff(c_30, plain, (k10_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.90/1.18  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.90/1.18  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.90/1.18  tff(c_117, plain, (![A_37, B_38, C_39]: (r2_hidden('#skF_2'(A_37, B_38, C_39), B_38) | ~r2_hidden(A_37, k10_relat_1(C_39, B_38)) | ~v1_relat_1(C_39))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.90/1.18  tff(c_16, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.90/1.18  tff(c_57, plain, (![A_21, B_22]: (~r2_hidden(A_21, k2_zfmisc_1(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.90/1.18  tff(c_60, plain, (![A_8]: (~r2_hidden(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_57])).
% 1.90/1.18  tff(c_126, plain, (![A_40, C_41]: (~r2_hidden(A_40, k10_relat_1(C_41, k1_xboole_0)) | ~v1_relat_1(C_41))), inference(resolution, [status(thm)], [c_117, c_60])).
% 1.90/1.18  tff(c_137, plain, (![C_42, B_43]: (~v1_relat_1(C_42) | r1_tarski(k10_relat_1(C_42, k1_xboole_0), B_43))), inference(resolution, [status(thm)], [c_6, c_126])).
% 1.90/1.18  tff(c_76, plain, (![A_26, B_27]: (r2_hidden('#skF_1'(A_26, B_27), A_26) | r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.90/1.18  tff(c_81, plain, (![B_27]: (r1_tarski(k1_xboole_0, B_27))), inference(resolution, [status(thm)], [c_76, c_60])).
% 1.90/1.18  tff(c_83, plain, (![B_29, A_30]: (B_29=A_30 | ~r1_tarski(B_29, A_30) | ~r1_tarski(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.90/1.18  tff(c_88, plain, (![B_27]: (k1_xboole_0=B_27 | ~r1_tarski(B_27, k1_xboole_0))), inference(resolution, [status(thm)], [c_81, c_83])).
% 1.90/1.18  tff(c_146, plain, (![C_44]: (k10_relat_1(C_44, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(C_44))), inference(resolution, [status(thm)], [c_137, c_88])).
% 1.90/1.18  tff(c_149, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_146])).
% 1.90/1.18  tff(c_153, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_149])).
% 1.90/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.18  
% 1.90/1.18  Inference rules
% 1.90/1.18  ----------------------
% 1.90/1.18  #Ref     : 0
% 1.90/1.18  #Sup     : 24
% 1.90/1.18  #Fact    : 0
% 1.90/1.18  #Define  : 0
% 1.90/1.18  #Split   : 0
% 1.90/1.18  #Chain   : 0
% 1.90/1.18  #Close   : 0
% 1.90/1.18  
% 1.90/1.18  Ordering : KBO
% 1.90/1.18  
% 1.90/1.18  Simplification rules
% 1.90/1.18  ----------------------
% 1.90/1.18  #Subsume      : 1
% 1.90/1.18  #Demod        : 3
% 1.90/1.18  #Tautology    : 13
% 1.90/1.18  #SimpNegUnit  : 1
% 1.90/1.18  #BackRed      : 0
% 1.90/1.18  
% 1.90/1.18  #Partial instantiations: 0
% 1.90/1.18  #Strategies tried      : 1
% 1.90/1.18  
% 1.90/1.18  Timing (in seconds)
% 1.90/1.18  ----------------------
% 1.90/1.19  Preprocessing        : 0.28
% 1.90/1.19  Parsing              : 0.15
% 1.90/1.19  CNF conversion       : 0.02
% 1.90/1.19  Main loop            : 0.14
% 1.90/1.19  Inferencing          : 0.06
% 1.90/1.19  Reduction            : 0.04
% 1.90/1.19  Demodulation         : 0.03
% 1.90/1.19  BG Simplification    : 0.01
% 1.90/1.19  Subsumption          : 0.03
% 1.90/1.19  Abstraction          : 0.01
% 1.90/1.19  MUC search           : 0.00
% 1.90/1.19  Cooper               : 0.00
% 1.90/1.19  Total                : 0.45
% 1.90/1.19  Index Insertion      : 0.00
% 1.90/1.19  Index Deletion       : 0.00
% 1.90/1.19  Index Matching       : 0.00
% 1.90/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
