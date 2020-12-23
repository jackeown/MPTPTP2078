%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:59 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :   40 (  71 expanded)
%              Number of leaves         :   22 (  35 expanded)
%              Depth                    :    6
%              Number of atoms          :   38 (  88 expanded)
%              Number of equality atoms :   20 (  48 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_54,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_34,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_65,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_603,plain,(
    ! [A_90,B_91] :
      ( r2_hidden(k4_tarski('#skF_6'(A_90,B_91),'#skF_5'(A_90,B_91)),A_90)
      | r2_hidden('#skF_7'(A_90,B_91),B_91)
      | k2_relat_1(A_90) = B_91 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,(
    ! [A_45,B_46] : ~ r2_hidden(A_45,k2_zfmisc_1(A_45,B_46)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_60,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_57])).

tff(c_1089,plain,(
    ! [B_110] :
      ( r2_hidden('#skF_7'(k1_xboole_0,B_110),B_110)
      | k2_relat_1(k1_xboole_0) = B_110 ) ),
    inference(resolution,[status(thm)],[c_603,c_60])).

tff(c_1245,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1089,c_60])).

tff(c_91,plain,(
    ! [C_60,A_61] :
      ( r2_hidden(k4_tarski(C_60,'#skF_4'(A_61,k1_relat_1(A_61),C_60)),A_61)
      | ~ r2_hidden(C_60,k1_relat_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_104,plain,(
    ! [C_60] : ~ r2_hidden(C_60,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_91,c_60])).

tff(c_1244,plain,(
    k2_relat_1(k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1089,c_104])).

tff(c_1271,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1245,c_1244])).

tff(c_1272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_1271])).

tff(c_1273,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_1781,plain,(
    ! [A_154,B_155] :
      ( r2_hidden(k4_tarski('#skF_6'(A_154,B_155),'#skF_5'(A_154,B_155)),A_154)
      | r2_hidden('#skF_7'(A_154,B_155),B_155)
      | k2_relat_1(A_154) = B_155 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1900,plain,(
    ! [B_156] :
      ( r2_hidden('#skF_7'(k1_xboole_0,B_156),B_156)
      | k2_relat_1(k1_xboole_0) = B_156 ) ),
    inference(resolution,[status(thm)],[c_1781,c_60])).

tff(c_1988,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1900,c_60])).

tff(c_2014,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1273,c_1988])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:51:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.52  
% 3.31/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/1.52  %$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5
% 3.31/1.52  
% 3.31/1.52  %Foreground sorts:
% 3.31/1.52  
% 3.31/1.52  
% 3.31/1.52  %Background operators:
% 3.31/1.52  
% 3.31/1.52  
% 3.31/1.52  %Foreground operators:
% 3.31/1.52  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.31/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.31/1.52  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.31/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.31/1.52  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.31/1.52  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.31/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.31/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.31/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.31/1.52  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 3.31/1.52  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.31/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.31/1.52  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.31/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.31/1.52  
% 3.46/1.53  tff(f_54, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.46/1.53  tff(f_50, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 3.46/1.53  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.46/1.53  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 3.46/1.53  tff(f_42, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 3.46/1.53  tff(c_34, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.46/1.53  tff(c_65, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_34])).
% 3.46/1.53  tff(c_603, plain, (![A_90, B_91]: (r2_hidden(k4_tarski('#skF_6'(A_90, B_91), '#skF_5'(A_90, B_91)), A_90) | r2_hidden('#skF_7'(A_90, B_91), B_91) | k2_relat_1(A_90)=B_91)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.46/1.53  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.46/1.53  tff(c_57, plain, (![A_45, B_46]: (~r2_hidden(A_45, k2_zfmisc_1(A_45, B_46)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.46/1.53  tff(c_60, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_57])).
% 3.46/1.53  tff(c_1089, plain, (![B_110]: (r2_hidden('#skF_7'(k1_xboole_0, B_110), B_110) | k2_relat_1(k1_xboole_0)=B_110)), inference(resolution, [status(thm)], [c_603, c_60])).
% 3.46/1.53  tff(c_1245, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1089, c_60])).
% 3.46/1.53  tff(c_91, plain, (![C_60, A_61]: (r2_hidden(k4_tarski(C_60, '#skF_4'(A_61, k1_relat_1(A_61), C_60)), A_61) | ~r2_hidden(C_60, k1_relat_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.46/1.53  tff(c_104, plain, (![C_60]: (~r2_hidden(C_60, k1_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_91, c_60])).
% 3.46/1.53  tff(c_1244, plain, (k2_relat_1(k1_xboole_0)=k1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_1089, c_104])).
% 3.46/1.53  tff(c_1271, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1245, c_1244])).
% 3.46/1.53  tff(c_1272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_1271])).
% 3.46/1.53  tff(c_1273, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 3.46/1.53  tff(c_1781, plain, (![A_154, B_155]: (r2_hidden(k4_tarski('#skF_6'(A_154, B_155), '#skF_5'(A_154, B_155)), A_154) | r2_hidden('#skF_7'(A_154, B_155), B_155) | k2_relat_1(A_154)=B_155)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.46/1.53  tff(c_1900, plain, (![B_156]: (r2_hidden('#skF_7'(k1_xboole_0, B_156), B_156) | k2_relat_1(k1_xboole_0)=B_156)), inference(resolution, [status(thm)], [c_1781, c_60])).
% 3.46/1.53  tff(c_1988, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1900, c_60])).
% 3.46/1.53  tff(c_2014, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1273, c_1988])).
% 3.46/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.53  
% 3.46/1.53  Inference rules
% 3.46/1.53  ----------------------
% 3.46/1.53  #Ref     : 0
% 3.46/1.53  #Sup     : 383
% 3.46/1.53  #Fact    : 0
% 3.46/1.53  #Define  : 0
% 3.46/1.53  #Split   : 1
% 3.46/1.53  #Chain   : 0
% 3.46/1.53  #Close   : 0
% 3.46/1.53  
% 3.46/1.53  Ordering : KBO
% 3.46/1.53  
% 3.46/1.53  Simplification rules
% 3.46/1.53  ----------------------
% 3.46/1.53  #Subsume      : 125
% 3.46/1.53  #Demod        : 31
% 3.46/1.53  #Tautology    : 20
% 3.46/1.53  #SimpNegUnit  : 4
% 3.46/1.53  #BackRed      : 16
% 3.46/1.53  
% 3.46/1.53  #Partial instantiations: 0
% 3.46/1.53  #Strategies tried      : 1
% 3.46/1.53  
% 3.46/1.53  Timing (in seconds)
% 3.46/1.53  ----------------------
% 3.47/1.53  Preprocessing        : 0.28
% 3.47/1.53  Parsing              : 0.14
% 3.47/1.53  CNF conversion       : 0.02
% 3.47/1.53  Main loop            : 0.49
% 3.47/1.53  Inferencing          : 0.18
% 3.47/1.53  Reduction            : 0.14
% 3.47/1.53  Demodulation         : 0.07
% 3.47/1.53  BG Simplification    : 0.02
% 3.47/1.53  Subsumption          : 0.11
% 3.47/1.53  Abstraction          : 0.03
% 3.47/1.53  MUC search           : 0.00
% 3.47/1.53  Cooper               : 0.00
% 3.47/1.53  Total                : 0.79
% 3.47/1.53  Index Insertion      : 0.00
% 3.47/1.53  Index Deletion       : 0.00
% 3.47/1.53  Index Matching       : 0.00
% 3.47/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
