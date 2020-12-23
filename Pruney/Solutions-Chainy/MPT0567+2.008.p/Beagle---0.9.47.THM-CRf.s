%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:15 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   28 (  34 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  36 expanded)
%              Number of equality atoms :   11 (  16 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_52,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_28,plain,(
    k10_relat_1('#skF_5',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_30,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_100,plain,(
    ! [A_70,B_71,C_72] :
      ( r2_hidden('#skF_2'(A_70,B_71,C_72),B_71)
      | r2_hidden('#skF_3'(A_70,B_71,C_72),C_72)
      | k10_relat_1(A_70,B_71) = C_72
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_53,plain,(
    ! [A_49,B_50] : ~ r2_hidden(A_49,k2_zfmisc_1(A_49,B_50)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_56,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_53])).

tff(c_144,plain,(
    ! [A_73,C_74] :
      ( r2_hidden('#skF_3'(A_73,k1_xboole_0,C_74),C_74)
      | k10_relat_1(A_73,k1_xboole_0) = C_74
      | ~ v1_relat_1(A_73) ) ),
    inference(resolution,[status(thm)],[c_100,c_56])).

tff(c_192,plain,(
    ! [A_78] :
      ( k10_relat_1(A_78,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_78) ) ),
    inference(resolution,[status(thm)],[c_144,c_56])).

tff(c_195,plain,(
    k10_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_192])).

tff(c_199,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_195])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.06/0.25  % Computer   : n004.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % DateTime   : Tue Dec  1 18:35:23 EST 2020
% 0.06/0.26  % CPUTime    : 
% 0.06/0.26  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.07  
% 1.65/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.07  %$ r2_hidden > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 1.65/1.07  
% 1.65/1.07  %Foreground sorts:
% 1.65/1.07  
% 1.65/1.07  
% 1.65/1.07  %Background operators:
% 1.65/1.07  
% 1.65/1.07  
% 1.65/1.07  %Foreground operators:
% 1.65/1.07  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.65/1.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.65/1.07  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.65/1.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.65/1.07  tff('#skF_5', type, '#skF_5': $i).
% 1.65/1.07  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.65/1.07  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 1.65/1.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.07  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.65/1.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.65/1.07  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.65/1.07  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.65/1.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.07  
% 1.65/1.08  tff(f_52, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_relat_1)).
% 1.65/1.08  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 1.65/1.08  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.65/1.08  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.65/1.08  tff(c_28, plain, (k10_relat_1('#skF_5', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.65/1.08  tff(c_30, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.65/1.08  tff(c_100, plain, (![A_70, B_71, C_72]: (r2_hidden('#skF_2'(A_70, B_71, C_72), B_71) | r2_hidden('#skF_3'(A_70, B_71, C_72), C_72) | k10_relat_1(A_70, B_71)=C_72 | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.65/1.08  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.65/1.08  tff(c_53, plain, (![A_49, B_50]: (~r2_hidden(A_49, k2_zfmisc_1(A_49, B_50)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.65/1.08  tff(c_56, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_53])).
% 1.65/1.08  tff(c_144, plain, (![A_73, C_74]: (r2_hidden('#skF_3'(A_73, k1_xboole_0, C_74), C_74) | k10_relat_1(A_73, k1_xboole_0)=C_74 | ~v1_relat_1(A_73))), inference(resolution, [status(thm)], [c_100, c_56])).
% 1.65/1.08  tff(c_192, plain, (![A_78]: (k10_relat_1(A_78, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_78))), inference(resolution, [status(thm)], [c_144, c_56])).
% 1.65/1.08  tff(c_195, plain, (k10_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_192])).
% 1.65/1.08  tff(c_199, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_195])).
% 1.65/1.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.08  
% 1.65/1.08  Inference rules
% 1.65/1.08  ----------------------
% 1.65/1.08  #Ref     : 0
% 1.65/1.08  #Sup     : 35
% 1.65/1.08  #Fact    : 0
% 1.65/1.08  #Define  : 0
% 1.65/1.08  #Split   : 0
% 1.65/1.08  #Chain   : 0
% 1.65/1.08  #Close   : 0
% 1.65/1.08  
% 1.65/1.08  Ordering : KBO
% 1.65/1.08  
% 1.65/1.08  Simplification rules
% 1.65/1.08  ----------------------
% 1.65/1.08  #Subsume      : 1
% 1.65/1.08  #Demod        : 0
% 1.65/1.08  #Tautology    : 8
% 1.65/1.08  #SimpNegUnit  : 1
% 1.65/1.08  #BackRed      : 0
% 1.65/1.08  
% 1.65/1.08  #Partial instantiations: 0
% 1.65/1.08  #Strategies tried      : 1
% 1.65/1.08  
% 1.65/1.08  Timing (in seconds)
% 1.65/1.08  ----------------------
% 1.65/1.08  Preprocessing        : 0.28
% 1.65/1.08  Parsing              : 0.15
% 1.65/1.08  CNF conversion       : 0.03
% 1.65/1.08  Main loop            : 0.16
% 1.65/1.08  Inferencing          : 0.06
% 1.65/1.08  Reduction            : 0.04
% 1.65/1.08  Demodulation         : 0.02
% 1.65/1.08  BG Simplification    : 0.01
% 1.65/1.08  Subsumption          : 0.04
% 1.65/1.08  Abstraction          : 0.01
% 1.65/1.08  MUC search           : 0.00
% 1.65/1.08  Cooper               : 0.00
% 1.65/1.08  Total                : 0.46
% 1.65/1.08  Index Insertion      : 0.00
% 1.65/1.08  Index Deletion       : 0.00
% 1.65/1.08  Index Matching       : 0.00
% 1.65/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
