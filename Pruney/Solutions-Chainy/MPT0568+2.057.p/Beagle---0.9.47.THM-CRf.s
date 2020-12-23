%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:28 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   42 (  71 expanded)
%              Number of leaves         :   24 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   42 (  94 expanded)
%              Number of equality atoms :   18 (  42 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_55,axiom,(
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

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_47,plain,(
    ! [B_56] : k2_zfmisc_1(k1_xboole_0,B_56) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_36,plain,(
    ! [A_51,B_52] : v1_relat_1(k2_zfmisc_1(A_51,B_52)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_51,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_36])).

tff(c_256,plain,(
    ! [A_109,B_110,C_111] :
      ( r2_hidden('#skF_2'(A_109,B_110,C_111),B_110)
      | r2_hidden('#skF_3'(A_109,B_110,C_111),C_111)
      | k10_relat_1(A_109,B_110) = C_111
      | ~ v1_relat_1(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_92,plain,(
    ! [B_61,A_62] :
      ( ~ r2_hidden(B_61,A_62)
      | k4_xboole_0(A_62,k1_tarski(B_61)) != A_62 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_97,plain,(
    ! [B_61] : ~ r2_hidden(B_61,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_92])).

tff(c_360,plain,(
    ! [A_112,C_113] :
      ( r2_hidden('#skF_3'(A_112,k1_xboole_0,C_113),C_113)
      | k10_relat_1(A_112,k1_xboole_0) = C_113
      | ~ v1_relat_1(A_112) ) ),
    inference(resolution,[status(thm)],[c_256,c_97])).

tff(c_414,plain,(
    ! [A_114] :
      ( k10_relat_1(A_114,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_114) ) ),
    inference(resolution,[status(thm)],[c_360,c_97])).

tff(c_421,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_51,c_414])).

tff(c_151,plain,(
    ! [D_77,A_78,B_79] :
      ( r2_hidden(k4_tarski(D_77,'#skF_4'(A_78,B_79,k10_relat_1(A_78,B_79),D_77)),A_78)
      | ~ r2_hidden(D_77,k10_relat_1(A_78,B_79))
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_161,plain,(
    ! [D_77,B_79] :
      ( ~ r2_hidden(D_77,k10_relat_1(k1_xboole_0,B_79))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_151,c_97])).

tff(c_166,plain,(
    ! [D_77,B_79] : ~ r2_hidden(D_77,k10_relat_1(k1_xboole_0,B_79)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_161])).

tff(c_575,plain,(
    ! [B_120,A_121] :
      ( k10_relat_1(k1_xboole_0,B_120) = k10_relat_1(A_121,k1_xboole_0)
      | ~ v1_relat_1(A_121) ) ),
    inference(resolution,[status(thm)],[c_360,c_166])).

tff(c_577,plain,(
    ! [B_120] : k10_relat_1(k1_xboole_0,k1_xboole_0) = k10_relat_1(k1_xboole_0,B_120) ),
    inference(resolution,[status(thm)],[c_51,c_575])).

tff(c_581,plain,(
    ! [B_120] : k10_relat_1(k1_xboole_0,B_120) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_577])).

tff(c_38,plain,(
    k10_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_597,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:33:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.38  
% 2.35/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.38  %$ r2_hidden > v1_relat_1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > k10_relat_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.35/1.38  
% 2.35/1.38  %Foreground sorts:
% 2.35/1.38  
% 2.35/1.38  
% 2.35/1.38  %Background operators:
% 2.35/1.38  
% 2.35/1.38  
% 2.35/1.38  %Foreground operators:
% 2.35/1.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.35/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.35/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.35/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.35/1.38  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.35/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.35/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.35/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.35/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.35/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.35/1.38  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.35/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.38  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.35/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.35/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.35/1.38  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.35/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.38  
% 2.35/1.39  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.35/1.39  tff(f_57, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.35/1.39  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 2.35/1.39  tff(f_27, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.35/1.39  tff(f_42, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.35/1.39  tff(f_60, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 2.35/1.39  tff(c_47, plain, (![B_56]: (k2_zfmisc_1(k1_xboole_0, B_56)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.35/1.39  tff(c_36, plain, (![A_51, B_52]: (v1_relat_1(k2_zfmisc_1(A_51, B_52)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.35/1.39  tff(c_51, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_47, c_36])).
% 2.35/1.39  tff(c_256, plain, (![A_109, B_110, C_111]: (r2_hidden('#skF_2'(A_109, B_110, C_111), B_110) | r2_hidden('#skF_3'(A_109, B_110, C_111), C_111) | k10_relat_1(A_109, B_110)=C_111 | ~v1_relat_1(A_109))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.35/1.39  tff(c_2, plain, (![A_1]: (k4_xboole_0(k1_xboole_0, A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.35/1.39  tff(c_92, plain, (![B_61, A_62]: (~r2_hidden(B_61, A_62) | k4_xboole_0(A_62, k1_tarski(B_61))!=A_62)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.35/1.39  tff(c_97, plain, (![B_61]: (~r2_hidden(B_61, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2, c_92])).
% 2.35/1.39  tff(c_360, plain, (![A_112, C_113]: (r2_hidden('#skF_3'(A_112, k1_xboole_0, C_113), C_113) | k10_relat_1(A_112, k1_xboole_0)=C_113 | ~v1_relat_1(A_112))), inference(resolution, [status(thm)], [c_256, c_97])).
% 2.35/1.39  tff(c_414, plain, (![A_114]: (k10_relat_1(A_114, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_114))), inference(resolution, [status(thm)], [c_360, c_97])).
% 2.35/1.39  tff(c_421, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_51, c_414])).
% 2.35/1.39  tff(c_151, plain, (![D_77, A_78, B_79]: (r2_hidden(k4_tarski(D_77, '#skF_4'(A_78, B_79, k10_relat_1(A_78, B_79), D_77)), A_78) | ~r2_hidden(D_77, k10_relat_1(A_78, B_79)) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.35/1.39  tff(c_161, plain, (![D_77, B_79]: (~r2_hidden(D_77, k10_relat_1(k1_xboole_0, B_79)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_151, c_97])).
% 2.35/1.39  tff(c_166, plain, (![D_77, B_79]: (~r2_hidden(D_77, k10_relat_1(k1_xboole_0, B_79)))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_161])).
% 2.35/1.39  tff(c_575, plain, (![B_120, A_121]: (k10_relat_1(k1_xboole_0, B_120)=k10_relat_1(A_121, k1_xboole_0) | ~v1_relat_1(A_121))), inference(resolution, [status(thm)], [c_360, c_166])).
% 2.35/1.39  tff(c_577, plain, (![B_120]: (k10_relat_1(k1_xboole_0, k1_xboole_0)=k10_relat_1(k1_xboole_0, B_120))), inference(resolution, [status(thm)], [c_51, c_575])).
% 2.35/1.39  tff(c_581, plain, (![B_120]: (k10_relat_1(k1_xboole_0, B_120)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_421, c_577])).
% 2.35/1.39  tff(c_38, plain, (k10_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.35/1.39  tff(c_597, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_581, c_38])).
% 2.35/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.39  
% 2.35/1.39  Inference rules
% 2.35/1.39  ----------------------
% 2.35/1.39  #Ref     : 0
% 2.35/1.39  #Sup     : 114
% 2.35/1.39  #Fact    : 0
% 2.35/1.39  #Define  : 0
% 2.35/1.39  #Split   : 0
% 2.35/1.39  #Chain   : 0
% 2.35/1.39  #Close   : 0
% 2.35/1.39  
% 2.35/1.39  Ordering : KBO
% 2.35/1.39  
% 2.35/1.39  Simplification rules
% 2.35/1.39  ----------------------
% 2.35/1.39  #Subsume      : 23
% 2.65/1.39  #Demod        : 45
% 2.65/1.39  #Tautology    : 27
% 2.65/1.39  #SimpNegUnit  : 5
% 2.65/1.39  #BackRed      : 7
% 2.65/1.39  
% 2.65/1.39  #Partial instantiations: 0
% 2.65/1.39  #Strategies tried      : 1
% 2.65/1.39  
% 2.65/1.39  Timing (in seconds)
% 2.65/1.39  ----------------------
% 2.65/1.39  Preprocessing        : 0.32
% 2.65/1.39  Parsing              : 0.16
% 2.65/1.39  CNF conversion       : 0.03
% 2.65/1.39  Main loop            : 0.28
% 2.65/1.39  Inferencing          : 0.10
% 2.65/1.39  Reduction            : 0.07
% 2.65/1.39  Demodulation         : 0.05
% 2.65/1.39  BG Simplification    : 0.02
% 2.65/1.39  Subsumption          : 0.07
% 2.65/1.39  Abstraction          : 0.02
% 2.65/1.39  MUC search           : 0.00
% 2.65/1.39  Cooper               : 0.00
% 2.65/1.39  Total                : 0.62
% 2.65/1.39  Index Insertion      : 0.00
% 2.65/1.39  Index Deletion       : 0.00
% 2.65/1.39  Index Matching       : 0.00
% 2.65/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
