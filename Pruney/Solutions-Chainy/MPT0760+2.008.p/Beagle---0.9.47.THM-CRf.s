%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:35 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   32 (  34 expanded)
%              Number of leaves         :   19 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   40 (  46 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k3_relat_1(B))
          | k1_wellord1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_wellord1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k1_wellord1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( D != B
                & r2_hidden(k4_tarski(D,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_32,plain,(
    k1_wellord1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_36,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_256,plain,(
    ! [A_82,B_83,C_84] :
      ( r2_hidden(k4_tarski('#skF_1'(A_82,B_83,C_84),B_83),A_82)
      | r2_hidden('#skF_2'(A_82,B_83,C_84),C_84)
      | k1_wellord1(A_82,B_83) = C_84
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [B_6,C_7,A_5] :
      ( r2_hidden(B_6,k3_relat_1(C_7))
      | ~ r2_hidden(k4_tarski(A_5,B_6),C_7)
      | ~ v1_relat_1(C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_342,plain,(
    ! [B_85,A_86,C_87] :
      ( r2_hidden(B_85,k3_relat_1(A_86))
      | r2_hidden('#skF_2'(A_86,B_85,C_87),C_87)
      | k1_wellord1(A_86,B_85) = C_87
      | ~ v1_relat_1(A_86) ) ),
    inference(resolution,[status(thm)],[c_256,c_10])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ! [A_22,B_23] : ~ r2_hidden(A_22,k2_zfmisc_1(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_62,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_59])).

tff(c_387,plain,(
    ! [B_91,A_92] :
      ( r2_hidden(B_91,k3_relat_1(A_92))
      | k1_wellord1(A_92,B_91) = k1_xboole_0
      | ~ v1_relat_1(A_92) ) ),
    inference(resolution,[status(thm)],[c_342,c_62])).

tff(c_34,plain,(
    ~ r2_hidden('#skF_3',k3_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_410,plain,
    ( k1_wellord1('#skF_4','#skF_3') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_387,c_34])).

tff(c_418,plain,(
    k1_wellord1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_410])).

tff(c_420,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_418])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:36:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.34  
% 2.47/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.35  %$ r2_hidden > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.47/1.35  
% 2.47/1.35  %Foreground sorts:
% 2.47/1.35  
% 2.47/1.35  
% 2.47/1.35  %Background operators:
% 2.47/1.35  
% 2.47/1.35  
% 2.47/1.35  %Foreground operators:
% 2.47/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.47/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.47/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.35  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.47/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.47/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.47/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.47/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.47/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.47/1.35  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 2.47/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.35  
% 2.47/1.36  tff(f_62, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k3_relat_1(B)) | (k1_wellord1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_wellord1)).
% 2.47/1.36  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k1_wellord1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (~(D = B) & r2_hidden(k4_tarski(D, B), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord1)).
% 2.47/1.36  tff(f_42, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relat_1)).
% 2.47/1.36  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.47/1.36  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.47/1.36  tff(c_32, plain, (k1_wellord1('#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.47/1.36  tff(c_36, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.47/1.36  tff(c_256, plain, (![A_82, B_83, C_84]: (r2_hidden(k4_tarski('#skF_1'(A_82, B_83, C_84), B_83), A_82) | r2_hidden('#skF_2'(A_82, B_83, C_84), C_84) | k1_wellord1(A_82, B_83)=C_84 | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.47/1.36  tff(c_10, plain, (![B_6, C_7, A_5]: (r2_hidden(B_6, k3_relat_1(C_7)) | ~r2_hidden(k4_tarski(A_5, B_6), C_7) | ~v1_relat_1(C_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.47/1.36  tff(c_342, plain, (![B_85, A_86, C_87]: (r2_hidden(B_85, k3_relat_1(A_86)) | r2_hidden('#skF_2'(A_86, B_85, C_87), C_87) | k1_wellord1(A_86, B_85)=C_87 | ~v1_relat_1(A_86))), inference(resolution, [status(thm)], [c_256, c_10])).
% 2.47/1.36  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.47/1.36  tff(c_59, plain, (![A_22, B_23]: (~r2_hidden(A_22, k2_zfmisc_1(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.47/1.36  tff(c_62, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_59])).
% 2.47/1.36  tff(c_387, plain, (![B_91, A_92]: (r2_hidden(B_91, k3_relat_1(A_92)) | k1_wellord1(A_92, B_91)=k1_xboole_0 | ~v1_relat_1(A_92))), inference(resolution, [status(thm)], [c_342, c_62])).
% 2.47/1.36  tff(c_34, plain, (~r2_hidden('#skF_3', k3_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.47/1.36  tff(c_410, plain, (k1_wellord1('#skF_4', '#skF_3')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_387, c_34])).
% 2.47/1.36  tff(c_418, plain, (k1_wellord1('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_410])).
% 2.47/1.36  tff(c_420, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_418])).
% 2.47/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.36  
% 2.47/1.36  Inference rules
% 2.47/1.36  ----------------------
% 2.47/1.36  #Ref     : 0
% 2.47/1.36  #Sup     : 77
% 2.47/1.36  #Fact    : 0
% 2.47/1.36  #Define  : 0
% 2.47/1.36  #Split   : 2
% 2.47/1.36  #Chain   : 0
% 2.47/1.36  #Close   : 0
% 2.47/1.36  
% 2.47/1.36  Ordering : KBO
% 2.47/1.36  
% 2.47/1.36  Simplification rules
% 2.47/1.36  ----------------------
% 2.47/1.36  #Subsume      : 8
% 2.47/1.36  #Demod        : 8
% 2.47/1.36  #Tautology    : 11
% 2.47/1.36  #SimpNegUnit  : 1
% 2.47/1.36  #BackRed      : 0
% 2.47/1.36  
% 2.47/1.36  #Partial instantiations: 0
% 2.47/1.36  #Strategies tried      : 1
% 2.47/1.36  
% 2.47/1.36  Timing (in seconds)
% 2.47/1.36  ----------------------
% 2.47/1.36  Preprocessing        : 0.30
% 2.47/1.36  Parsing              : 0.16
% 2.47/1.36  CNF conversion       : 0.02
% 2.47/1.36  Main loop            : 0.30
% 2.47/1.36  Inferencing          : 0.11
% 2.47/1.36  Reduction            : 0.07
% 2.47/1.36  Demodulation         : 0.04
% 2.47/1.36  BG Simplification    : 0.02
% 2.47/1.36  Subsumption          : 0.08
% 2.47/1.36  Abstraction          : 0.02
% 2.47/1.36  MUC search           : 0.00
% 2.47/1.36  Cooper               : 0.00
% 2.47/1.36  Total                : 0.62
% 2.47/1.36  Index Insertion      : 0.00
% 2.47/1.37  Index Deletion       : 0.00
% 2.47/1.37  Index Matching       : 0.00
% 2.47/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
