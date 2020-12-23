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
% DateTime   : Thu Dec  3 10:00:38 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   37 (  67 expanded)
%              Number of leaves         :   19 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   39 (  94 expanded)
%              Number of equality atoms :   15 (  42 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_32,plain,(
    ! [B_51] : k2_zfmisc_1(k1_xboole_0,B_51) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ! [A_47,B_48] : v1_relat_1(k2_zfmisc_1(A_47,B_48)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_36,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_28])).

tff(c_106,plain,(
    ! [A_74,B_75,C_76] :
      ( r2_hidden('#skF_2'(A_74,B_75,C_76),B_75)
      | r2_hidden('#skF_3'(A_74,B_75,C_76),C_76)
      | k9_relat_1(A_74,B_75) = C_76
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ! [A_53,B_54] : ~ r2_hidden(A_53,k2_zfmisc_1(A_53,B_54)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_62,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_59])).

tff(c_240,plain,(
    ! [A_91,C_92] :
      ( r2_hidden('#skF_3'(A_91,k1_xboole_0,C_92),C_92)
      | k9_relat_1(A_91,k1_xboole_0) = C_92
      | ~ v1_relat_1(A_91) ) ),
    inference(resolution,[status(thm)],[c_106,c_62])).

tff(c_279,plain,(
    ! [A_93] :
      ( k9_relat_1(A_93,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_93) ) ),
    inference(resolution,[status(thm)],[c_240,c_62])).

tff(c_286,plain,(
    k9_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_279])).

tff(c_150,plain,(
    ! [A_77,B_78,D_79] :
      ( r2_hidden(k4_tarski('#skF_4'(A_77,B_78,k9_relat_1(A_77,B_78),D_79),D_79),A_77)
      | ~ r2_hidden(D_79,k9_relat_1(A_77,B_78))
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_168,plain,(
    ! [D_79,B_78] :
      ( ~ r2_hidden(D_79,k9_relat_1(k1_xboole_0,B_78))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_150,c_62])).

tff(c_175,plain,(
    ! [D_79,B_78] : ~ r2_hidden(D_79,k9_relat_1(k1_xboole_0,B_78)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_168])).

tff(c_367,plain,(
    ! [B_96,A_97] :
      ( k9_relat_1(k1_xboole_0,B_96) = k9_relat_1(A_97,k1_xboole_0)
      | ~ v1_relat_1(A_97) ) ),
    inference(resolution,[status(thm)],[c_240,c_175])).

tff(c_369,plain,(
    ! [B_96] : k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1(k1_xboole_0,B_96) ),
    inference(resolution,[status(thm)],[c_36,c_367])).

tff(c_373,plain,(
    ! [B_96] : k9_relat_1(k1_xboole_0,B_96) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_369])).

tff(c_30,plain,(
    k9_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:47:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.26  
% 2.10/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.26  %$ r2_hidden > v1_relat_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.10/1.26  
% 2.10/1.26  %Foreground sorts:
% 2.10/1.26  
% 2.10/1.26  
% 2.10/1.26  %Background operators:
% 2.10/1.26  
% 2.10/1.26  
% 2.10/1.26  %Foreground operators:
% 2.10/1.26  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.10/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.26  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.10/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.10/1.26  tff('#skF_5', type, '#skF_5': $i).
% 2.10/1.26  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.10/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.10/1.26  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.10/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.10/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.10/1.26  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.10/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.26  
% 2.10/1.27  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.10/1.27  tff(f_49, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.10/1.27  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d13_relat_1)).
% 2.10/1.27  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.10/1.27  tff(f_52, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 2.10/1.27  tff(c_32, plain, (![B_51]: (k2_zfmisc_1(k1_xboole_0, B_51)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.10/1.27  tff(c_28, plain, (![A_47, B_48]: (v1_relat_1(k2_zfmisc_1(A_47, B_48)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.10/1.27  tff(c_36, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_28])).
% 2.10/1.27  tff(c_106, plain, (![A_74, B_75, C_76]: (r2_hidden('#skF_2'(A_74, B_75, C_76), B_75) | r2_hidden('#skF_3'(A_74, B_75, C_76), C_76) | k9_relat_1(A_74, B_75)=C_76 | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.10/1.27  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.10/1.27  tff(c_59, plain, (![A_53, B_54]: (~r2_hidden(A_53, k2_zfmisc_1(A_53, B_54)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.10/1.27  tff(c_62, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_59])).
% 2.10/1.27  tff(c_240, plain, (![A_91, C_92]: (r2_hidden('#skF_3'(A_91, k1_xboole_0, C_92), C_92) | k9_relat_1(A_91, k1_xboole_0)=C_92 | ~v1_relat_1(A_91))), inference(resolution, [status(thm)], [c_106, c_62])).
% 2.10/1.27  tff(c_279, plain, (![A_93]: (k9_relat_1(A_93, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_93))), inference(resolution, [status(thm)], [c_240, c_62])).
% 2.10/1.27  tff(c_286, plain, (k9_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_279])).
% 2.10/1.27  tff(c_150, plain, (![A_77, B_78, D_79]: (r2_hidden(k4_tarski('#skF_4'(A_77, B_78, k9_relat_1(A_77, B_78), D_79), D_79), A_77) | ~r2_hidden(D_79, k9_relat_1(A_77, B_78)) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.10/1.27  tff(c_168, plain, (![D_79, B_78]: (~r2_hidden(D_79, k9_relat_1(k1_xboole_0, B_78)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_150, c_62])).
% 2.10/1.27  tff(c_175, plain, (![D_79, B_78]: (~r2_hidden(D_79, k9_relat_1(k1_xboole_0, B_78)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_168])).
% 2.10/1.27  tff(c_367, plain, (![B_96, A_97]: (k9_relat_1(k1_xboole_0, B_96)=k9_relat_1(A_97, k1_xboole_0) | ~v1_relat_1(A_97))), inference(resolution, [status(thm)], [c_240, c_175])).
% 2.10/1.27  tff(c_369, plain, (![B_96]: (k9_relat_1(k1_xboole_0, k1_xboole_0)=k9_relat_1(k1_xboole_0, B_96))), inference(resolution, [status(thm)], [c_36, c_367])).
% 2.10/1.27  tff(c_373, plain, (![B_96]: (k9_relat_1(k1_xboole_0, B_96)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_286, c_369])).
% 2.10/1.27  tff(c_30, plain, (k9_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.10/1.27  tff(c_426, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_373, c_30])).
% 2.10/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.27  
% 2.10/1.27  Inference rules
% 2.10/1.27  ----------------------
% 2.10/1.27  #Ref     : 0
% 2.10/1.27  #Sup     : 82
% 2.10/1.27  #Fact    : 0
% 2.10/1.27  #Define  : 0
% 2.10/1.27  #Split   : 0
% 2.10/1.27  #Chain   : 0
% 2.10/1.27  #Close   : 0
% 2.10/1.27  
% 2.10/1.27  Ordering : KBO
% 2.10/1.27  
% 2.10/1.27  Simplification rules
% 2.10/1.27  ----------------------
% 2.10/1.27  #Subsume      : 18
% 2.10/1.27  #Demod        : 32
% 2.10/1.27  #Tautology    : 16
% 2.10/1.27  #SimpNegUnit  : 3
% 2.10/1.27  #BackRed      : 5
% 2.10/1.27  
% 2.10/1.27  #Partial instantiations: 0
% 2.10/1.27  #Strategies tried      : 1
% 2.10/1.27  
% 2.10/1.27  Timing (in seconds)
% 2.10/1.27  ----------------------
% 2.10/1.28  Preprocessing        : 0.28
% 2.10/1.28  Parsing              : 0.15
% 2.10/1.28  CNF conversion       : 0.02
% 2.10/1.28  Main loop            : 0.23
% 2.10/1.28  Inferencing          : 0.09
% 2.10/1.28  Reduction            : 0.06
% 2.10/1.28  Demodulation         : 0.04
% 2.10/1.28  BG Simplification    : 0.01
% 2.10/1.28  Subsumption          : 0.05
% 2.10/1.28  Abstraction          : 0.01
% 2.10/1.28  MUC search           : 0.00
% 2.10/1.28  Cooper               : 0.00
% 2.10/1.28  Total                : 0.53
% 2.10/1.28  Index Insertion      : 0.00
% 2.10/1.28  Index Deletion       : 0.00
% 2.10/1.28  Index Matching       : 0.00
% 2.10/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
