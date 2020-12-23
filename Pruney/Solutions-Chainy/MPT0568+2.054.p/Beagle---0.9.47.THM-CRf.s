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
% DateTime   : Thu Dec  3 10:01:27 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
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

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_52,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

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
      | k10_relat_1(A_74,B_75) = C_76
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
      | k10_relat_1(A_91,k1_xboole_0) = C_92
      | ~ v1_relat_1(A_91) ) ),
    inference(resolution,[status(thm)],[c_106,c_62])).

tff(c_279,plain,(
    ! [A_93] :
      ( k10_relat_1(A_93,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_93) ) ),
    inference(resolution,[status(thm)],[c_240,c_62])).

tff(c_286,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_279])).

tff(c_150,plain,(
    ! [D_77,A_78,B_79] :
      ( r2_hidden(k4_tarski(D_77,'#skF_4'(A_78,B_79,k10_relat_1(A_78,B_79),D_77)),A_78)
      | ~ r2_hidden(D_77,k10_relat_1(A_78,B_79))
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_168,plain,(
    ! [D_77,B_79] :
      ( ~ r2_hidden(D_77,k10_relat_1(k1_xboole_0,B_79))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_150,c_62])).

tff(c_175,plain,(
    ! [D_77,B_79] : ~ r2_hidden(D_77,k10_relat_1(k1_xboole_0,B_79)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_168])).

tff(c_367,plain,(
    ! [B_96,A_97] :
      ( k10_relat_1(k1_xboole_0,B_96) = k10_relat_1(A_97,k1_xboole_0)
      | ~ v1_relat_1(A_97) ) ),
    inference(resolution,[status(thm)],[c_240,c_175])).

tff(c_369,plain,(
    ! [B_96] : k10_relat_1(k1_xboole_0,k1_xboole_0) = k10_relat_1(k1_xboole_0,B_96) ),
    inference(resolution,[status(thm)],[c_36,c_367])).

tff(c_373,plain,(
    ! [B_96] : k10_relat_1(k1_xboole_0,B_96) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_369])).

tff(c_30,plain,(
    k10_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:55:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.32  
% 1.91/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.32  %$ r2_hidden > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 1.91/1.32  
% 1.91/1.32  %Foreground sorts:
% 1.91/1.32  
% 1.91/1.32  
% 1.91/1.32  %Background operators:
% 1.91/1.32  
% 1.91/1.32  
% 1.91/1.32  %Foreground operators:
% 1.91/1.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.91/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.32  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.91/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.91/1.32  tff('#skF_5', type, '#skF_5': $i).
% 1.91/1.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.91/1.32  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 1.91/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.32  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.91/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.91/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.91/1.32  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.91/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.32  
% 1.91/1.33  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.91/1.33  tff(f_49, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.91/1.33  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 1.91/1.33  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.91/1.33  tff(f_52, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 1.91/1.33  tff(c_32, plain, (![B_51]: (k2_zfmisc_1(k1_xboole_0, B_51)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.91/1.33  tff(c_28, plain, (![A_47, B_48]: (v1_relat_1(k2_zfmisc_1(A_47, B_48)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.91/1.33  tff(c_36, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_32, c_28])).
% 1.91/1.33  tff(c_106, plain, (![A_74, B_75, C_76]: (r2_hidden('#skF_2'(A_74, B_75, C_76), B_75) | r2_hidden('#skF_3'(A_74, B_75, C_76), C_76) | k10_relat_1(A_74, B_75)=C_76 | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.91/1.33  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.91/1.33  tff(c_59, plain, (![A_53, B_54]: (~r2_hidden(A_53, k2_zfmisc_1(A_53, B_54)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.91/1.33  tff(c_62, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_59])).
% 1.91/1.33  tff(c_240, plain, (![A_91, C_92]: (r2_hidden('#skF_3'(A_91, k1_xboole_0, C_92), C_92) | k10_relat_1(A_91, k1_xboole_0)=C_92 | ~v1_relat_1(A_91))), inference(resolution, [status(thm)], [c_106, c_62])).
% 1.91/1.33  tff(c_279, plain, (![A_93]: (k10_relat_1(A_93, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_93))), inference(resolution, [status(thm)], [c_240, c_62])).
% 1.91/1.33  tff(c_286, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_279])).
% 1.91/1.33  tff(c_150, plain, (![D_77, A_78, B_79]: (r2_hidden(k4_tarski(D_77, '#skF_4'(A_78, B_79, k10_relat_1(A_78, B_79), D_77)), A_78) | ~r2_hidden(D_77, k10_relat_1(A_78, B_79)) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.91/1.33  tff(c_168, plain, (![D_77, B_79]: (~r2_hidden(D_77, k10_relat_1(k1_xboole_0, B_79)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_150, c_62])).
% 1.91/1.33  tff(c_175, plain, (![D_77, B_79]: (~r2_hidden(D_77, k10_relat_1(k1_xboole_0, B_79)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_168])).
% 1.91/1.33  tff(c_367, plain, (![B_96, A_97]: (k10_relat_1(k1_xboole_0, B_96)=k10_relat_1(A_97, k1_xboole_0) | ~v1_relat_1(A_97))), inference(resolution, [status(thm)], [c_240, c_175])).
% 1.91/1.33  tff(c_369, plain, (![B_96]: (k10_relat_1(k1_xboole_0, k1_xboole_0)=k10_relat_1(k1_xboole_0, B_96))), inference(resolution, [status(thm)], [c_36, c_367])).
% 1.91/1.33  tff(c_373, plain, (![B_96]: (k10_relat_1(k1_xboole_0, B_96)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_286, c_369])).
% 1.91/1.33  tff(c_30, plain, (k10_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.91/1.33  tff(c_426, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_373, c_30])).
% 1.91/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.33  
% 1.91/1.33  Inference rules
% 1.91/1.33  ----------------------
% 1.91/1.33  #Ref     : 0
% 1.91/1.33  #Sup     : 82
% 1.91/1.33  #Fact    : 0
% 1.91/1.33  #Define  : 0
% 1.91/1.33  #Split   : 0
% 1.91/1.33  #Chain   : 0
% 1.91/1.33  #Close   : 0
% 1.91/1.33  
% 1.91/1.33  Ordering : KBO
% 2.26/1.33  
% 2.26/1.33  Simplification rules
% 2.26/1.33  ----------------------
% 2.26/1.33  #Subsume      : 18
% 2.26/1.33  #Demod        : 32
% 2.26/1.33  #Tautology    : 16
% 2.26/1.33  #SimpNegUnit  : 3
% 2.26/1.33  #BackRed      : 5
% 2.26/1.33  
% 2.26/1.33  #Partial instantiations: 0
% 2.26/1.33  #Strategies tried      : 1
% 2.26/1.33  
% 2.26/1.33  Timing (in seconds)
% 2.26/1.33  ----------------------
% 2.26/1.33  Preprocessing        : 0.27
% 2.26/1.33  Parsing              : 0.14
% 2.26/1.33  CNF conversion       : 0.02
% 2.26/1.33  Main loop            : 0.23
% 2.26/1.33  Inferencing          : 0.09
% 2.26/1.33  Reduction            : 0.06
% 2.26/1.33  Demodulation         : 0.04
% 2.26/1.33  BG Simplification    : 0.01
% 2.26/1.33  Subsumption          : 0.05
% 2.26/1.33  Abstraction          : 0.01
% 2.26/1.33  MUC search           : 0.00
% 2.26/1.33  Cooper               : 0.00
% 2.26/1.33  Total                : 0.53
% 2.26/1.33  Index Insertion      : 0.00
% 2.26/1.33  Index Deletion       : 0.00
% 2.26/1.34  Index Matching       : 0.00
% 2.26/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
