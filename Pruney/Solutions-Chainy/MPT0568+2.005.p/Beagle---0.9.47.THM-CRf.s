%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:21 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   40 (  68 expanded)
%              Number of leaves         :   21 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   45 (  94 expanded)
%              Number of equality atoms :   15 (  30 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_52,axiom,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_55,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_33,plain,(
    ! [A_48] :
      ( v1_relat_1(A_48)
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_37,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_33])).

tff(c_108,plain,(
    ! [A_75,B_76,C_77] :
      ( r2_hidden('#skF_2'(A_75,B_76,C_77),B_76)
      | r2_hidden('#skF_3'(A_75,B_76,C_77),C_77)
      | k10_relat_1(A_75,B_76) = C_77
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_6,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_60,plain,(
    ! [A_51,B_52] : ~ r2_hidden(A_51,k2_zfmisc_1(A_51,B_52)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_63,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_60])).

tff(c_152,plain,(
    ! [A_78,C_79] :
      ( r2_hidden('#skF_3'(A_78,k1_xboole_0,C_79),C_79)
      | k10_relat_1(A_78,k1_xboole_0) = C_79
      | ~ v1_relat_1(A_78) ) ),
    inference(resolution,[status(thm)],[c_108,c_63])).

tff(c_176,plain,(
    ! [A_80] :
      ( k10_relat_1(A_80,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_80) ) ),
    inference(resolution,[status(thm)],[c_152,c_63])).

tff(c_180,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_37,c_176])).

tff(c_147,plain,(
    ! [A_75,C_77] :
      ( r2_hidden('#skF_3'(A_75,k1_xboole_0,C_77),C_77)
      | k10_relat_1(A_75,k1_xboole_0) = C_77
      | ~ v1_relat_1(A_75) ) ),
    inference(resolution,[status(thm)],[c_108,c_63])).

tff(c_181,plain,(
    ! [D_81,A_82,B_83] :
      ( r2_hidden(k4_tarski(D_81,'#skF_4'(A_82,B_83,k10_relat_1(A_82,B_83),D_81)),A_82)
      | ~ r2_hidden(D_81,k10_relat_1(A_82,B_83))
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_199,plain,(
    ! [D_81,B_83] :
      ( ~ r2_hidden(D_81,k10_relat_1(k1_xboole_0,B_83))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_181,c_63])).

tff(c_238,plain,(
    ! [D_84,B_85] : ~ r2_hidden(D_84,k10_relat_1(k1_xboole_0,B_85)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_199])).

tff(c_266,plain,(
    ! [B_86,A_87] :
      ( k10_relat_1(k1_xboole_0,B_86) = k10_relat_1(A_87,k1_xboole_0)
      | ~ v1_relat_1(A_87) ) ),
    inference(resolution,[status(thm)],[c_147,c_238])).

tff(c_268,plain,(
    ! [B_86] : k10_relat_1(k1_xboole_0,k1_xboole_0) = k10_relat_1(k1_xboole_0,B_86) ),
    inference(resolution,[status(thm)],[c_37,c_266])).

tff(c_270,plain,(
    ! [B_86] : k10_relat_1(k1_xboole_0,B_86) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_268])).

tff(c_32,plain,(
    k10_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_276,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:24:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.60  
% 2.43/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.60  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.43/1.60  
% 2.43/1.60  %Foreground sorts:
% 2.43/1.60  
% 2.43/1.60  
% 2.43/1.60  %Background operators:
% 2.43/1.60  
% 2.43/1.60  
% 2.43/1.60  %Foreground operators:
% 2.43/1.60  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.43/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.43/1.60  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.43/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.43/1.60  tff('#skF_5', type, '#skF_5': $i).
% 2.43/1.60  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.43/1.60  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.43/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.60  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.43/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.43/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.43/1.60  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.43/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.43/1.60  
% 2.57/1.62  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.57/1.62  tff(f_39, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 2.57/1.62  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d14_relat_1)).
% 2.57/1.62  tff(f_32, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.57/1.62  tff(f_35, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.57/1.62  tff(f_55, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 2.57/1.62  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.57/1.62  tff(c_33, plain, (![A_48]: (v1_relat_1(A_48) | ~v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.57/1.62  tff(c_37, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_33])).
% 2.57/1.62  tff(c_108, plain, (![A_75, B_76, C_77]: (r2_hidden('#skF_2'(A_75, B_76, C_77), B_76) | r2_hidden('#skF_3'(A_75, B_76, C_77), C_77) | k10_relat_1(A_75, B_76)=C_77 | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.57/1.62  tff(c_6, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.57/1.62  tff(c_60, plain, (![A_51, B_52]: (~r2_hidden(A_51, k2_zfmisc_1(A_51, B_52)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.57/1.62  tff(c_63, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_60])).
% 2.57/1.62  tff(c_152, plain, (![A_78, C_79]: (r2_hidden('#skF_3'(A_78, k1_xboole_0, C_79), C_79) | k10_relat_1(A_78, k1_xboole_0)=C_79 | ~v1_relat_1(A_78))), inference(resolution, [status(thm)], [c_108, c_63])).
% 2.57/1.62  tff(c_176, plain, (![A_80]: (k10_relat_1(A_80, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_80))), inference(resolution, [status(thm)], [c_152, c_63])).
% 2.57/1.62  tff(c_180, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_37, c_176])).
% 2.57/1.62  tff(c_147, plain, (![A_75, C_77]: (r2_hidden('#skF_3'(A_75, k1_xboole_0, C_77), C_77) | k10_relat_1(A_75, k1_xboole_0)=C_77 | ~v1_relat_1(A_75))), inference(resolution, [status(thm)], [c_108, c_63])).
% 2.57/1.62  tff(c_181, plain, (![D_81, A_82, B_83]: (r2_hidden(k4_tarski(D_81, '#skF_4'(A_82, B_83, k10_relat_1(A_82, B_83), D_81)), A_82) | ~r2_hidden(D_81, k10_relat_1(A_82, B_83)) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.57/1.62  tff(c_199, plain, (![D_81, B_83]: (~r2_hidden(D_81, k10_relat_1(k1_xboole_0, B_83)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_181, c_63])).
% 2.57/1.62  tff(c_238, plain, (![D_84, B_85]: (~r2_hidden(D_84, k10_relat_1(k1_xboole_0, B_85)))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_199])).
% 2.57/1.62  tff(c_266, plain, (![B_86, A_87]: (k10_relat_1(k1_xboole_0, B_86)=k10_relat_1(A_87, k1_xboole_0) | ~v1_relat_1(A_87))), inference(resolution, [status(thm)], [c_147, c_238])).
% 2.57/1.62  tff(c_268, plain, (![B_86]: (k10_relat_1(k1_xboole_0, k1_xboole_0)=k10_relat_1(k1_xboole_0, B_86))), inference(resolution, [status(thm)], [c_37, c_266])).
% 2.57/1.62  tff(c_270, plain, (![B_86]: (k10_relat_1(k1_xboole_0, B_86)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_180, c_268])).
% 2.57/1.62  tff(c_32, plain, (k10_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.57/1.62  tff(c_276, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_270, c_32])).
% 2.57/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.62  
% 2.57/1.62  Inference rules
% 2.57/1.62  ----------------------
% 2.57/1.62  #Ref     : 0
% 2.57/1.62  #Sup     : 50
% 2.57/1.62  #Fact    : 0
% 2.57/1.62  #Define  : 0
% 2.57/1.62  #Split   : 0
% 2.57/1.62  #Chain   : 0
% 2.57/1.62  #Close   : 0
% 2.57/1.62  
% 2.57/1.62  Ordering : KBO
% 2.57/1.62  
% 2.57/1.62  Simplification rules
% 2.57/1.62  ----------------------
% 2.57/1.62  #Subsume      : 9
% 2.57/1.62  #Demod        : 13
% 2.57/1.62  #Tautology    : 11
% 2.57/1.62  #SimpNegUnit  : 2
% 2.57/1.62  #BackRed      : 3
% 2.57/1.62  
% 2.57/1.62  #Partial instantiations: 0
% 2.57/1.62  #Strategies tried      : 1
% 2.57/1.62  
% 2.57/1.62  Timing (in seconds)
% 2.57/1.62  ----------------------
% 2.57/1.63  Preprocessing        : 0.48
% 2.57/1.63  Parsing              : 0.25
% 2.57/1.63  CNF conversion       : 0.04
% 2.57/1.63  Main loop            : 0.33
% 2.57/1.63  Inferencing          : 0.13
% 2.57/1.63  Reduction            : 0.08
% 2.57/1.63  Demodulation         : 0.06
% 2.57/1.63  BG Simplification    : 0.02
% 2.57/1.63  Subsumption          : 0.07
% 2.57/1.63  Abstraction          : 0.02
% 2.57/1.63  MUC search           : 0.00
% 2.57/1.63  Cooper               : 0.00
% 2.57/1.63  Total                : 0.85
% 2.57/1.63  Index Insertion      : 0.00
% 2.57/1.63  Index Deletion       : 0.00
% 2.57/1.63  Index Matching       : 0.00
% 2.57/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
