%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:27 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   35 (  52 expanded)
%              Number of leaves         :   22 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   38 (  64 expanded)
%              Number of equality atoms :   13 (  26 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k8_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_4 > #skF_2 > #skF_8 > #skF_3 > #skF_7

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( C = k8_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(E,A)
                  & r2_hidden(k4_tarski(D,E),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_1)).

tff(f_61,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_32,plain,(
    ! [A_23] :
      ( r2_hidden('#skF_5'(A_23),A_23)
      | v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,(
    ! [A_43,B_44] : ~ r2_hidden(A_43,k2_zfmisc_1(A_43,B_44)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_65,plain,(
    ! [A_46] : ~ r2_hidden(A_46,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_57])).

tff(c_70,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32,c_65])).

tff(c_163,plain,(
    ! [A_80,B_81,C_82] :
      ( r2_hidden(k4_tarski('#skF_1'(A_80,B_81,C_82),'#skF_2'(A_80,B_81,C_82)),B_81)
      | r2_hidden(k4_tarski('#skF_3'(A_80,B_81,C_82),'#skF_4'(A_80,B_81,C_82)),C_82)
      | k8_relat_1(A_80,B_81) = C_82
      | ~ v1_relat_1(C_82)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_63,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_57])).

tff(c_178,plain,(
    ! [A_80,C_82] :
      ( r2_hidden(k4_tarski('#skF_3'(A_80,k1_xboole_0,C_82),'#skF_4'(A_80,k1_xboole_0,C_82)),C_82)
      | k8_relat_1(A_80,k1_xboole_0) = C_82
      | ~ v1_relat_1(C_82)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_163,c_63])).

tff(c_233,plain,(
    ! [A_84,C_85] :
      ( r2_hidden(k4_tarski('#skF_3'(A_84,k1_xboole_0,C_85),'#skF_4'(A_84,k1_xboole_0,C_85)),C_85)
      | k8_relat_1(A_84,k1_xboole_0) = C_85
      | ~ v1_relat_1(C_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_178])).

tff(c_248,plain,(
    ! [A_84] :
      ( k8_relat_1(A_84,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_233,c_63])).

tff(c_254,plain,(
    ! [A_84] : k8_relat_1(A_84,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_248])).

tff(c_34,plain,(
    k8_relat_1('#skF_8',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:00:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.22  
% 1.97/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.22  %$ r2_hidden > v1_relat_1 > k8_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_4 > #skF_2 > #skF_8 > #skF_3 > #skF_7
% 1.97/1.22  
% 1.97/1.22  %Foreground sorts:
% 1.97/1.22  
% 1.97/1.22  
% 1.97/1.22  %Background operators:
% 1.97/1.22  
% 1.97/1.22  
% 1.97/1.22  %Foreground operators:
% 1.97/1.22  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.97/1.22  tff('#skF_5', type, '#skF_5': $i > $i).
% 1.97/1.22  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 1.97/1.22  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.97/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.22  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.97/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.22  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.97/1.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.97/1.22  tff('#skF_8', type, '#skF_8': $i).
% 1.97/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.97/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.97/1.22  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.97/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.22  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 1.97/1.22  
% 2.08/1.23  tff(f_58, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.08/1.23  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.08/1.23  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.08/1.23  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k8_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(E, A) & r2_hidden(k4_tarski(D, E), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_relat_1)).
% 2.08/1.23  tff(f_61, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_relat_1)).
% 2.08/1.23  tff(c_32, plain, (![A_23]: (r2_hidden('#skF_5'(A_23), A_23) | v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.08/1.23  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.08/1.23  tff(c_57, plain, (![A_43, B_44]: (~r2_hidden(A_43, k2_zfmisc_1(A_43, B_44)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.08/1.23  tff(c_65, plain, (![A_46]: (~r2_hidden(A_46, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_57])).
% 2.08/1.23  tff(c_70, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_65])).
% 2.08/1.23  tff(c_163, plain, (![A_80, B_81, C_82]: (r2_hidden(k4_tarski('#skF_1'(A_80, B_81, C_82), '#skF_2'(A_80, B_81, C_82)), B_81) | r2_hidden(k4_tarski('#skF_3'(A_80, B_81, C_82), '#skF_4'(A_80, B_81, C_82)), C_82) | k8_relat_1(A_80, B_81)=C_82 | ~v1_relat_1(C_82) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.08/1.23  tff(c_63, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_57])).
% 2.08/1.23  tff(c_178, plain, (![A_80, C_82]: (r2_hidden(k4_tarski('#skF_3'(A_80, k1_xboole_0, C_82), '#skF_4'(A_80, k1_xboole_0, C_82)), C_82) | k8_relat_1(A_80, k1_xboole_0)=C_82 | ~v1_relat_1(C_82) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_163, c_63])).
% 2.08/1.23  tff(c_233, plain, (![A_84, C_85]: (r2_hidden(k4_tarski('#skF_3'(A_84, k1_xboole_0, C_85), '#skF_4'(A_84, k1_xboole_0, C_85)), C_85) | k8_relat_1(A_84, k1_xboole_0)=C_85 | ~v1_relat_1(C_85))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_178])).
% 2.08/1.23  tff(c_248, plain, (![A_84]: (k8_relat_1(A_84, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_233, c_63])).
% 2.08/1.23  tff(c_254, plain, (![A_84]: (k8_relat_1(A_84, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_70, c_248])).
% 2.08/1.23  tff(c_34, plain, (k8_relat_1('#skF_8', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.08/1.23  tff(c_259, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_254, c_34])).
% 2.08/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.23  
% 2.08/1.23  Inference rules
% 2.08/1.23  ----------------------
% 2.08/1.23  #Ref     : 1
% 2.08/1.23  #Sup     : 46
% 2.08/1.23  #Fact    : 0
% 2.08/1.23  #Define  : 0
% 2.08/1.23  #Split   : 0
% 2.08/1.23  #Chain   : 0
% 2.08/1.23  #Close   : 0
% 2.08/1.23  
% 2.08/1.23  Ordering : KBO
% 2.08/1.23  
% 2.08/1.23  Simplification rules
% 2.08/1.23  ----------------------
% 2.08/1.23  #Subsume      : 6
% 2.08/1.23  #Demod        : 18
% 2.08/1.23  #Tautology    : 16
% 2.08/1.23  #SimpNegUnit  : 4
% 2.08/1.23  #BackRed      : 2
% 2.08/1.23  
% 2.08/1.23  #Partial instantiations: 0
% 2.08/1.23  #Strategies tried      : 1
% 2.08/1.23  
% 2.08/1.23  Timing (in seconds)
% 2.08/1.23  ----------------------
% 2.08/1.23  Preprocessing        : 0.27
% 2.08/1.23  Parsing              : 0.14
% 2.08/1.23  CNF conversion       : 0.02
% 2.08/1.23  Main loop            : 0.20
% 2.08/1.23  Inferencing          : 0.08
% 2.08/1.23  Reduction            : 0.05
% 2.08/1.23  Demodulation         : 0.04
% 2.08/1.23  BG Simplification    : 0.01
% 2.08/1.23  Subsumption          : 0.04
% 2.08/1.23  Abstraction          : 0.01
% 2.08/1.23  MUC search           : 0.00
% 2.08/1.23  Cooper               : 0.00
% 2.08/1.23  Total                : 0.50
% 2.08/1.23  Index Insertion      : 0.00
% 2.08/1.23  Index Deletion       : 0.00
% 2.08/1.23  Index Matching       : 0.00
% 2.08/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
