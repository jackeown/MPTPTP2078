%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:27 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   39 (  68 expanded)
%              Number of leaves         :   21 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   40 (  88 expanded)
%              Number of equality atoms :   16 (  36 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_50,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_49,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

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

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_53,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_30,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_37,plain,(
    ! [A_48] : v1_relat_1(k6_relat_1(A_48)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_39,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_37])).

tff(c_224,plain,(
    ! [A_105,B_106,C_107] :
      ( r2_hidden('#skF_2'(A_105,B_106,C_107),B_106)
      | r2_hidden('#skF_3'(A_105,B_106,C_107),C_107)
      | k10_relat_1(A_105,B_106) = C_107
      | ~ v1_relat_1(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    ! [A_51,B_52] : ~ r2_hidden(A_51,k2_zfmisc_1(A_51,B_52)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_68,plain,(
    ! [A_1] : ~ r2_hidden(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_62])).

tff(c_348,plain,(
    ! [A_108,C_109] :
      ( r2_hidden('#skF_3'(A_108,k1_xboole_0,C_109),C_109)
      | k10_relat_1(A_108,k1_xboole_0) = C_109
      | ~ v1_relat_1(A_108) ) ),
    inference(resolution,[status(thm)],[c_224,c_68])).

tff(c_412,plain,(
    ! [A_110] :
      ( k10_relat_1(A_110,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_110) ) ),
    inference(resolution,[status(thm)],[c_348,c_68])).

tff(c_419,plain,(
    k10_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_39,c_412])).

tff(c_109,plain,(
    ! [D_72,A_73,B_74] :
      ( r2_hidden(k4_tarski(D_72,'#skF_4'(A_73,B_74,k10_relat_1(A_73,B_74),D_72)),A_73)
      | ~ r2_hidden(D_72,k10_relat_1(A_73,B_74))
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_127,plain,(
    ! [D_72,B_74] :
      ( ~ r2_hidden(D_72,k10_relat_1(k1_xboole_0,B_74))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_109,c_68])).

tff(c_134,plain,(
    ! [D_72,B_74] : ~ r2_hidden(D_72,k10_relat_1(k1_xboole_0,B_74)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_127])).

tff(c_533,plain,(
    ! [B_116,A_117] :
      ( k10_relat_1(k1_xboole_0,B_116) = k10_relat_1(A_117,k1_xboole_0)
      | ~ v1_relat_1(A_117) ) ),
    inference(resolution,[status(thm)],[c_348,c_134])).

tff(c_535,plain,(
    ! [B_116] : k10_relat_1(k1_xboole_0,k1_xboole_0) = k10_relat_1(k1_xboole_0,B_116) ),
    inference(resolution,[status(thm)],[c_39,c_533])).

tff(c_539,plain,(
    ! [B_116] : k10_relat_1(k1_xboole_0,B_116) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_535])).

tff(c_32,plain,(
    k10_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_556,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_539,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:50:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.45  
% 2.41/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.45  %$ r2_hidden > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.41/1.45  
% 2.41/1.45  %Foreground sorts:
% 2.41/1.45  
% 2.41/1.45  
% 2.41/1.45  %Background operators:
% 2.41/1.45  
% 2.41/1.45  
% 2.41/1.45  %Foreground operators:
% 2.41/1.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.41/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.41/1.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.41/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.41/1.45  tff('#skF_5', type, '#skF_5': $i).
% 2.41/1.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.41/1.45  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.41/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.45  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.41/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.41/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.41/1.45  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.41/1.45  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.41/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.45  
% 2.41/1.46  tff(f_50, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 2.41/1.46  tff(f_49, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.41/1.46  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 2.41/1.46  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.41/1.46  tff(f_34, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.41/1.46  tff(f_53, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 2.41/1.46  tff(c_30, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.41/1.46  tff(c_37, plain, (![A_48]: (v1_relat_1(k6_relat_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.41/1.46  tff(c_39, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_37])).
% 2.41/1.46  tff(c_224, plain, (![A_105, B_106, C_107]: (r2_hidden('#skF_2'(A_105, B_106, C_107), B_106) | r2_hidden('#skF_3'(A_105, B_106, C_107), C_107) | k10_relat_1(A_105, B_106)=C_107 | ~v1_relat_1(A_105))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.41/1.46  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.41/1.46  tff(c_62, plain, (![A_51, B_52]: (~r2_hidden(A_51, k2_zfmisc_1(A_51, B_52)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.41/1.46  tff(c_68, plain, (![A_1]: (~r2_hidden(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_62])).
% 2.41/1.46  tff(c_348, plain, (![A_108, C_109]: (r2_hidden('#skF_3'(A_108, k1_xboole_0, C_109), C_109) | k10_relat_1(A_108, k1_xboole_0)=C_109 | ~v1_relat_1(A_108))), inference(resolution, [status(thm)], [c_224, c_68])).
% 2.41/1.46  tff(c_412, plain, (![A_110]: (k10_relat_1(A_110, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_110))), inference(resolution, [status(thm)], [c_348, c_68])).
% 2.41/1.46  tff(c_419, plain, (k10_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_39, c_412])).
% 2.41/1.46  tff(c_109, plain, (![D_72, A_73, B_74]: (r2_hidden(k4_tarski(D_72, '#skF_4'(A_73, B_74, k10_relat_1(A_73, B_74), D_72)), A_73) | ~r2_hidden(D_72, k10_relat_1(A_73, B_74)) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.41/1.46  tff(c_127, plain, (![D_72, B_74]: (~r2_hidden(D_72, k10_relat_1(k1_xboole_0, B_74)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_109, c_68])).
% 2.41/1.46  tff(c_134, plain, (![D_72, B_74]: (~r2_hidden(D_72, k10_relat_1(k1_xboole_0, B_74)))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_127])).
% 2.41/1.46  tff(c_533, plain, (![B_116, A_117]: (k10_relat_1(k1_xboole_0, B_116)=k10_relat_1(A_117, k1_xboole_0) | ~v1_relat_1(A_117))), inference(resolution, [status(thm)], [c_348, c_134])).
% 2.41/1.46  tff(c_535, plain, (![B_116]: (k10_relat_1(k1_xboole_0, k1_xboole_0)=k10_relat_1(k1_xboole_0, B_116))), inference(resolution, [status(thm)], [c_39, c_533])).
% 2.41/1.46  tff(c_539, plain, (![B_116]: (k10_relat_1(k1_xboole_0, B_116)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_419, c_535])).
% 2.41/1.46  tff(c_32, plain, (k10_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.41/1.46  tff(c_556, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_539, c_32])).
% 2.41/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.46  
% 2.41/1.46  Inference rules
% 2.41/1.46  ----------------------
% 2.41/1.46  #Ref     : 0
% 2.41/1.46  #Sup     : 107
% 2.41/1.46  #Fact    : 0
% 2.41/1.46  #Define  : 0
% 2.41/1.46  #Split   : 0
% 2.41/1.46  #Chain   : 0
% 2.41/1.46  #Close   : 0
% 2.41/1.46  
% 2.41/1.46  Ordering : KBO
% 2.41/1.46  
% 2.41/1.46  Simplification rules
% 2.41/1.46  ----------------------
% 2.41/1.46  #Subsume      : 28
% 2.41/1.46  #Demod        : 51
% 2.41/1.46  #Tautology    : 16
% 2.41/1.46  #SimpNegUnit  : 3
% 2.41/1.46  #BackRed      : 8
% 2.41/1.46  
% 2.41/1.46  #Partial instantiations: 0
% 2.41/1.46  #Strategies tried      : 1
% 2.41/1.46  
% 2.41/1.46  Timing (in seconds)
% 2.41/1.46  ----------------------
% 2.41/1.46  Preprocessing        : 0.32
% 2.41/1.46  Parsing              : 0.17
% 2.41/1.46  CNF conversion       : 0.03
% 2.41/1.46  Main loop            : 0.29
% 2.41/1.46  Inferencing          : 0.11
% 2.41/1.46  Reduction            : 0.07
% 2.41/1.47  Demodulation         : 0.05
% 2.41/1.47  BG Simplification    : 0.02
% 2.41/1.47  Subsumption          : 0.08
% 2.41/1.47  Abstraction          : 0.02
% 2.41/1.47  MUC search           : 0.00
% 2.41/1.47  Cooper               : 0.00
% 2.41/1.47  Total                : 0.64
% 2.41/1.47  Index Insertion      : 0.00
% 2.41/1.47  Index Deletion       : 0.00
% 2.41/1.47  Index Matching       : 0.00
% 2.41/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
