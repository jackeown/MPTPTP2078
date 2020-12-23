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
% DateTime   : Thu Dec  3 10:14:23 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   38 (  42 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   47 (  67 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_20,plain,(
    ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_28,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_26,plain,(
    v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    ! [B_19,C_20,A_21] :
      ( r2_hidden(B_19,C_20)
      | ~ r1_tarski(k2_tarski(A_21,B_19),C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_65,plain,(
    ! [B_22,A_23] : r2_hidden(B_22,k2_tarski(A_23,B_22)) ),
    inference(resolution,[status(thm)],[c_6,c_56])).

tff(c_68,plain,(
    ! [A_3] : r2_hidden(A_3,k1_tarski(A_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_65])).

tff(c_140,plain,(
    ! [D_41,C_42,B_43,A_44] :
      ( r2_hidden(k1_funct_1(D_41,C_42),B_43)
      | k1_xboole_0 = B_43
      | ~ r2_hidden(C_42,A_44)
      | ~ m1_subset_1(D_41,k1_zfmisc_1(k2_zfmisc_1(A_44,B_43)))
      | ~ v1_funct_2(D_41,A_44,B_43)
      | ~ v1_funct_1(D_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_185,plain,(
    ! [D_53,A_54,B_55] :
      ( r2_hidden(k1_funct_1(D_53,A_54),B_55)
      | k1_xboole_0 = B_55
      | ~ m1_subset_1(D_53,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_54),B_55)))
      | ~ v1_funct_2(D_53,k1_tarski(A_54),B_55)
      | ~ v1_funct_1(D_53) ) ),
    inference(resolution,[status(thm)],[c_68,c_140])).

tff(c_188,plain,
    ( r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_185])).

tff(c_191,plain,
    ( r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_188])).

tff(c_193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_20,c_191])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.20  
% 1.93/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.20  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.93/1.20  
% 1.93/1.20  %Foreground sorts:
% 1.93/1.20  
% 1.93/1.20  
% 1.93/1.20  %Background operators:
% 1.93/1.20  
% 1.93/1.20  
% 1.93/1.20  %Foreground operators:
% 1.93/1.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.93/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.93/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.93/1.20  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.93/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.93/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.93/1.20  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.93/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.93/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.93/1.20  
% 2.02/1.21  tff(f_65, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 2.02/1.21  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.02/1.21  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.02/1.21  tff(f_41, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.02/1.21  tff(f_53, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.02/1.21  tff(c_22, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.02/1.21  tff(c_20, plain, (~r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.02/1.21  tff(c_28, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.02/1.21  tff(c_26, plain, (v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.02/1.21  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.02/1.21  tff(c_8, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.02/1.21  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.02/1.21  tff(c_56, plain, (![B_19, C_20, A_21]: (r2_hidden(B_19, C_20) | ~r1_tarski(k2_tarski(A_21, B_19), C_20))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.02/1.21  tff(c_65, plain, (![B_22, A_23]: (r2_hidden(B_22, k2_tarski(A_23, B_22)))), inference(resolution, [status(thm)], [c_6, c_56])).
% 2.02/1.21  tff(c_68, plain, (![A_3]: (r2_hidden(A_3, k1_tarski(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_65])).
% 2.02/1.21  tff(c_140, plain, (![D_41, C_42, B_43, A_44]: (r2_hidden(k1_funct_1(D_41, C_42), B_43) | k1_xboole_0=B_43 | ~r2_hidden(C_42, A_44) | ~m1_subset_1(D_41, k1_zfmisc_1(k2_zfmisc_1(A_44, B_43))) | ~v1_funct_2(D_41, A_44, B_43) | ~v1_funct_1(D_41))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.02/1.21  tff(c_185, plain, (![D_53, A_54, B_55]: (r2_hidden(k1_funct_1(D_53, A_54), B_55) | k1_xboole_0=B_55 | ~m1_subset_1(D_53, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_54), B_55))) | ~v1_funct_2(D_53, k1_tarski(A_54), B_55) | ~v1_funct_1(D_53))), inference(resolution, [status(thm)], [c_68, c_140])).
% 2.02/1.21  tff(c_188, plain, (r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2') | k1_xboole_0='#skF_2' | ~v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_185])).
% 2.02/1.21  tff(c_191, plain, (r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_188])).
% 2.02/1.21  tff(c_193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_20, c_191])).
% 2.02/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.21  
% 2.02/1.21  Inference rules
% 2.02/1.21  ----------------------
% 2.02/1.21  #Ref     : 0
% 2.02/1.21  #Sup     : 32
% 2.02/1.21  #Fact    : 0
% 2.02/1.21  #Define  : 0
% 2.02/1.21  #Split   : 0
% 2.02/1.21  #Chain   : 0
% 2.02/1.21  #Close   : 0
% 2.02/1.21  
% 2.02/1.21  Ordering : KBO
% 2.02/1.21  
% 2.02/1.21  Simplification rules
% 2.02/1.21  ----------------------
% 2.02/1.21  #Subsume      : 3
% 2.02/1.21  #Demod        : 13
% 2.02/1.21  #Tautology    : 15
% 2.02/1.21  #SimpNegUnit  : 1
% 2.02/1.21  #BackRed      : 0
% 2.02/1.21  
% 2.02/1.21  #Partial instantiations: 0
% 2.02/1.21  #Strategies tried      : 1
% 2.02/1.21  
% 2.02/1.21  Timing (in seconds)
% 2.02/1.21  ----------------------
% 2.02/1.21  Preprocessing        : 0.30
% 2.02/1.21  Parsing              : 0.16
% 2.02/1.21  CNF conversion       : 0.02
% 2.02/1.21  Main loop            : 0.16
% 2.02/1.21  Inferencing          : 0.06
% 2.02/1.21  Reduction            : 0.05
% 2.02/1.21  Demodulation         : 0.04
% 2.02/1.21  BG Simplification    : 0.01
% 2.02/1.21  Subsumption          : 0.03
% 2.02/1.22  Abstraction          : 0.01
% 2.02/1.22  MUC search           : 0.00
% 2.02/1.22  Cooper               : 0.00
% 2.02/1.22  Total                : 0.48
% 2.02/1.22  Index Insertion      : 0.00
% 2.02/1.22  Index Deletion       : 0.00
% 2.02/1.22  Index Matching       : 0.00
% 2.02/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
