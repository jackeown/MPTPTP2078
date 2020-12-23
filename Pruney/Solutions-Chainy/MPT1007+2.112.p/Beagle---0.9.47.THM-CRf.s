%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:26 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   33 (  37 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   43 (  63 expanded)
%              Number of equality atoms :    9 (  13 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(c_16,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_14,plain,(
    ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_22,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(k1_tarski(B_4),k1_tarski(B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,B_14)
      | ~ r1_tarski(k1_tarski(A_13),B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_34,plain,(
    ! [B_4] : r2_hidden(B_4,k1_tarski(B_4)) ),
    inference(resolution,[status(thm)],[c_8,c_26])).

tff(c_58,plain,(
    ! [D_20,C_21,B_22,A_23] :
      ( r2_hidden(k1_funct_1(D_20,C_21),B_22)
      | k1_xboole_0 = B_22
      | ~ r2_hidden(C_21,A_23)
      | ~ m1_subset_1(D_20,k1_zfmisc_1(k2_zfmisc_1(A_23,B_22)))
      | ~ v1_funct_2(D_20,A_23,B_22)
      | ~ v1_funct_1(D_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_62,plain,(
    ! [D_24,B_25,B_26] :
      ( r2_hidden(k1_funct_1(D_24,B_25),B_26)
      | k1_xboole_0 = B_26
      | ~ m1_subset_1(D_24,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(B_25),B_26)))
      | ~ v1_funct_2(D_24,k1_tarski(B_25),B_26)
      | ~ v1_funct_1(D_24) ) ),
    inference(resolution,[status(thm)],[c_34,c_58])).

tff(c_65,plain,
    ( r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_62])).

tff(c_68,plain,
    ( r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_65])).

tff(c_70,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_14,c_68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:29:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.20  
% 1.79/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.20  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.79/1.20  
% 1.79/1.20  %Foreground sorts:
% 1.79/1.20  
% 1.79/1.20  
% 1.79/1.20  %Background operators:
% 1.79/1.20  
% 1.79/1.20  
% 1.79/1.20  %Foreground operators:
% 1.79/1.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.79/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.79/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.79/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.79/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.79/1.20  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.79/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.79/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.79/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.79/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.79/1.20  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.79/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.79/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.79/1.20  
% 1.79/1.21  tff(f_59, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 1.79/1.21  tff(f_35, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 1.79/1.21  tff(f_29, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 1.79/1.21  tff(f_47, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 1.79/1.21  tff(c_16, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.79/1.21  tff(c_14, plain, (~r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.79/1.21  tff(c_22, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.79/1.21  tff(c_20, plain, (v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.79/1.21  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.79/1.21  tff(c_8, plain, (![B_4]: (r1_tarski(k1_tarski(B_4), k1_tarski(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.79/1.21  tff(c_26, plain, (![A_13, B_14]: (r2_hidden(A_13, B_14) | ~r1_tarski(k1_tarski(A_13), B_14))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.79/1.21  tff(c_34, plain, (![B_4]: (r2_hidden(B_4, k1_tarski(B_4)))), inference(resolution, [status(thm)], [c_8, c_26])).
% 1.79/1.21  tff(c_58, plain, (![D_20, C_21, B_22, A_23]: (r2_hidden(k1_funct_1(D_20, C_21), B_22) | k1_xboole_0=B_22 | ~r2_hidden(C_21, A_23) | ~m1_subset_1(D_20, k1_zfmisc_1(k2_zfmisc_1(A_23, B_22))) | ~v1_funct_2(D_20, A_23, B_22) | ~v1_funct_1(D_20))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.79/1.21  tff(c_62, plain, (![D_24, B_25, B_26]: (r2_hidden(k1_funct_1(D_24, B_25), B_26) | k1_xboole_0=B_26 | ~m1_subset_1(D_24, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(B_25), B_26))) | ~v1_funct_2(D_24, k1_tarski(B_25), B_26) | ~v1_funct_1(D_24))), inference(resolution, [status(thm)], [c_34, c_58])).
% 1.79/1.21  tff(c_65, plain, (r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2') | k1_xboole_0='#skF_2' | ~v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_62])).
% 1.79/1.21  tff(c_68, plain, (r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_65])).
% 1.79/1.21  tff(c_70, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_14, c_68])).
% 1.79/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.21  
% 1.79/1.21  Inference rules
% 1.79/1.21  ----------------------
% 1.79/1.21  #Ref     : 0
% 1.79/1.21  #Sup     : 8
% 1.79/1.21  #Fact    : 0
% 1.79/1.21  #Define  : 0
% 1.79/1.21  #Split   : 0
% 1.79/1.21  #Chain   : 0
% 1.79/1.21  #Close   : 0
% 1.79/1.21  
% 1.79/1.21  Ordering : KBO
% 1.79/1.21  
% 1.79/1.21  Simplification rules
% 1.79/1.21  ----------------------
% 1.79/1.21  #Subsume      : 0
% 1.79/1.21  #Demod        : 2
% 1.79/1.21  #Tautology    : 4
% 1.79/1.21  #SimpNegUnit  : 1
% 1.79/1.21  #BackRed      : 0
% 1.79/1.21  
% 1.79/1.21  #Partial instantiations: 0
% 1.79/1.21  #Strategies tried      : 1
% 1.79/1.21  
% 1.79/1.21  Timing (in seconds)
% 1.79/1.21  ----------------------
% 1.79/1.22  Preprocessing        : 0.31
% 1.79/1.22  Parsing              : 0.16
% 1.79/1.22  CNF conversion       : 0.02
% 1.79/1.22  Main loop            : 0.10
% 1.79/1.22  Inferencing          : 0.04
% 1.79/1.22  Reduction            : 0.03
% 1.79/1.22  Demodulation         : 0.02
% 1.79/1.22  BG Simplification    : 0.01
% 1.79/1.22  Subsumption          : 0.01
% 1.79/1.22  Abstraction          : 0.00
% 1.79/1.22  MUC search           : 0.00
% 1.79/1.22  Cooper               : 0.00
% 1.79/1.22  Total                : 0.43
% 1.79/1.22  Index Insertion      : 0.00
% 1.79/1.22  Index Deletion       : 0.00
% 1.79/1.22  Index Matching       : 0.00
% 1.79/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
