%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:30 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   46 (  52 expanded)
%              Number of leaves         :   28 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   53 (  79 expanded)
%              Number of equality atoms :   22 (  28 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_38,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_32,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_51,plain,(
    ! [A_24,B_25] : k2_xboole_0(k1_tarski(A_24),B_25) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_55,plain,(
    ! [A_24] : k1_tarski(A_24) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_51])).

tff(c_40,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_38,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_34,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1918,plain,(
    ! [D_2805,C_2806,B_2807,A_2808] :
      ( r2_hidden(k1_funct_1(D_2805,C_2806),B_2807)
      | k1_xboole_0 = B_2807
      | ~ r2_hidden(C_2806,A_2808)
      | ~ m1_subset_1(D_2805,k1_zfmisc_1(k2_zfmisc_1(A_2808,B_2807)))
      | ~ v1_funct_2(D_2805,A_2808,B_2807)
      | ~ v1_funct_1(D_2805) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2194,plain,(
    ! [D_3161,B_3162] :
      ( r2_hidden(k1_funct_1(D_3161,'#skF_5'),B_3162)
      | k1_xboole_0 = B_3162
      | ~ m1_subset_1(D_3161,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_3162)))
      | ~ v1_funct_2(D_3161,'#skF_3',B_3162)
      | ~ v1_funct_1(D_3161) ) ),
    inference(resolution,[status(thm)],[c_34,c_1918])).

tff(c_2203,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_2194])).

tff(c_2206,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_2203])).

tff(c_2207,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_2206])).

tff(c_22,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_84,plain,(
    ! [D_33,B_34,A_35] :
      ( D_33 = B_34
      | D_33 = A_35
      | ~ r2_hidden(D_33,k2_tarski(A_35,B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_90,plain,(
    ! [D_33,A_9] :
      ( D_33 = A_9
      | D_33 = A_9
      | ~ r2_hidden(D_33,k1_tarski(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_84])).

tff(c_2214,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2207,c_90])).

tff(c_2260,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_32,c_2214])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:02:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.40/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.55  
% 3.40/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.56  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 3.40/1.56  
% 3.40/1.56  %Foreground sorts:
% 3.40/1.56  
% 3.40/1.56  
% 3.40/1.56  %Background operators:
% 3.40/1.56  
% 3.40/1.56  
% 3.40/1.56  %Foreground operators:
% 3.40/1.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.40/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.40/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.40/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.40/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.40/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.40/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.40/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.40/1.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.40/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.40/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.40/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.40/1.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.40/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.40/1.56  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.40/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.40/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.40/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/1.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.40/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.40/1.56  
% 3.40/1.56  tff(f_68, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 3.40/1.56  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.40/1.56  tff(f_45, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.40/1.56  tff(f_57, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 3.40/1.56  tff(f_38, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.40/1.56  tff(f_36, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 3.40/1.56  tff(c_32, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.40/1.56  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.40/1.56  tff(c_51, plain, (![A_24, B_25]: (k2_xboole_0(k1_tarski(A_24), B_25)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.40/1.56  tff(c_55, plain, (![A_24]: (k1_tarski(A_24)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_51])).
% 3.40/1.56  tff(c_40, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.40/1.56  tff(c_38, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.40/1.56  tff(c_36, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.40/1.56  tff(c_34, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.40/1.56  tff(c_1918, plain, (![D_2805, C_2806, B_2807, A_2808]: (r2_hidden(k1_funct_1(D_2805, C_2806), B_2807) | k1_xboole_0=B_2807 | ~r2_hidden(C_2806, A_2808) | ~m1_subset_1(D_2805, k1_zfmisc_1(k2_zfmisc_1(A_2808, B_2807))) | ~v1_funct_2(D_2805, A_2808, B_2807) | ~v1_funct_1(D_2805))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.40/1.56  tff(c_2194, plain, (![D_3161, B_3162]: (r2_hidden(k1_funct_1(D_3161, '#skF_5'), B_3162) | k1_xboole_0=B_3162 | ~m1_subset_1(D_3161, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_3162))) | ~v1_funct_2(D_3161, '#skF_3', B_3162) | ~v1_funct_1(D_3161))), inference(resolution, [status(thm)], [c_34, c_1918])).
% 3.40/1.56  tff(c_2203, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_36, c_2194])).
% 3.40/1.56  tff(c_2206, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_2203])).
% 3.40/1.56  tff(c_2207, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_55, c_2206])).
% 3.40/1.56  tff(c_22, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.40/1.56  tff(c_84, plain, (![D_33, B_34, A_35]: (D_33=B_34 | D_33=A_35 | ~r2_hidden(D_33, k2_tarski(A_35, B_34)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.40/1.56  tff(c_90, plain, (![D_33, A_9]: (D_33=A_9 | D_33=A_9 | ~r2_hidden(D_33, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_84])).
% 3.40/1.56  tff(c_2214, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_2207, c_90])).
% 3.40/1.56  tff(c_2260, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_32, c_2214])).
% 3.40/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.56  
% 3.40/1.56  Inference rules
% 3.40/1.56  ----------------------
% 3.40/1.56  #Ref     : 0
% 3.40/1.56  #Sup     : 293
% 3.40/1.56  #Fact    : 8
% 3.40/1.56  #Define  : 0
% 3.40/1.56  #Split   : 5
% 3.40/1.56  #Chain   : 0
% 3.40/1.56  #Close   : 0
% 3.40/1.56  
% 3.40/1.56  Ordering : KBO
% 3.40/1.56  
% 3.40/1.56  Simplification rules
% 3.40/1.56  ----------------------
% 3.40/1.56  #Subsume      : 56
% 3.40/1.56  #Demod        : 42
% 3.40/1.56  #Tautology    : 98
% 3.40/1.56  #SimpNegUnit  : 16
% 3.40/1.56  #BackRed      : 0
% 3.40/1.56  
% 3.40/1.56  #Partial instantiations: 2070
% 3.40/1.56  #Strategies tried      : 1
% 3.40/1.56  
% 3.40/1.56  Timing (in seconds)
% 3.40/1.56  ----------------------
% 3.40/1.57  Preprocessing        : 0.30
% 3.40/1.57  Parsing              : 0.16
% 3.40/1.57  CNF conversion       : 0.02
% 3.40/1.57  Main loop            : 0.51
% 3.40/1.57  Inferencing          : 0.28
% 3.40/1.57  Reduction            : 0.11
% 3.40/1.57  Demodulation         : 0.08
% 3.40/1.57  BG Simplification    : 0.03
% 3.40/1.57  Subsumption          : 0.07
% 3.40/1.57  Abstraction          : 0.03
% 3.40/1.57  MUC search           : 0.00
% 3.40/1.57  Cooper               : 0.00
% 3.40/1.57  Total                : 0.84
% 3.40/1.57  Index Insertion      : 0.00
% 3.40/1.57  Index Deletion       : 0.00
% 3.40/1.57  Index Matching       : 0.00
% 3.40/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
