%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:24 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   31 (  35 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   38 (  58 expanded)
%              Number of equality atoms :    9 (  13 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_24,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_22,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_20,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_70,plain,(
    ! [D_25,C_26,B_27,A_28] :
      ( r2_hidden(k1_funct_1(D_25,C_26),B_27)
      | k1_xboole_0 = B_27
      | ~ r2_hidden(C_26,A_28)
      | ~ m1_subset_1(D_25,k1_zfmisc_1(k2_zfmisc_1(A_28,B_27)))
      | ~ v1_funct_2(D_25,A_28,B_27)
      | ~ v1_funct_1(D_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_80,plain,(
    ! [D_29,C_30,B_31] :
      ( r2_hidden(k1_funct_1(D_29,C_30),B_31)
      | k1_xboole_0 = B_31
      | ~ m1_subset_1(D_29,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_30),B_31)))
      | ~ v1_funct_2(D_29,k1_tarski(C_30),B_31)
      | ~ v1_funct_1(D_29) ) ),
    inference(resolution,[status(thm)],[c_4,c_70])).

tff(c_83,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_80])).

tff(c_86,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_83])).

tff(c_88,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_16,c_86])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:27:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.13  
% 1.61/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.13  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.61/1.13  
% 1.61/1.13  %Foreground sorts:
% 1.61/1.13  
% 1.61/1.13  
% 1.61/1.13  %Background operators:
% 1.61/1.13  
% 1.61/1.13  
% 1.61/1.13  %Foreground operators:
% 1.61/1.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.61/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.61/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.61/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.61/1.13  tff('#skF_5', type, '#skF_5': $i).
% 1.61/1.13  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.61/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.61/1.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.61/1.13  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.61/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.61/1.13  tff('#skF_4', type, '#skF_4': $i).
% 1.61/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.13  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.61/1.13  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.61/1.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.61/1.13  
% 1.61/1.14  tff(f_56, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 1.61/1.14  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.61/1.14  tff(f_44, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 1.61/1.14  tff(c_18, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.61/1.14  tff(c_16, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.61/1.14  tff(c_24, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.61/1.14  tff(c_22, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.61/1.14  tff(c_20, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.61/1.14  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.61/1.14  tff(c_70, plain, (![D_25, C_26, B_27, A_28]: (r2_hidden(k1_funct_1(D_25, C_26), B_27) | k1_xboole_0=B_27 | ~r2_hidden(C_26, A_28) | ~m1_subset_1(D_25, k1_zfmisc_1(k2_zfmisc_1(A_28, B_27))) | ~v1_funct_2(D_25, A_28, B_27) | ~v1_funct_1(D_25))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.61/1.14  tff(c_80, plain, (![D_29, C_30, B_31]: (r2_hidden(k1_funct_1(D_29, C_30), B_31) | k1_xboole_0=B_31 | ~m1_subset_1(D_29, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_30), B_31))) | ~v1_funct_2(D_29, k1_tarski(C_30), B_31) | ~v1_funct_1(D_29))), inference(resolution, [status(thm)], [c_4, c_70])).
% 1.61/1.14  tff(c_83, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_20, c_80])).
% 1.61/1.14  tff(c_86, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_83])).
% 1.61/1.14  tff(c_88, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_16, c_86])).
% 1.61/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.14  
% 1.61/1.14  Inference rules
% 1.61/1.14  ----------------------
% 1.61/1.14  #Ref     : 0
% 1.61/1.14  #Sup     : 12
% 1.61/1.14  #Fact    : 0
% 1.61/1.14  #Define  : 0
% 1.61/1.14  #Split   : 0
% 1.61/1.14  #Chain   : 0
% 1.61/1.14  #Close   : 0
% 1.61/1.14  
% 1.61/1.14  Ordering : KBO
% 1.61/1.14  
% 1.61/1.14  Simplification rules
% 1.61/1.14  ----------------------
% 1.61/1.14  #Subsume      : 0
% 1.61/1.14  #Demod        : 4
% 1.61/1.14  #Tautology    : 6
% 1.61/1.14  #SimpNegUnit  : 1
% 1.61/1.14  #BackRed      : 0
% 1.61/1.14  
% 1.61/1.14  #Partial instantiations: 0
% 1.61/1.14  #Strategies tried      : 1
% 1.61/1.14  
% 1.61/1.14  Timing (in seconds)
% 1.61/1.14  ----------------------
% 1.61/1.15  Preprocessing        : 0.28
% 1.61/1.15  Parsing              : 0.14
% 1.61/1.15  CNF conversion       : 0.02
% 1.61/1.15  Main loop            : 0.13
% 1.61/1.15  Inferencing          : 0.05
% 1.61/1.15  Reduction            : 0.03
% 1.61/1.15  Demodulation         : 0.02
% 1.61/1.15  BG Simplification    : 0.01
% 1.61/1.15  Subsumption          : 0.03
% 1.61/1.15  Abstraction          : 0.01
% 1.61/1.15  MUC search           : 0.00
% 1.61/1.15  Cooper               : 0.00
% 1.61/1.15  Total                : 0.43
% 1.61/1.15  Index Insertion      : 0.00
% 1.61/1.15  Index Deletion       : 0.00
% 1.61/1.15  Index Matching       : 0.00
% 1.61/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
