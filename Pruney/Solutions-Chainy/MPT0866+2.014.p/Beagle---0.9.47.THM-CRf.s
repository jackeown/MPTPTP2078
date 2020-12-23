%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:22 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   44 (  69 expanded)
%              Number of leaves         :   22 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   56 ( 120 expanded)
%              Number of equality atoms :   16 (  40 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ! [C] :
                ( m1_subset_1(C,k2_zfmisc_1(A,B))
               => C = k4_tarski(k1_mcart_1(C),k2_mcart_1(C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_mcart_1)).

tff(f_51,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ~ v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_subset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_14,plain,(
    k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_10,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    m1_subset_1('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_34,plain,(
    ! [A_21,B_22] :
      ( k4_tarski(k1_mcart_1(A_21),k2_mcart_1(A_21)) = A_21
      | ~ r2_hidden(A_21,B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_38,plain,(
    ! [A_23,B_24] :
      ( k4_tarski(k1_mcart_1(A_23),k2_mcart_1(A_23)) = A_23
      | ~ v1_relat_1(B_24)
      | v1_xboole_0(B_24)
      | ~ m1_subset_1(A_23,B_24) ) ),
    inference(resolution,[status(thm)],[c_8,c_34])).

tff(c_40,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_16,c_38])).

tff(c_43,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_40])).

tff(c_44,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_43])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_3,B_4))
      | v1_xboole_0(B_4)
      | v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_53,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_6])).

tff(c_56,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_53])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_22,plain,(
    ! [B_14,A_15] :
      ( ~ v1_xboole_0(B_14)
      | B_14 = A_15
      | ~ v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_25,plain,(
    ! [A_15] :
      ( k1_xboole_0 = A_15
      | ~ v1_xboole_0(A_15) ) ),
    inference(resolution,[status(thm)],[c_2,c_22])).

tff(c_59,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_56,c_25])).

tff(c_65,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_59])).

tff(c_66,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_70,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_66,c_25])).

tff(c_76,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_70])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:30:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.11  
% 1.63/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.11  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.63/1.11  
% 1.63/1.11  %Foreground sorts:
% 1.63/1.11  
% 1.63/1.11  
% 1.63/1.11  %Background operators:
% 1.63/1.11  
% 1.63/1.11  
% 1.63/1.11  %Foreground operators:
% 1.63/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.63/1.11  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.63/1.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.63/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.63/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.11  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.63/1.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.63/1.11  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.63/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.11  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.63/1.11  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.63/1.11  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.63/1.11  
% 1.63/1.12  tff(f_71, negated_conjecture, ~(![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (C = k4_tarski(k1_mcart_1(C), k2_mcart_1(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_mcart_1)).
% 1.63/1.12  tff(f_51, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.63/1.12  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 1.63/1.12  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 1.63/1.12  tff(f_43, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => ~v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_subset_1)).
% 1.63/1.12  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.63/1.12  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 1.63/1.12  tff(c_18, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.63/1.12  tff(c_20, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.63/1.12  tff(c_14, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.63/1.12  tff(c_10, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.63/1.12  tff(c_16, plain, (m1_subset_1('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.63/1.12  tff(c_8, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.63/1.12  tff(c_34, plain, (![A_21, B_22]: (k4_tarski(k1_mcart_1(A_21), k2_mcart_1(A_21))=A_21 | ~r2_hidden(A_21, B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.63/1.12  tff(c_38, plain, (![A_23, B_24]: (k4_tarski(k1_mcart_1(A_23), k2_mcart_1(A_23))=A_23 | ~v1_relat_1(B_24) | v1_xboole_0(B_24) | ~m1_subset_1(A_23, B_24))), inference(resolution, [status(thm)], [c_8, c_34])).
% 1.63/1.12  tff(c_40, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_16, c_38])).
% 1.63/1.12  tff(c_43, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_40])).
% 1.63/1.12  tff(c_44, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_14, c_43])).
% 1.63/1.12  tff(c_6, plain, (![A_3, B_4]: (~v1_xboole_0(k2_zfmisc_1(A_3, B_4)) | v1_xboole_0(B_4) | v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.63/1.12  tff(c_53, plain, (v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_44, c_6])).
% 1.63/1.12  tff(c_56, plain, (v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_53])).
% 1.63/1.12  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.63/1.12  tff(c_22, plain, (![B_14, A_15]: (~v1_xboole_0(B_14) | B_14=A_15 | ~v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.63/1.12  tff(c_25, plain, (![A_15]: (k1_xboole_0=A_15 | ~v1_xboole_0(A_15))), inference(resolution, [status(thm)], [c_2, c_22])).
% 1.63/1.12  tff(c_59, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_56, c_25])).
% 1.63/1.12  tff(c_65, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_59])).
% 1.63/1.12  tff(c_66, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_53])).
% 1.63/1.12  tff(c_70, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_66, c_25])).
% 1.63/1.12  tff(c_76, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_70])).
% 1.63/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.12  
% 1.63/1.12  Inference rules
% 1.63/1.12  ----------------------
% 1.63/1.12  #Ref     : 0
% 1.63/1.12  #Sup     : 11
% 1.63/1.12  #Fact    : 0
% 1.63/1.12  #Define  : 0
% 1.63/1.12  #Split   : 1
% 1.63/1.12  #Chain   : 0
% 1.63/1.12  #Close   : 0
% 1.63/1.12  
% 1.63/1.12  Ordering : KBO
% 1.63/1.12  
% 1.63/1.12  Simplification rules
% 1.63/1.12  ----------------------
% 1.63/1.12  #Subsume      : 0
% 1.63/1.12  #Demod        : 1
% 1.63/1.12  #Tautology    : 1
% 1.63/1.12  #SimpNegUnit  : 3
% 1.63/1.12  #BackRed      : 0
% 1.63/1.12  
% 1.63/1.12  #Partial instantiations: 0
% 1.63/1.12  #Strategies tried      : 1
% 1.63/1.12  
% 1.63/1.12  Timing (in seconds)
% 1.63/1.12  ----------------------
% 1.63/1.12  Preprocessing        : 0.26
% 1.63/1.12  Parsing              : 0.14
% 1.63/1.12  CNF conversion       : 0.01
% 1.63/1.12  Main loop            : 0.10
% 1.63/1.12  Inferencing          : 0.04
% 1.63/1.12  Reduction            : 0.03
% 1.63/1.12  Demodulation         : 0.02
% 1.63/1.12  BG Simplification    : 0.01
% 1.63/1.12  Subsumption          : 0.01
% 1.63/1.12  Abstraction          : 0.00
% 1.63/1.12  MUC search           : 0.00
% 1.63/1.12  Cooper               : 0.00
% 1.63/1.12  Total                : 0.39
% 1.63/1.12  Index Insertion      : 0.00
% 1.63/1.12  Index Deletion       : 0.00
% 1.63/1.12  Index Matching       : 0.00
% 1.63/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
