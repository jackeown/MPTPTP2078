%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:22 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   41 (  63 expanded)
%              Number of leaves         :   21 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   50 ( 108 expanded)
%              Number of equality atoms :   15 (  38 expanded)
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

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ! [C] :
                ( m1_subset_1(C,k2_zfmisc_1(A,B))
               => C = k4_tarski(k1_mcart_1(C),k2_mcart_1(C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_mcart_1)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ~ v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_subset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_16,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_12,plain,(
    k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_14,plain,(
    m1_subset_1('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_23,plain,(
    ! [A_18,B_19] :
      ( k4_tarski(k1_mcart_1(A_18),k2_mcart_1(A_18)) = A_18
      | ~ r2_hidden(A_18,B_19)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_27,plain,(
    ! [A_20,B_21] :
      ( k4_tarski(k1_mcart_1(A_20),k2_mcart_1(A_20)) = A_20
      | ~ v1_relat_1(B_21)
      | v1_xboole_0(B_21)
      | ~ m1_subset_1(A_20,B_21) ) ),
    inference(resolution,[status(thm)],[c_6,c_23])).

tff(c_29,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_14,c_27])).

tff(c_32,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_29])).

tff(c_33,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_32])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_2,B_3))
      | v1_xboole_0(B_3)
      | v1_xboole_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_40,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_33,c_4])).

tff(c_42,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_45,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_42,c_2])).

tff(c_49,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_45])).

tff(c_50,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_54,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_50,c_2])).

tff(c_58,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:08:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.19  
% 1.77/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.19  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.77/1.19  
% 1.77/1.19  %Foreground sorts:
% 1.77/1.19  
% 1.77/1.19  
% 1.77/1.19  %Background operators:
% 1.77/1.19  
% 1.77/1.19  
% 1.77/1.19  %Foreground operators:
% 1.77/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.77/1.19  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.77/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.77/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.77/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.77/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.77/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.19  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.77/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.77/1.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.77/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.19  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.77/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.77/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.77/1.19  
% 1.77/1.21  tff(f_66, negated_conjecture, ~(![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (C = k4_tarski(k1_mcart_1(C), k2_mcart_1(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_mcart_1)).
% 1.77/1.21  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.77/1.21  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 1.77/1.21  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 1.77/1.21  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => ~v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_subset_1)).
% 1.77/1.21  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.77/1.21  tff(c_16, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.77/1.21  tff(c_18, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.77/1.21  tff(c_12, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.77/1.21  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.77/1.21  tff(c_14, plain, (m1_subset_1('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.77/1.21  tff(c_6, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.77/1.21  tff(c_23, plain, (![A_18, B_19]: (k4_tarski(k1_mcart_1(A_18), k2_mcart_1(A_18))=A_18 | ~r2_hidden(A_18, B_19) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.77/1.21  tff(c_27, plain, (![A_20, B_21]: (k4_tarski(k1_mcart_1(A_20), k2_mcart_1(A_20))=A_20 | ~v1_relat_1(B_21) | v1_xboole_0(B_21) | ~m1_subset_1(A_20, B_21))), inference(resolution, [status(thm)], [c_6, c_23])).
% 1.77/1.21  tff(c_29, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_14, c_27])).
% 1.77/1.21  tff(c_32, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_29])).
% 1.77/1.21  tff(c_33, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_12, c_32])).
% 1.77/1.21  tff(c_4, plain, (![A_2, B_3]: (~v1_xboole_0(k2_zfmisc_1(A_2, B_3)) | v1_xboole_0(B_3) | v1_xboole_0(A_2))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.77/1.21  tff(c_40, plain, (v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_33, c_4])).
% 1.77/1.21  tff(c_42, plain, (v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_40])).
% 1.77/1.21  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.77/1.21  tff(c_45, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_42, c_2])).
% 1.77/1.21  tff(c_49, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_45])).
% 1.77/1.21  tff(c_50, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 1.77/1.21  tff(c_54, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_50, c_2])).
% 1.77/1.21  tff(c_58, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_54])).
% 1.77/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.21  
% 1.77/1.21  Inference rules
% 1.77/1.21  ----------------------
% 1.77/1.21  #Ref     : 0
% 1.77/1.21  #Sup     : 6
% 1.77/1.21  #Fact    : 0
% 1.77/1.21  #Define  : 0
% 1.77/1.21  #Split   : 1
% 1.77/1.21  #Chain   : 0
% 1.77/1.21  #Close   : 0
% 1.77/1.21  
% 1.77/1.21  Ordering : KBO
% 1.77/1.21  
% 1.77/1.21  Simplification rules
% 1.77/1.21  ----------------------
% 1.77/1.21  #Subsume      : 0
% 1.77/1.21  #Demod        : 1
% 1.77/1.21  #Tautology    : 0
% 1.77/1.21  #SimpNegUnit  : 3
% 1.77/1.21  #BackRed      : 0
% 1.77/1.21  
% 1.77/1.21  #Partial instantiations: 0
% 1.77/1.21  #Strategies tried      : 1
% 1.77/1.21  
% 1.77/1.21  Timing (in seconds)
% 1.77/1.21  ----------------------
% 1.77/1.21  Preprocessing        : 0.27
% 1.77/1.21  Parsing              : 0.14
% 1.77/1.21  CNF conversion       : 0.02
% 1.77/1.21  Main loop            : 0.10
% 1.77/1.21  Inferencing          : 0.04
% 1.77/1.21  Reduction            : 0.04
% 1.77/1.21  Demodulation         : 0.03
% 1.77/1.21  BG Simplification    : 0.01
% 1.77/1.21  Subsumption          : 0.01
% 1.77/1.21  Abstraction          : 0.00
% 1.77/1.21  MUC search           : 0.00
% 1.77/1.21  Cooper               : 0.00
% 1.77/1.21  Total                : 0.39
% 1.77/1.21  Index Insertion      : 0.00
% 1.77/1.21  Index Deletion       : 0.00
% 1.77/1.21  Index Matching       : 0.00
% 1.77/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
