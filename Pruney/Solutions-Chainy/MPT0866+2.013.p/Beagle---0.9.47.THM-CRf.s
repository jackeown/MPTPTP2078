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
% DateTime   : Thu Dec  3 10:09:21 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   43 (  48 expanded)
%              Number of leaves         :   24 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   57 (  74 expanded)
%              Number of equality atoms :   25 (  38 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ! [C] :
                ( m1_subset_1(C,k2_zfmisc_1(A,B))
               => C = k4_tarski(k1_mcart_1(C),k2_mcart_1(C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_mcart_1)).

tff(f_41,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_16,plain,(
    k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8,plain,(
    ! [A_5,B_6] : v1_relat_1(k2_zfmisc_1(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( r2_hidden(A_2,B_3)
      | v1_xboole_0(B_3)
      | ~ m1_subset_1(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_160,plain,(
    ! [A_38,B_39] :
      ( k4_tarski(k1_mcart_1(A_38),k2_mcart_1(A_38)) = A_38
      | ~ r2_hidden(A_38,B_39)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_165,plain,(
    ! [A_42,B_43] :
      ( k4_tarski(k1_mcart_1(A_42),k2_mcart_1(A_42)) = A_42
      | ~ v1_relat_1(B_43)
      | v1_xboole_0(B_43)
      | ~ m1_subset_1(A_42,B_43) ) ),
    inference(resolution,[status(thm)],[c_4,c_160])).

tff(c_167,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_18,c_165])).

tff(c_170,plain,
    ( k4_tarski(k1_mcart_1('#skF_3'),k2_mcart_1('#skF_3')) = '#skF_3'
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_167])).

tff(c_171,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_170])).

tff(c_132,plain,(
    ! [A_32,B_33] :
      ( k1_relat_1(k2_zfmisc_1(A_32,B_33)) = A_32
      | k1_xboole_0 = B_33
      | k1_xboole_0 = A_32 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [A_4] :
      ( v1_xboole_0(k1_relat_1(A_4))
      | ~ v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_141,plain,(
    ! [A_32,B_33] :
      ( v1_xboole_0(A_32)
      | ~ v1_xboole_0(k2_zfmisc_1(A_32,B_33))
      | k1_xboole_0 = B_33
      | k1_xboole_0 = A_32 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_6])).

tff(c_177,plain,
    ( v1_xboole_0('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_171,c_141])).

tff(c_189,plain,(
    v1_xboole_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_20,c_177])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_197,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_189,c_2])).

tff(c_202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_197])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:37:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.22  
% 1.94/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.23  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.94/1.23  
% 1.94/1.23  %Foreground sorts:
% 1.94/1.23  
% 1.94/1.23  
% 1.94/1.23  %Background operators:
% 1.94/1.23  
% 1.94/1.23  
% 1.94/1.23  %Foreground operators:
% 1.94/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.94/1.23  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.94/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.94/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.94/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.23  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.94/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.94/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.94/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.23  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.94/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.94/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.94/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.94/1.23  
% 1.99/1.25  tff(f_73, negated_conjecture, ~(![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (C = k4_tarski(k1_mcart_1(C), k2_mcart_1(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_mcart_1)).
% 1.99/1.25  tff(f_41, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.99/1.25  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 1.99/1.25  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 1.99/1.25  tff(f_53, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 1.99/1.25  tff(f_39, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 1.99/1.25  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.99/1.25  tff(c_22, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.99/1.25  tff(c_20, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.99/1.25  tff(c_16, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.99/1.25  tff(c_8, plain, (![A_5, B_6]: (v1_relat_1(k2_zfmisc_1(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.99/1.25  tff(c_18, plain, (m1_subset_1('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 1.99/1.25  tff(c_4, plain, (![A_2, B_3]: (r2_hidden(A_2, B_3) | v1_xboole_0(B_3) | ~m1_subset_1(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.99/1.25  tff(c_160, plain, (![A_38, B_39]: (k4_tarski(k1_mcart_1(A_38), k2_mcart_1(A_38))=A_38 | ~r2_hidden(A_38, B_39) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.99/1.25  tff(c_165, plain, (![A_42, B_43]: (k4_tarski(k1_mcart_1(A_42), k2_mcart_1(A_42))=A_42 | ~v1_relat_1(B_43) | v1_xboole_0(B_43) | ~m1_subset_1(A_42, B_43))), inference(resolution, [status(thm)], [c_4, c_160])).
% 1.99/1.25  tff(c_167, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_165])).
% 1.99/1.25  tff(c_170, plain, (k4_tarski(k1_mcart_1('#skF_3'), k2_mcart_1('#skF_3'))='#skF_3' | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_167])).
% 1.99/1.25  tff(c_171, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_16, c_170])).
% 1.99/1.25  tff(c_132, plain, (![A_32, B_33]: (k1_relat_1(k2_zfmisc_1(A_32, B_33))=A_32 | k1_xboole_0=B_33 | k1_xboole_0=A_32)), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.99/1.25  tff(c_6, plain, (![A_4]: (v1_xboole_0(k1_relat_1(A_4)) | ~v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.99/1.25  tff(c_141, plain, (![A_32, B_33]: (v1_xboole_0(A_32) | ~v1_xboole_0(k2_zfmisc_1(A_32, B_33)) | k1_xboole_0=B_33 | k1_xboole_0=A_32)), inference(superposition, [status(thm), theory('equality')], [c_132, c_6])).
% 1.99/1.25  tff(c_177, plain, (v1_xboole_0('#skF_1') | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_171, c_141])).
% 1.99/1.25  tff(c_189, plain, (v1_xboole_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_22, c_20, c_177])).
% 1.99/1.25  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.99/1.25  tff(c_197, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_189, c_2])).
% 1.99/1.25  tff(c_202, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_197])).
% 1.99/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.25  
% 1.99/1.25  Inference rules
% 1.99/1.25  ----------------------
% 1.99/1.25  #Ref     : 0
% 1.99/1.25  #Sup     : 35
% 1.99/1.25  #Fact    : 0
% 1.99/1.25  #Define  : 0
% 1.99/1.25  #Split   : 1
% 1.99/1.25  #Chain   : 0
% 1.99/1.25  #Close   : 0
% 1.99/1.25  
% 1.99/1.25  Ordering : KBO
% 1.99/1.25  
% 1.99/1.25  Simplification rules
% 1.99/1.25  ----------------------
% 1.99/1.25  #Subsume      : 8
% 1.99/1.25  #Demod        : 8
% 1.99/1.25  #Tautology    : 17
% 1.99/1.25  #SimpNegUnit  : 7
% 1.99/1.25  #BackRed      : 1
% 1.99/1.25  
% 1.99/1.25  #Partial instantiations: 0
% 1.99/1.25  #Strategies tried      : 1
% 1.99/1.25  
% 1.99/1.25  Timing (in seconds)
% 1.99/1.25  ----------------------
% 1.99/1.25  Preprocessing        : 0.27
% 1.99/1.25  Parsing              : 0.15
% 1.99/1.25  CNF conversion       : 0.02
% 1.99/1.25  Main loop            : 0.18
% 1.99/1.25  Inferencing          : 0.07
% 1.99/1.25  Reduction            : 0.05
% 1.99/1.25  Demodulation         : 0.03
% 1.99/1.25  BG Simplification    : 0.01
% 1.99/1.26  Subsumption          : 0.03
% 1.99/1.26  Abstraction          : 0.01
% 1.99/1.26  MUC search           : 0.00
% 1.99/1.26  Cooper               : 0.00
% 1.99/1.26  Total                : 0.50
% 1.99/1.26  Index Insertion      : 0.00
% 1.99/1.26  Index Deletion       : 0.00
% 1.99/1.26  Index Matching       : 0.00
% 1.99/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
