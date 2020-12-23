%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:06 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   41 (  46 expanded)
%              Number of leaves         :   26 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 (  55 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_40,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_56,plain,(
    ! [B_43,A_44] :
      ( ~ v1_xboole_0(B_43)
      | ~ r2_hidden(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_56])).

tff(c_98,plain,(
    ! [B_58,A_59] :
      ( m1_subset_1(B_58,A_59)
      | ~ r2_hidden(B_58,A_59)
      | v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_107,plain,
    ( m1_subset_1('#skF_2','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_98])).

tff(c_112,plain,(
    m1_subset_1('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_107])).

tff(c_188,plain,(
    ! [B_73,A_74] :
      ( m1_subset_1(k1_tarski(B_73),k1_zfmisc_1(A_74))
      | k1_xboole_0 = A_74
      | ~ m1_subset_1(B_73,A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_38,plain,(
    ~ m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_194,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_188,c_38])).

tff(c_198,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_194])).

tff(c_8,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_141,plain,(
    ! [A_67,B_68,C_69] :
      ( ~ r1_xboole_0(A_67,B_68)
      | ~ r2_hidden(C_69,B_68)
      | ~ r2_hidden(C_69,A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_150,plain,(
    ! [C_69] : ~ r2_hidden(C_69,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_141])).

tff(c_202,plain,(
    ! [C_69] : ~ r2_hidden(C_69,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_150])).

tff(c_210,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_202,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:11:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.25  
% 2.11/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.25  %$ r2_hidden > r1_xboole_0 > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.11/1.25  
% 2.11/1.25  %Foreground sorts:
% 2.11/1.25  
% 2.11/1.25  
% 2.11/1.25  %Background operators:
% 2.11/1.25  
% 2.11/1.25  
% 2.11/1.25  %Foreground operators:
% 2.11/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.11/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.11/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.11/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.11/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.11/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.11/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.11/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.25  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.11/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.11/1.25  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.11/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.25  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.11/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.11/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.11/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.11/1.25  
% 2.11/1.26  tff(f_99, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 2.11/1.26  tff(f_60, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 2.11/1.26  tff(f_87, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.11/1.26  tff(f_94, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 2.11/1.26  tff(f_55, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.11/1.26  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.11/1.26  tff(c_40, plain, (r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.11/1.26  tff(c_56, plain, (![B_43, A_44]: (~v1_xboole_0(B_43) | ~r2_hidden(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.11/1.26  tff(c_60, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_56])).
% 2.11/1.26  tff(c_98, plain, (![B_58, A_59]: (m1_subset_1(B_58, A_59) | ~r2_hidden(B_58, A_59) | v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.11/1.26  tff(c_107, plain, (m1_subset_1('#skF_2', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_98])).
% 2.11/1.26  tff(c_112, plain, (m1_subset_1('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_107])).
% 2.11/1.26  tff(c_188, plain, (![B_73, A_74]: (m1_subset_1(k1_tarski(B_73), k1_zfmisc_1(A_74)) | k1_xboole_0=A_74 | ~m1_subset_1(B_73, A_74))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.11/1.26  tff(c_38, plain, (~m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.11/1.26  tff(c_194, plain, (k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_188, c_38])).
% 2.11/1.26  tff(c_198, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_194])).
% 2.11/1.26  tff(c_8, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.11/1.26  tff(c_141, plain, (![A_67, B_68, C_69]: (~r1_xboole_0(A_67, B_68) | ~r2_hidden(C_69, B_68) | ~r2_hidden(C_69, A_67))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.11/1.26  tff(c_150, plain, (![C_69]: (~r2_hidden(C_69, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_141])).
% 2.11/1.26  tff(c_202, plain, (![C_69]: (~r2_hidden(C_69, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_198, c_150])).
% 2.11/1.26  tff(c_210, plain, $false, inference(negUnitSimplification, [status(thm)], [c_202, c_40])).
% 2.11/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.26  
% 2.11/1.26  Inference rules
% 2.11/1.26  ----------------------
% 2.11/1.26  #Ref     : 0
% 2.11/1.26  #Sup     : 34
% 2.11/1.26  #Fact    : 0
% 2.11/1.26  #Define  : 0
% 2.11/1.26  #Split   : 1
% 2.11/1.26  #Chain   : 0
% 2.11/1.26  #Close   : 0
% 2.11/1.26  
% 2.11/1.26  Ordering : KBO
% 2.11/1.26  
% 2.11/1.26  Simplification rules
% 2.11/1.26  ----------------------
% 2.11/1.26  #Subsume      : 6
% 2.11/1.26  #Demod        : 8
% 2.11/1.26  #Tautology    : 15
% 2.11/1.26  #SimpNegUnit  : 2
% 2.11/1.26  #BackRed      : 7
% 2.11/1.26  
% 2.11/1.26  #Partial instantiations: 0
% 2.11/1.26  #Strategies tried      : 1
% 2.11/1.26  
% 2.11/1.26  Timing (in seconds)
% 2.11/1.26  ----------------------
% 2.11/1.27  Preprocessing        : 0.33
% 2.11/1.27  Parsing              : 0.17
% 2.11/1.27  CNF conversion       : 0.02
% 2.11/1.27  Main loop            : 0.17
% 2.11/1.27  Inferencing          : 0.06
% 2.11/1.27  Reduction            : 0.05
% 2.11/1.27  Demodulation         : 0.03
% 2.11/1.27  BG Simplification    : 0.02
% 2.11/1.27  Subsumption          : 0.03
% 2.11/1.27  Abstraction          : 0.01
% 2.11/1.27  MUC search           : 0.00
% 2.11/1.27  Cooper               : 0.00
% 2.11/1.27  Total                : 0.53
% 2.11/1.27  Index Insertion      : 0.00
% 2.11/1.27  Index Deletion       : 0.00
% 2.11/1.27  Index Matching       : 0.00
% 2.11/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
