%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:28 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   47 (  51 expanded)
%              Number of leaves         :   29 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   49 (  69 expanded)
%              Number of equality atoms :   19 (  23 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_28,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_16,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_63,plain,(
    ! [A_32,B_33] : k2_xboole_0(k1_tarski(A_32),k1_tarski(B_33)) = k2_tarski(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_24,plain,(
    ! [A_18,B_19] : k2_xboole_0(k1_tarski(A_18),B_19) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_74,plain,(
    ! [A_34,B_35] : k2_tarski(A_34,B_35) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_24])).

tff(c_76,plain,(
    ! [A_8] : k1_tarski(A_8) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_74])).

tff(c_36,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_34,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_32,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_30,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_110,plain,(
    ! [D_52,C_53,B_54,A_55] :
      ( r2_hidden(k1_funct_1(D_52,C_53),B_54)
      | k1_xboole_0 = B_54
      | ~ r2_hidden(C_53,A_55)
      | ~ m1_subset_1(D_52,k1_zfmisc_1(k2_zfmisc_1(A_55,B_54)))
      | ~ v1_funct_2(D_52,A_55,B_54)
      | ~ v1_funct_1(D_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_147,plain,(
    ! [D_60,B_61] :
      ( r2_hidden(k1_funct_1(D_60,'#skF_5'),B_61)
      | k1_xboole_0 = B_61
      | ~ m1_subset_1(D_60,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_61)))
      | ~ v1_funct_2(D_60,'#skF_3',B_61)
      | ~ v1_funct_1(D_60) ) ),
    inference(resolution,[status(thm)],[c_30,c_110])).

tff(c_150,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_32,c_147])).

tff(c_153,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_150])).

tff(c_154,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_153])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_159,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_154,c_2])).

tff(c_164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_159])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:15:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.28  
% 1.96/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.28  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.96/1.28  
% 1.96/1.28  %Foreground sorts:
% 1.96/1.28  
% 1.96/1.28  
% 1.96/1.28  %Background operators:
% 1.96/1.28  
% 1.96/1.28  
% 1.96/1.28  %Foreground operators:
% 1.96/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.96/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.96/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.96/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.96/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.96/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.96/1.28  tff('#skF_5', type, '#skF_5': $i).
% 1.96/1.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.96/1.28  tff('#skF_6', type, '#skF_6': $i).
% 1.96/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.96/1.28  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.96/1.28  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.96/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.96/1.28  tff('#skF_4', type, '#skF_4': $i).
% 1.96/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.96/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.96/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.96/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.96/1.28  
% 1.96/1.29  tff(f_68, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 1.96/1.29  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.96/1.29  tff(f_34, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.96/1.29  tff(f_45, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.96/1.29  tff(f_57, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 1.96/1.29  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.96/1.29  tff(c_28, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.96/1.29  tff(c_16, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.96/1.29  tff(c_63, plain, (![A_32, B_33]: (k2_xboole_0(k1_tarski(A_32), k1_tarski(B_33))=k2_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.96/1.29  tff(c_24, plain, (![A_18, B_19]: (k2_xboole_0(k1_tarski(A_18), B_19)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.96/1.29  tff(c_74, plain, (![A_34, B_35]: (k2_tarski(A_34, B_35)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_63, c_24])).
% 1.96/1.29  tff(c_76, plain, (![A_8]: (k1_tarski(A_8)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_74])).
% 1.96/1.29  tff(c_36, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.96/1.29  tff(c_34, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.96/1.29  tff(c_32, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.96/1.29  tff(c_30, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.96/1.29  tff(c_110, plain, (![D_52, C_53, B_54, A_55]: (r2_hidden(k1_funct_1(D_52, C_53), B_54) | k1_xboole_0=B_54 | ~r2_hidden(C_53, A_55) | ~m1_subset_1(D_52, k1_zfmisc_1(k2_zfmisc_1(A_55, B_54))) | ~v1_funct_2(D_52, A_55, B_54) | ~v1_funct_1(D_52))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.96/1.29  tff(c_147, plain, (![D_60, B_61]: (r2_hidden(k1_funct_1(D_60, '#skF_5'), B_61) | k1_xboole_0=B_61 | ~m1_subset_1(D_60, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_61))) | ~v1_funct_2(D_60, '#skF_3', B_61) | ~v1_funct_1(D_60))), inference(resolution, [status(thm)], [c_30, c_110])).
% 1.96/1.29  tff(c_150, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_32, c_147])).
% 1.96/1.29  tff(c_153, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_150])).
% 1.96/1.29  tff(c_154, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_76, c_153])).
% 1.96/1.29  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.96/1.29  tff(c_159, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_154, c_2])).
% 1.96/1.29  tff(c_164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_159])).
% 1.96/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.29  
% 1.96/1.29  Inference rules
% 1.96/1.29  ----------------------
% 1.96/1.29  #Ref     : 0
% 1.96/1.29  #Sup     : 27
% 1.96/1.29  #Fact    : 0
% 1.96/1.29  #Define  : 0
% 1.96/1.29  #Split   : 0
% 1.96/1.29  #Chain   : 0
% 1.96/1.29  #Close   : 0
% 1.96/1.29  
% 1.96/1.29  Ordering : KBO
% 1.96/1.29  
% 1.96/1.29  Simplification rules
% 1.96/1.29  ----------------------
% 1.96/1.29  #Subsume      : 0
% 1.96/1.29  #Demod        : 4
% 1.96/1.29  #Tautology    : 16
% 1.96/1.29  #SimpNegUnit  : 2
% 1.96/1.29  #BackRed      : 0
% 1.96/1.29  
% 1.96/1.29  #Partial instantiations: 0
% 1.96/1.29  #Strategies tried      : 1
% 1.96/1.29  
% 1.96/1.29  Timing (in seconds)
% 1.96/1.29  ----------------------
% 1.96/1.30  Preprocessing        : 0.32
% 1.96/1.30  Parsing              : 0.17
% 1.96/1.30  CNF conversion       : 0.02
% 1.96/1.30  Main loop            : 0.16
% 1.96/1.30  Inferencing          : 0.06
% 1.96/1.30  Reduction            : 0.05
% 1.96/1.30  Demodulation         : 0.03
% 1.96/1.30  BG Simplification    : 0.01
% 1.96/1.30  Subsumption          : 0.03
% 1.96/1.30  Abstraction          : 0.01
% 1.96/1.30  MUC search           : 0.00
% 1.96/1.30  Cooper               : 0.00
% 1.96/1.30  Total                : 0.50
% 1.96/1.30  Index Insertion      : 0.00
% 1.96/1.30  Index Deletion       : 0.00
% 1.96/1.30  Index Matching       : 0.00
% 1.96/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
