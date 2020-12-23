%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:26 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   43 (  60 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 ( 115 expanded)
%              Number of equality atoms :   12 (  25 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_38,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_22,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_30,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_28,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_26,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_24,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_85,plain,(
    ! [D_27,C_28,B_29,A_30] :
      ( r2_hidden(k1_funct_1(D_27,C_28),B_29)
      | k1_xboole_0 = B_29
      | ~ r2_hidden(C_28,A_30)
      | ~ m1_subset_1(D_27,k1_zfmisc_1(k2_zfmisc_1(A_30,B_29)))
      | ~ v1_funct_2(D_27,A_30,B_29)
      | ~ v1_funct_1(D_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_99,plain,(
    ! [D_33,B_34] :
      ( r2_hidden(k1_funct_1(D_33,'#skF_5'),B_34)
      | k1_xboole_0 = B_34
      | ~ m1_subset_1(D_33,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_34)))
      | ~ v1_funct_2(D_33,'#skF_3',B_34)
      | ~ v1_funct_1(D_33) ) ),
    inference(resolution,[status(thm)],[c_24,c_85])).

tff(c_102,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_99])).

tff(c_105,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_102])).

tff(c_106,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_105])).

tff(c_18,plain,(
    ! [A_7] : ~ v1_xboole_0(k1_tarski(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_126,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_18])).

tff(c_134,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_126])).

tff(c_135,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_105])).

tff(c_4,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_141,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_135,c_4])).

tff(c_146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_141])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:53:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.28  
% 1.97/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.28  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.97/1.28  
% 1.97/1.28  %Foreground sorts:
% 1.97/1.28  
% 1.97/1.28  
% 1.97/1.28  %Background operators:
% 1.97/1.28  
% 1.97/1.28  
% 1.97/1.28  %Foreground operators:
% 1.97/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.97/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.97/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.28  tff('#skF_5', type, '#skF_5': $i).
% 1.97/1.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.97/1.28  tff('#skF_6', type, '#skF_6': $i).
% 1.97/1.28  tff('#skF_3', type, '#skF_3': $i).
% 1.97/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.97/1.28  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.97/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.97/1.28  tff('#skF_4', type, '#skF_4': $i).
% 1.97/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.97/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.97/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.97/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.97/1.28  
% 1.97/1.29  tff(f_61, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 1.97/1.29  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.97/1.29  tff(f_50, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 1.97/1.29  tff(f_38, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 1.97/1.29  tff(f_33, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 1.97/1.29  tff(c_22, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.97/1.29  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.97/1.29  tff(c_30, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.97/1.29  tff(c_28, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.97/1.29  tff(c_26, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.97/1.29  tff(c_24, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.97/1.29  tff(c_85, plain, (![D_27, C_28, B_29, A_30]: (r2_hidden(k1_funct_1(D_27, C_28), B_29) | k1_xboole_0=B_29 | ~r2_hidden(C_28, A_30) | ~m1_subset_1(D_27, k1_zfmisc_1(k2_zfmisc_1(A_30, B_29))) | ~v1_funct_2(D_27, A_30, B_29) | ~v1_funct_1(D_27))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.97/1.29  tff(c_99, plain, (![D_33, B_34]: (r2_hidden(k1_funct_1(D_33, '#skF_5'), B_34) | k1_xboole_0=B_34 | ~m1_subset_1(D_33, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_34))) | ~v1_funct_2(D_33, '#skF_3', B_34) | ~v1_funct_1(D_33))), inference(resolution, [status(thm)], [c_24, c_85])).
% 1.97/1.29  tff(c_102, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_26, c_99])).
% 1.97/1.29  tff(c_105, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_102])).
% 1.97/1.29  tff(c_106, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_105])).
% 1.97/1.29  tff(c_18, plain, (![A_7]: (~v1_xboole_0(k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.97/1.29  tff(c_126, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_106, c_18])).
% 1.97/1.29  tff(c_134, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_126])).
% 1.97/1.29  tff(c_135, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_105])).
% 1.97/1.29  tff(c_4, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.97/1.29  tff(c_141, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_135, c_4])).
% 1.97/1.29  tff(c_146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_141])).
% 1.97/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.29  
% 1.97/1.29  Inference rules
% 1.97/1.29  ----------------------
% 1.97/1.29  #Ref     : 0
% 1.97/1.29  #Sup     : 25
% 1.97/1.29  #Fact    : 0
% 1.97/1.29  #Define  : 0
% 1.97/1.29  #Split   : 1
% 1.97/1.29  #Chain   : 0
% 1.97/1.29  #Close   : 0
% 1.97/1.29  
% 1.97/1.29  Ordering : KBO
% 1.97/1.29  
% 1.97/1.29  Simplification rules
% 1.97/1.29  ----------------------
% 1.97/1.29  #Subsume      : 0
% 1.97/1.29  #Demod        : 15
% 1.97/1.29  #Tautology    : 9
% 1.97/1.29  #SimpNegUnit  : 1
% 1.97/1.29  #BackRed      : 2
% 1.97/1.29  
% 1.97/1.29  #Partial instantiations: 0
% 1.97/1.29  #Strategies tried      : 1
% 1.97/1.29  
% 1.97/1.29  Timing (in seconds)
% 1.97/1.29  ----------------------
% 1.97/1.29  Preprocessing        : 0.27
% 1.97/1.29  Parsing              : 0.14
% 1.97/1.29  CNF conversion       : 0.02
% 1.97/1.29  Main loop            : 0.16
% 1.97/1.29  Inferencing          : 0.06
% 1.97/1.29  Reduction            : 0.05
% 1.97/1.29  Demodulation         : 0.03
% 1.97/1.29  BG Simplification    : 0.01
% 1.97/1.29  Subsumption          : 0.04
% 1.97/1.29  Abstraction          : 0.01
% 1.97/1.29  MUC search           : 0.00
% 1.97/1.29  Cooper               : 0.00
% 1.97/1.29  Total                : 0.46
% 1.97/1.29  Index Insertion      : 0.00
% 1.97/1.29  Index Deletion       : 0.00
% 1.97/1.30  Index Matching       : 0.00
% 1.97/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
