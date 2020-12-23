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
% DateTime   : Thu Dec  3 09:56:58 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   44 (  55 expanded)
%              Number of leaves         :   22 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   53 (  90 expanded)
%              Number of equality atoms :    6 (  10 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,A)
       => ( A != k1_xboole_0
         => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_60,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_38,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_57,plain,(
    ! [B_23,A_24] :
      ( v1_xboole_0(B_23)
      | ~ m1_subset_1(B_23,A_24)
      | ~ v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_65,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_57])).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_65])).

tff(c_106,plain,(
    ! [B_34,A_35] :
      ( r2_hidden(B_34,A_35)
      | ~ m1_subset_1(B_34,A_35)
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(k1_tarski(A_9),B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_32,plain,(
    ! [A_13] : ~ v1_xboole_0(k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10,plain,(
    ! [C_8,A_4] :
      ( r2_hidden(C_8,k1_zfmisc_1(A_4))
      | ~ r1_tarski(C_8,A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_86,plain,(
    ! [B_30,A_31] :
      ( m1_subset_1(B_30,A_31)
      | ~ r2_hidden(B_30,A_31)
      | v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_89,plain,(
    ! [C_8,A_4] :
      ( m1_subset_1(C_8,k1_zfmisc_1(A_4))
      | v1_xboole_0(k1_zfmisc_1(A_4))
      | ~ r1_tarski(C_8,A_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_86])).

tff(c_93,plain,(
    ! [C_32,A_33] :
      ( m1_subset_1(C_32,k1_zfmisc_1(A_33))
      | ~ r1_tarski(C_32,A_33) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_89])).

tff(c_34,plain,(
    ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_101,plain,(
    ~ r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_93,c_34])).

tff(c_105,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_101])).

tff(c_109,plain,
    ( ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_106,c_105])).

tff(c_119,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_109])).

tff(c_121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_119])).

tff(c_123,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_65])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_130,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_123,c_2])).

tff(c_134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_130])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:22:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.16  
% 1.82/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.16  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.82/1.16  
% 1.82/1.16  %Foreground sorts:
% 1.82/1.16  
% 1.82/1.16  
% 1.82/1.16  %Background operators:
% 1.82/1.16  
% 1.82/1.16  
% 1.82/1.16  %Foreground operators:
% 1.82/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.82/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.82/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.82/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.82/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.82/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.82/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.82/1.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.82/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.82/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.82/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.82/1.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.82/1.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.82/1.16  
% 1.82/1.17  tff(f_68, negated_conjecture, ~(![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_subset_1)).
% 1.82/1.17  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 1.82/1.17  tff(f_44, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 1.82/1.17  tff(f_60, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.82/1.17  tff(f_40, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.82/1.17  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.82/1.17  tff(c_36, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.82/1.17  tff(c_38, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.82/1.17  tff(c_57, plain, (![B_23, A_24]: (v1_xboole_0(B_23) | ~m1_subset_1(B_23, A_24) | ~v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.82/1.17  tff(c_65, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_57])).
% 1.82/1.17  tff(c_66, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_65])).
% 1.82/1.17  tff(c_106, plain, (![B_34, A_35]: (r2_hidden(B_34, A_35) | ~m1_subset_1(B_34, A_35) | v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.82/1.17  tff(c_22, plain, (![A_9, B_10]: (r1_tarski(k1_tarski(A_9), B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.82/1.17  tff(c_32, plain, (![A_13]: (~v1_xboole_0(k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.82/1.17  tff(c_10, plain, (![C_8, A_4]: (r2_hidden(C_8, k1_zfmisc_1(A_4)) | ~r1_tarski(C_8, A_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.82/1.17  tff(c_86, plain, (![B_30, A_31]: (m1_subset_1(B_30, A_31) | ~r2_hidden(B_30, A_31) | v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.82/1.17  tff(c_89, plain, (![C_8, A_4]: (m1_subset_1(C_8, k1_zfmisc_1(A_4)) | v1_xboole_0(k1_zfmisc_1(A_4)) | ~r1_tarski(C_8, A_4))), inference(resolution, [status(thm)], [c_10, c_86])).
% 1.82/1.17  tff(c_93, plain, (![C_32, A_33]: (m1_subset_1(C_32, k1_zfmisc_1(A_33)) | ~r1_tarski(C_32, A_33))), inference(negUnitSimplification, [status(thm)], [c_32, c_89])).
% 1.82/1.17  tff(c_34, plain, (~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.82/1.17  tff(c_101, plain, (~r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_93, c_34])).
% 1.82/1.17  tff(c_105, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_101])).
% 1.82/1.17  tff(c_109, plain, (~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_106, c_105])).
% 1.82/1.17  tff(c_119, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_109])).
% 1.82/1.17  tff(c_121, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_119])).
% 1.82/1.17  tff(c_123, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_65])).
% 1.82/1.17  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.82/1.17  tff(c_130, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_123, c_2])).
% 1.82/1.17  tff(c_134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_130])).
% 1.82/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.17  
% 1.82/1.17  Inference rules
% 1.82/1.17  ----------------------
% 1.82/1.17  #Ref     : 0
% 1.82/1.17  #Sup     : 18
% 1.82/1.17  #Fact    : 0
% 1.82/1.17  #Define  : 0
% 1.82/1.17  #Split   : 1
% 1.82/1.17  #Chain   : 0
% 1.82/1.17  #Close   : 0
% 1.82/1.17  
% 1.82/1.17  Ordering : KBO
% 1.82/1.17  
% 1.82/1.17  Simplification rules
% 1.82/1.17  ----------------------
% 1.82/1.17  #Subsume      : 2
% 1.82/1.17  #Demod        : 1
% 1.82/1.17  #Tautology    : 7
% 1.82/1.17  #SimpNegUnit  : 3
% 1.82/1.17  #BackRed      : 0
% 1.82/1.17  
% 1.82/1.17  #Partial instantiations: 0
% 1.82/1.17  #Strategies tried      : 1
% 1.82/1.17  
% 1.82/1.17  Timing (in seconds)
% 1.82/1.17  ----------------------
% 1.82/1.17  Preprocessing        : 0.29
% 1.82/1.17  Parsing              : 0.15
% 1.82/1.17  CNF conversion       : 0.02
% 1.82/1.17  Main loop            : 0.12
% 1.82/1.17  Inferencing          : 0.04
% 1.82/1.17  Reduction            : 0.03
% 1.82/1.17  Demodulation         : 0.02
% 1.82/1.17  BG Simplification    : 0.01
% 1.82/1.17  Subsumption          : 0.02
% 1.82/1.17  Abstraction          : 0.01
% 1.82/1.17  MUC search           : 0.00
% 1.82/1.17  Cooper               : 0.00
% 1.82/1.17  Total                : 0.43
% 1.82/1.17  Index Insertion      : 0.00
% 1.82/1.17  Index Deletion       : 0.00
% 1.82/1.17  Index Matching       : 0.00
% 1.82/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
