%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:26 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   44 (  65 expanded)
%              Number of leaves         :   24 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   53 ( 131 expanded)
%              Number of equality atoms :   13 (  31 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

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
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_34,axiom,(
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
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

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

tff(c_82,plain,(
    ! [D_31,C_32,B_33,A_34] :
      ( r2_hidden(k1_funct_1(D_31,C_32),B_33)
      | k1_xboole_0 = B_33
      | ~ r2_hidden(C_32,A_34)
      | ~ m1_subset_1(D_31,k1_zfmisc_1(k2_zfmisc_1(A_34,B_33)))
      | ~ v1_funct_2(D_31,A_34,B_33)
      | ~ v1_funct_1(D_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_96,plain,(
    ! [D_37,B_38] :
      ( r2_hidden(k1_funct_1(D_37,'#skF_5'),B_38)
      | k1_xboole_0 = B_38
      | ~ m1_subset_1(D_37,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_38)))
      | ~ v1_funct_2(D_37,'#skF_3',B_38)
      | ~ v1_funct_1(D_37) ) ),
    inference(resolution,[status(thm)],[c_24,c_82])).

tff(c_99,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_96])).

tff(c_102,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_99])).

tff(c_103,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_102])).

tff(c_16,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | ~ r1_tarski(k1_tarski(A_7),B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_118,plain,(
    ! [B_8] :
      ( r2_hidden('#skF_4',B_8)
      | ~ r1_tarski(k1_xboole_0,B_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_16])).

tff(c_137,plain,(
    ! [B_39] : r2_hidden('#skF_4',B_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_118])).

tff(c_4,plain,(
    ! [C_6,A_2] :
      ( C_6 = A_2
      | ~ r2_hidden(C_6,k1_tarski(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_146,plain,(
    ! [A_40] : A_40 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_137,c_4])).

tff(c_202,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_22])).

tff(c_203,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_102])).

tff(c_209,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_203,c_4])).

tff(c_214,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_209])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:00:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.24  
% 2.06/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.24  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.06/1.24  
% 2.06/1.24  %Foreground sorts:
% 2.06/1.24  
% 2.06/1.24  
% 2.06/1.24  %Background operators:
% 2.06/1.24  
% 2.06/1.24  
% 2.06/1.24  %Foreground operators:
% 2.06/1.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.06/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.06/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.24  tff('#skF_5', type, '#skF_5': $i).
% 2.06/1.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.06/1.24  tff('#skF_6', type, '#skF_6': $i).
% 2.06/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.06/1.24  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.06/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.06/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.24  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.06/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.06/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.06/1.24  
% 2.06/1.25  tff(f_61, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 2.06/1.25  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.06/1.25  tff(f_50, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.06/1.25  tff(f_38, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.06/1.25  tff(f_34, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.06/1.25  tff(c_22, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.06/1.25  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.06/1.25  tff(c_30, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.06/1.25  tff(c_28, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.06/1.25  tff(c_26, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.06/1.25  tff(c_24, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.06/1.25  tff(c_82, plain, (![D_31, C_32, B_33, A_34]: (r2_hidden(k1_funct_1(D_31, C_32), B_33) | k1_xboole_0=B_33 | ~r2_hidden(C_32, A_34) | ~m1_subset_1(D_31, k1_zfmisc_1(k2_zfmisc_1(A_34, B_33))) | ~v1_funct_2(D_31, A_34, B_33) | ~v1_funct_1(D_31))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.06/1.25  tff(c_96, plain, (![D_37, B_38]: (r2_hidden(k1_funct_1(D_37, '#skF_5'), B_38) | k1_xboole_0=B_38 | ~m1_subset_1(D_37, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_38))) | ~v1_funct_2(D_37, '#skF_3', B_38) | ~v1_funct_1(D_37))), inference(resolution, [status(thm)], [c_24, c_82])).
% 2.06/1.25  tff(c_99, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_26, c_96])).
% 2.06/1.25  tff(c_102, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_99])).
% 2.06/1.25  tff(c_103, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_102])).
% 2.06/1.25  tff(c_16, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | ~r1_tarski(k1_tarski(A_7), B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.06/1.25  tff(c_118, plain, (![B_8]: (r2_hidden('#skF_4', B_8) | ~r1_tarski(k1_xboole_0, B_8))), inference(superposition, [status(thm), theory('equality')], [c_103, c_16])).
% 2.06/1.25  tff(c_137, plain, (![B_39]: (r2_hidden('#skF_4', B_39))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_118])).
% 2.06/1.25  tff(c_4, plain, (![C_6, A_2]: (C_6=A_2 | ~r2_hidden(C_6, k1_tarski(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.06/1.25  tff(c_146, plain, (![A_40]: (A_40='#skF_4')), inference(resolution, [status(thm)], [c_137, c_4])).
% 2.06/1.25  tff(c_202, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_146, c_22])).
% 2.06/1.25  tff(c_203, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_102])).
% 2.06/1.25  tff(c_209, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_203, c_4])).
% 2.06/1.25  tff(c_214, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_209])).
% 2.06/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.25  
% 2.06/1.25  Inference rules
% 2.06/1.25  ----------------------
% 2.06/1.25  #Ref     : 0
% 2.06/1.25  #Sup     : 51
% 2.06/1.25  #Fact    : 0
% 2.06/1.25  #Define  : 0
% 2.06/1.25  #Split   : 1
% 2.06/1.25  #Chain   : 0
% 2.06/1.25  #Close   : 0
% 2.06/1.25  
% 2.06/1.25  Ordering : KBO
% 2.06/1.25  
% 2.06/1.25  Simplification rules
% 2.06/1.25  ----------------------
% 2.06/1.25  #Subsume      : 2
% 2.06/1.25  #Demod        : 20
% 2.06/1.25  #Tautology    : 12
% 2.06/1.25  #SimpNegUnit  : 1
% 2.06/1.25  #BackRed      : 2
% 2.06/1.25  
% 2.06/1.25  #Partial instantiations: 0
% 2.06/1.25  #Strategies tried      : 1
% 2.06/1.25  
% 2.06/1.25  Timing (in seconds)
% 2.06/1.25  ----------------------
% 2.06/1.26  Preprocessing        : 0.28
% 2.06/1.26  Parsing              : 0.15
% 2.06/1.26  CNF conversion       : 0.02
% 2.06/1.26  Main loop            : 0.21
% 2.06/1.26  Inferencing          : 0.09
% 2.06/1.26  Reduction            : 0.06
% 2.06/1.26  Demodulation         : 0.04
% 2.06/1.26  BG Simplification    : 0.01
% 2.06/1.26  Subsumption          : 0.05
% 2.06/1.26  Abstraction          : 0.01
% 2.06/1.26  MUC search           : 0.00
% 2.06/1.26  Cooper               : 0.00
% 2.06/1.26  Total                : 0.52
% 2.06/1.26  Index Insertion      : 0.00
% 2.12/1.26  Index Deletion       : 0.00
% 2.12/1.26  Index Matching       : 0.00
% 2.12/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
