%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:28 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   45 (  63 expanded)
%              Number of leaves         :   25 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   52 ( 122 expanded)
%              Number of equality atoms :   12 (  27 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_64,negated_conjecture,(
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

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_41,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_22,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_28,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_26,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_149,plain,(
    ! [D_37,C_38,B_39,A_40] :
      ( r2_hidden(k1_funct_1(D_37,C_38),B_39)
      | k1_xboole_0 = B_39
      | ~ r2_hidden(C_38,A_40)
      | ~ m1_subset_1(D_37,k1_zfmisc_1(k2_zfmisc_1(A_40,B_39)))
      | ~ v1_funct_2(D_37,A_40,B_39)
      | ~ v1_funct_1(D_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_202,plain,(
    ! [D_46,B_47] :
      ( r2_hidden(k1_funct_1(D_46,'#skF_5'),B_47)
      | k1_xboole_0 = B_47
      | ~ m1_subset_1(D_46,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_47)))
      | ~ v1_funct_2(D_46,'#skF_3',B_47)
      | ~ v1_funct_1(D_46) ) ),
    inference(resolution,[status(thm)],[c_24,c_149])).

tff(c_205,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_202])).

tff(c_208,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_205])).

tff(c_209,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_208])).

tff(c_6,plain,(
    ! [C_6] : r2_hidden(C_6,k1_tarski(C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_42,plain,(
    ! [B_17,A_18] :
      ( ~ r1_tarski(B_17,A_18)
      | ~ r2_hidden(A_18,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_49,plain,(
    ! [C_6] : ~ r1_tarski(k1_tarski(C_6),C_6) ),
    inference(resolution,[status(thm)],[c_6,c_42])).

tff(c_227,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_49])).

tff(c_238,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_227])).

tff(c_239,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_208])).

tff(c_4,plain,(
    ! [C_6,A_2] :
      ( C_6 = A_2
      | ~ r2_hidden(C_6,k1_tarski(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_245,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_239,c_4])).

tff(c_253,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_245])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:49:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.23  
% 1.82/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.23  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.82/1.23  
% 1.82/1.23  %Foreground sorts:
% 1.82/1.23  
% 1.82/1.23  
% 1.82/1.23  %Background operators:
% 1.82/1.23  
% 1.82/1.23  
% 1.82/1.23  %Foreground operators:
% 1.82/1.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.82/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.82/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.82/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.82/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.82/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.82/1.23  tff('#skF_5', type, '#skF_5': $i).
% 1.82/1.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.82/1.23  tff('#skF_6', type, '#skF_6': $i).
% 1.82/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.82/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.82/1.23  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.82/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.82/1.23  tff('#skF_4', type, '#skF_4': $i).
% 1.82/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.82/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.82/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.82/1.23  
% 2.04/1.24  tff(f_64, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 2.04/1.24  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.04/1.24  tff(f_53, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.04/1.24  tff(f_34, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.04/1.24  tff(f_41, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.04/1.24  tff(c_22, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.04/1.24  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.04/1.24  tff(c_30, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.04/1.24  tff(c_28, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.04/1.24  tff(c_26, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.04/1.24  tff(c_24, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.04/1.24  tff(c_149, plain, (![D_37, C_38, B_39, A_40]: (r2_hidden(k1_funct_1(D_37, C_38), B_39) | k1_xboole_0=B_39 | ~r2_hidden(C_38, A_40) | ~m1_subset_1(D_37, k1_zfmisc_1(k2_zfmisc_1(A_40, B_39))) | ~v1_funct_2(D_37, A_40, B_39) | ~v1_funct_1(D_37))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.04/1.24  tff(c_202, plain, (![D_46, B_47]: (r2_hidden(k1_funct_1(D_46, '#skF_5'), B_47) | k1_xboole_0=B_47 | ~m1_subset_1(D_46, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_47))) | ~v1_funct_2(D_46, '#skF_3', B_47) | ~v1_funct_1(D_46))), inference(resolution, [status(thm)], [c_24, c_149])).
% 2.04/1.24  tff(c_205, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_26, c_202])).
% 2.04/1.24  tff(c_208, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_205])).
% 2.04/1.24  tff(c_209, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_208])).
% 2.04/1.24  tff(c_6, plain, (![C_6]: (r2_hidden(C_6, k1_tarski(C_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.04/1.24  tff(c_42, plain, (![B_17, A_18]: (~r1_tarski(B_17, A_18) | ~r2_hidden(A_18, B_17))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.04/1.24  tff(c_49, plain, (![C_6]: (~r1_tarski(k1_tarski(C_6), C_6))), inference(resolution, [status(thm)], [c_6, c_42])).
% 2.04/1.24  tff(c_227, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_209, c_49])).
% 2.04/1.24  tff(c_238, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_227])).
% 2.04/1.24  tff(c_239, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_208])).
% 2.04/1.24  tff(c_4, plain, (![C_6, A_2]: (C_6=A_2 | ~r2_hidden(C_6, k1_tarski(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.04/1.24  tff(c_245, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_239, c_4])).
% 2.04/1.24  tff(c_253, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_245])).
% 2.04/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.24  
% 2.04/1.24  Inference rules
% 2.04/1.24  ----------------------
% 2.04/1.24  #Ref     : 0
% 2.04/1.24  #Sup     : 47
% 2.04/1.24  #Fact    : 0
% 2.04/1.24  #Define  : 0
% 2.04/1.24  #Split   : 1
% 2.04/1.24  #Chain   : 0
% 2.04/1.24  #Close   : 0
% 2.04/1.24  
% 2.04/1.24  Ordering : KBO
% 2.04/1.24  
% 2.04/1.24  Simplification rules
% 2.04/1.24  ----------------------
% 2.04/1.24  #Subsume      : 5
% 2.04/1.24  #Demod        : 29
% 2.04/1.24  #Tautology    : 21
% 2.04/1.24  #SimpNegUnit  : 1
% 2.04/1.24  #BackRed      : 2
% 2.04/1.24  
% 2.04/1.24  #Partial instantiations: 0
% 2.04/1.24  #Strategies tried      : 1
% 2.04/1.24  
% 2.04/1.24  Timing (in seconds)
% 2.04/1.24  ----------------------
% 2.04/1.24  Preprocessing        : 0.28
% 2.04/1.24  Parsing              : 0.15
% 2.04/1.24  CNF conversion       : 0.02
% 2.04/1.24  Main loop            : 0.20
% 2.04/1.24  Inferencing          : 0.07
% 2.04/1.24  Reduction            : 0.06
% 2.04/1.24  Demodulation         : 0.04
% 2.04/1.24  BG Simplification    : 0.01
% 2.04/1.24  Subsumption          : 0.04
% 2.04/1.24  Abstraction          : 0.02
% 2.04/1.24  MUC search           : 0.00
% 2.04/1.24  Cooper               : 0.00
% 2.04/1.24  Total                : 0.50
% 2.04/1.24  Index Insertion      : 0.00
% 2.04/1.24  Index Deletion       : 0.00
% 2.04/1.24  Index Matching       : 0.00
% 2.04/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
