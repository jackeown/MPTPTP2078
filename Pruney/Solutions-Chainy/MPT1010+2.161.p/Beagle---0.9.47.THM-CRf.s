%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:26 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   45 (  80 expanded)
%              Number of leaves         :   25 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   53 ( 179 expanded)
%              Number of equality atoms :   18 (  46 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_22,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_30,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_28,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_26,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_24,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_92,plain,(
    ! [D_31,C_32,B_33,A_34] :
      ( r2_hidden(k1_funct_1(D_31,C_32),B_33)
      | k1_xboole_0 = B_33
      | ~ r2_hidden(C_32,A_34)
      | ~ m1_subset_1(D_31,k1_zfmisc_1(k2_zfmisc_1(A_34,B_33)))
      | ~ v1_funct_2(D_31,A_34,B_33)
      | ~ v1_funct_1(D_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_106,plain,(
    ! [D_37,B_38] :
      ( r2_hidden(k1_funct_1(D_37,'#skF_5'),B_38)
      | k1_xboole_0 = B_38
      | ~ m1_subset_1(D_37,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_38)))
      | ~ v1_funct_2(D_37,'#skF_3',B_38)
      | ~ v1_funct_1(D_37) ) ),
    inference(resolution,[status(thm)],[c_24,c_92])).

tff(c_109,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_106])).

tff(c_112,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_109])).

tff(c_113,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [B_9,A_8] :
      ( r2_hidden(B_9,A_8)
      | k3_xboole_0(A_8,k1_tarski(B_9)) != k1_tarski(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_128,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_4',A_8)
      | k3_xboole_0(A_8,k1_xboole_0) != k1_tarski('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_18])).

tff(c_143,plain,(
    ! [A_39] : r2_hidden('#skF_4',A_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_2,c_128])).

tff(c_4,plain,(
    ! [C_6,A_2] :
      ( C_6 = A_2
      | ~ r2_hidden(C_6,k1_tarski(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_152,plain,(
    ! [A_40] : A_40 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_143,c_4])).

tff(c_212,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_22])).

tff(c_213,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_219,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_213,c_4])).

tff(c_224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_219])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:11:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.31  
% 2.16/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.32  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.16/1.32  
% 2.16/1.32  %Foreground sorts:
% 2.16/1.32  
% 2.16/1.32  
% 2.16/1.32  %Background operators:
% 2.16/1.32  
% 2.16/1.32  
% 2.16/1.32  %Foreground operators:
% 2.16/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.16/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.16/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.16/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.16/1.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.16/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.16/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.16/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.32  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.16/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.16/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.16/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.16/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.16/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.16/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.32  
% 2.16/1.33  tff(f_63, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 2.16/1.33  tff(f_52, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.16/1.33  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.16/1.33  tff(f_40, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 2.16/1.33  tff(f_34, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.16/1.33  tff(c_22, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.16/1.33  tff(c_30, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.16/1.33  tff(c_28, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.16/1.33  tff(c_26, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.16/1.33  tff(c_24, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.16/1.33  tff(c_92, plain, (![D_31, C_32, B_33, A_34]: (r2_hidden(k1_funct_1(D_31, C_32), B_33) | k1_xboole_0=B_33 | ~r2_hidden(C_32, A_34) | ~m1_subset_1(D_31, k1_zfmisc_1(k2_zfmisc_1(A_34, B_33))) | ~v1_funct_2(D_31, A_34, B_33) | ~v1_funct_1(D_31))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.16/1.33  tff(c_106, plain, (![D_37, B_38]: (r2_hidden(k1_funct_1(D_37, '#skF_5'), B_38) | k1_xboole_0=B_38 | ~m1_subset_1(D_37, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_38))) | ~v1_funct_2(D_37, '#skF_3', B_38) | ~v1_funct_1(D_37))), inference(resolution, [status(thm)], [c_24, c_92])).
% 2.16/1.33  tff(c_109, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_26, c_106])).
% 2.16/1.33  tff(c_112, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_109])).
% 2.16/1.33  tff(c_113, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_112])).
% 2.16/1.33  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.16/1.33  tff(c_18, plain, (![B_9, A_8]: (r2_hidden(B_9, A_8) | k3_xboole_0(A_8, k1_tarski(B_9))!=k1_tarski(B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.16/1.33  tff(c_128, plain, (![A_8]: (r2_hidden('#skF_4', A_8) | k3_xboole_0(A_8, k1_xboole_0)!=k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_113, c_18])).
% 2.16/1.33  tff(c_143, plain, (![A_39]: (r2_hidden('#skF_4', A_39))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_2, c_128])).
% 2.16/1.33  tff(c_4, plain, (![C_6, A_2]: (C_6=A_2 | ~r2_hidden(C_6, k1_tarski(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.16/1.33  tff(c_152, plain, (![A_40]: (A_40='#skF_4')), inference(resolution, [status(thm)], [c_143, c_4])).
% 2.16/1.33  tff(c_212, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_152, c_22])).
% 2.16/1.33  tff(c_213, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_112])).
% 2.16/1.33  tff(c_219, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_213, c_4])).
% 2.16/1.33  tff(c_224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_219])).
% 2.16/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.33  
% 2.16/1.33  Inference rules
% 2.16/1.33  ----------------------
% 2.16/1.33  #Ref     : 0
% 2.16/1.33  #Sup     : 55
% 2.16/1.33  #Fact    : 0
% 2.16/1.33  #Define  : 0
% 2.16/1.33  #Split   : 1
% 2.16/1.33  #Chain   : 0
% 2.16/1.33  #Close   : 0
% 2.16/1.33  
% 2.16/1.33  Ordering : KBO
% 2.16/1.33  
% 2.16/1.33  Simplification rules
% 2.16/1.33  ----------------------
% 2.16/1.33  #Subsume      : 4
% 2.16/1.33  #Demod        : 20
% 2.16/1.33  #Tautology    : 14
% 2.16/1.33  #SimpNegUnit  : 1
% 2.16/1.33  #BackRed      : 2
% 2.16/1.33  
% 2.16/1.33  #Partial instantiations: 0
% 2.16/1.33  #Strategies tried      : 1
% 2.16/1.33  
% 2.16/1.33  Timing (in seconds)
% 2.16/1.33  ----------------------
% 2.16/1.33  Preprocessing        : 0.31
% 2.16/1.33  Parsing              : 0.16
% 2.16/1.33  CNF conversion       : 0.02
% 2.16/1.33  Main loop            : 0.20
% 2.16/1.33  Inferencing          : 0.08
% 2.16/1.33  Reduction            : 0.05
% 2.16/1.33  Demodulation         : 0.04
% 2.16/1.33  BG Simplification    : 0.01
% 2.16/1.33  Subsumption          : 0.04
% 2.16/1.33  Abstraction          : 0.02
% 2.16/1.33  MUC search           : 0.00
% 2.16/1.33  Cooper               : 0.00
% 2.16/1.33  Total                : 0.54
% 2.16/1.33  Index Insertion      : 0.00
% 2.16/1.33  Index Deletion       : 0.00
% 2.16/1.33  Index Matching       : 0.00
% 2.16/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
