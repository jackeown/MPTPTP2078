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
% DateTime   : Thu Dec  3 10:15:28 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   44 (  79 expanded)
%              Number of leaves         :   24 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   53 ( 179 expanded)
%              Number of equality atoms :   18 (  46 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k3_xboole_0 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_20,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_28,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_26,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_24,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
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

tff(c_95,plain,(
    ! [D_35,B_36] :
      ( r2_hidden(k1_funct_1(D_35,'#skF_5'),B_36)
      | k1_xboole_0 = B_36
      | ~ m1_subset_1(D_35,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_36)))
      | ~ v1_funct_2(D_35,'#skF_3',B_36)
      | ~ v1_funct_1(D_35) ) ),
    inference(resolution,[status(thm)],[c_22,c_82])).

tff(c_98,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_95])).

tff(c_101,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_98])).

tff(c_102,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [B_8,A_7] :
      ( r2_hidden(B_8,A_7)
      | k3_xboole_0(A_7,k1_tarski(B_8)) != k1_tarski(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_117,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_4',A_7)
      | k3_xboole_0(A_7,k1_xboole_0) != k1_tarski('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_16])).

tff(c_136,plain,(
    ! [A_37] : r2_hidden('#skF_4',A_37) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_2,c_117])).

tff(c_4,plain,(
    ! [C_6,A_2] :
      ( C_6 = A_2
      | ~ r2_hidden(C_6,k1_tarski(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_145,plain,(
    ! [A_38] : A_38 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_136,c_4])).

tff(c_209,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_20])).

tff(c_210,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_216,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_210,c_4])).

tff(c_221,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_216])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:13:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.36  
% 2.11/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.37  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k3_xboole_0 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.11/1.37  
% 2.11/1.37  %Foreground sorts:
% 2.11/1.37  
% 2.11/1.37  
% 2.11/1.37  %Background operators:
% 2.11/1.37  
% 2.11/1.37  
% 2.11/1.37  %Foreground operators:
% 2.11/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.11/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.11/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.11/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.11/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.11/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.11/1.37  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.11/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.11/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.11/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.37  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.11/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.11/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.11/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.11/1.37  
% 2.30/1.38  tff(f_61, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_2)).
% 2.30/1.38  tff(f_50, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 2.30/1.38  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.30/1.38  tff(f_38, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_zfmisc_1)).
% 2.30/1.38  tff(f_34, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.30/1.38  tff(c_20, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.30/1.38  tff(c_28, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.30/1.38  tff(c_26, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.30/1.38  tff(c_24, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.30/1.38  tff(c_22, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.30/1.38  tff(c_82, plain, (![D_31, C_32, B_33, A_34]: (r2_hidden(k1_funct_1(D_31, C_32), B_33) | k1_xboole_0=B_33 | ~r2_hidden(C_32, A_34) | ~m1_subset_1(D_31, k1_zfmisc_1(k2_zfmisc_1(A_34, B_33))) | ~v1_funct_2(D_31, A_34, B_33) | ~v1_funct_1(D_31))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.30/1.38  tff(c_95, plain, (![D_35, B_36]: (r2_hidden(k1_funct_1(D_35, '#skF_5'), B_36) | k1_xboole_0=B_36 | ~m1_subset_1(D_35, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_36))) | ~v1_funct_2(D_35, '#skF_3', B_36) | ~v1_funct_1(D_35))), inference(resolution, [status(thm)], [c_22, c_82])).
% 2.30/1.38  tff(c_98, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_24, c_95])).
% 2.30/1.38  tff(c_101, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_98])).
% 2.30/1.38  tff(c_102, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_101])).
% 2.30/1.38  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.30/1.38  tff(c_16, plain, (![B_8, A_7]: (r2_hidden(B_8, A_7) | k3_xboole_0(A_7, k1_tarski(B_8))!=k1_tarski(B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.30/1.38  tff(c_117, plain, (![A_7]: (r2_hidden('#skF_4', A_7) | k3_xboole_0(A_7, k1_xboole_0)!=k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_16])).
% 2.30/1.38  tff(c_136, plain, (![A_37]: (r2_hidden('#skF_4', A_37))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_2, c_117])).
% 2.30/1.38  tff(c_4, plain, (![C_6, A_2]: (C_6=A_2 | ~r2_hidden(C_6, k1_tarski(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.30/1.38  tff(c_145, plain, (![A_38]: (A_38='#skF_4')), inference(resolution, [status(thm)], [c_136, c_4])).
% 2.30/1.38  tff(c_209, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_145, c_20])).
% 2.30/1.38  tff(c_210, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_101])).
% 2.30/1.38  tff(c_216, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_210, c_4])).
% 2.30/1.38  tff(c_221, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_216])).
% 2.30/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.38  
% 2.30/1.38  Inference rules
% 2.30/1.38  ----------------------
% 2.30/1.38  #Ref     : 0
% 2.30/1.38  #Sup     : 56
% 2.30/1.38  #Fact    : 0
% 2.30/1.38  #Define  : 0
% 2.30/1.38  #Split   : 1
% 2.30/1.38  #Chain   : 0
% 2.30/1.38  #Close   : 0
% 2.30/1.38  
% 2.30/1.38  Ordering : KBO
% 2.30/1.38  
% 2.30/1.38  Simplification rules
% 2.30/1.38  ----------------------
% 2.30/1.38  #Subsume      : 3
% 2.30/1.38  #Demod        : 21
% 2.30/1.38  #Tautology    : 13
% 2.30/1.38  #SimpNegUnit  : 1
% 2.30/1.38  #BackRed      : 2
% 2.30/1.38  
% 2.30/1.38  #Partial instantiations: 0
% 2.30/1.38  #Strategies tried      : 1
% 2.30/1.38  
% 2.30/1.38  Timing (in seconds)
% 2.30/1.38  ----------------------
% 2.30/1.38  Preprocessing        : 0.36
% 2.30/1.38  Parsing              : 0.15
% 2.30/1.38  CNF conversion       : 0.04
% 2.30/1.38  Main loop            : 0.24
% 2.30/1.38  Inferencing          : 0.10
% 2.30/1.38  Reduction            : 0.06
% 2.30/1.38  Demodulation         : 0.05
% 2.30/1.38  BG Simplification    : 0.02
% 2.30/1.38  Subsumption          : 0.05
% 2.30/1.38  Abstraction          : 0.01
% 2.30/1.38  MUC search           : 0.00
% 2.30/1.38  Cooper               : 0.00
% 2.30/1.38  Total                : 0.63
% 2.30/1.38  Index Insertion      : 0.00
% 2.30/1.38  Index Deletion       : 0.00
% 2.30/1.38  Index Matching       : 0.00
% 2.30/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
