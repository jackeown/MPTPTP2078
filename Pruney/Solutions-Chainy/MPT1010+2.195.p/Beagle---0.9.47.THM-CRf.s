%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:31 EST 2020

% Result     : Theorem 3.69s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :   46 (  52 expanded)
%              Number of leaves         :   28 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   53 (  79 expanded)
%              Number of equality atoms :   22 (  28 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_38,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_32,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_51,plain,(
    ! [A_23,B_24] : k2_xboole_0(k1_tarski(A_23),B_24) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_55,plain,(
    ! [A_23] : k1_tarski(A_23) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_51])).

tff(c_40,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_38,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_34,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1918,plain,(
    ! [D_2804,C_2805,B_2806,A_2807] :
      ( r2_hidden(k1_funct_1(D_2804,C_2805),B_2806)
      | k1_xboole_0 = B_2806
      | ~ r2_hidden(C_2805,A_2807)
      | ~ m1_subset_1(D_2804,k1_zfmisc_1(k2_zfmisc_1(A_2807,B_2806)))
      | ~ v1_funct_2(D_2804,A_2807,B_2806)
      | ~ v1_funct_1(D_2804) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2194,plain,(
    ! [D_3160,B_3161] :
      ( r2_hidden(k1_funct_1(D_3160,'#skF_5'),B_3161)
      | k1_xboole_0 = B_3161
      | ~ m1_subset_1(D_3160,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_3161)))
      | ~ v1_funct_2(D_3160,'#skF_3',B_3161)
      | ~ v1_funct_1(D_3160) ) ),
    inference(resolution,[status(thm)],[c_34,c_1918])).

tff(c_2203,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_2194])).

tff(c_2206,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_2203])).

tff(c_2207,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_2206])).

tff(c_22,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_84,plain,(
    ! [D_32,B_33,A_34] :
      ( D_32 = B_33
      | D_32 = A_34
      | ~ r2_hidden(D_32,k2_tarski(A_34,B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_90,plain,(
    ! [D_32,A_8] :
      ( D_32 = A_8
      | D_32 = A_8
      | ~ r2_hidden(D_32,k1_tarski(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_84])).

tff(c_2214,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2207,c_90])).

tff(c_2260,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_32,c_2214])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:20:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.69/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.73  
% 3.85/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.73  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 3.85/1.73  
% 3.85/1.73  %Foreground sorts:
% 3.85/1.73  
% 3.85/1.73  
% 3.85/1.73  %Background operators:
% 3.85/1.73  
% 3.85/1.73  
% 3.85/1.73  %Foreground operators:
% 3.85/1.73  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.85/1.73  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.85/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.85/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.85/1.73  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.85/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.85/1.73  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.85/1.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.85/1.73  tff('#skF_5', type, '#skF_5': $i).
% 3.85/1.73  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.85/1.73  tff('#skF_6', type, '#skF_6': $i).
% 3.85/1.73  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.85/1.73  tff('#skF_3', type, '#skF_3': $i).
% 3.85/1.73  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.85/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.85/1.73  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.85/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.85/1.73  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.85/1.73  tff('#skF_4', type, '#skF_4': $i).
% 3.85/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.85/1.73  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.85/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.85/1.73  
% 3.85/1.74  tff(f_68, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 3.85/1.74  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.85/1.74  tff(f_45, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.85/1.74  tff(f_57, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 3.85/1.74  tff(f_38, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.85/1.74  tff(f_36, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 3.85/1.74  tff(c_32, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.85/1.74  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.85/1.74  tff(c_51, plain, (![A_23, B_24]: (k2_xboole_0(k1_tarski(A_23), B_24)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.85/1.74  tff(c_55, plain, (![A_23]: (k1_tarski(A_23)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_51])).
% 3.85/1.74  tff(c_40, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.85/1.74  tff(c_38, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.85/1.74  tff(c_36, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.85/1.74  tff(c_34, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.85/1.74  tff(c_1918, plain, (![D_2804, C_2805, B_2806, A_2807]: (r2_hidden(k1_funct_1(D_2804, C_2805), B_2806) | k1_xboole_0=B_2806 | ~r2_hidden(C_2805, A_2807) | ~m1_subset_1(D_2804, k1_zfmisc_1(k2_zfmisc_1(A_2807, B_2806))) | ~v1_funct_2(D_2804, A_2807, B_2806) | ~v1_funct_1(D_2804))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.85/1.74  tff(c_2194, plain, (![D_3160, B_3161]: (r2_hidden(k1_funct_1(D_3160, '#skF_5'), B_3161) | k1_xboole_0=B_3161 | ~m1_subset_1(D_3160, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_3161))) | ~v1_funct_2(D_3160, '#skF_3', B_3161) | ~v1_funct_1(D_3160))), inference(resolution, [status(thm)], [c_34, c_1918])).
% 3.85/1.74  tff(c_2203, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_36, c_2194])).
% 3.85/1.74  tff(c_2206, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_2203])).
% 3.85/1.74  tff(c_2207, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_55, c_2206])).
% 3.85/1.74  tff(c_22, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.85/1.74  tff(c_84, plain, (![D_32, B_33, A_34]: (D_32=B_33 | D_32=A_34 | ~r2_hidden(D_32, k2_tarski(A_34, B_33)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.85/1.74  tff(c_90, plain, (![D_32, A_8]: (D_32=A_8 | D_32=A_8 | ~r2_hidden(D_32, k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_84])).
% 3.85/1.74  tff(c_2214, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_2207, c_90])).
% 3.85/1.74  tff(c_2260, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_32, c_2214])).
% 3.85/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.74  
% 3.85/1.74  Inference rules
% 3.85/1.74  ----------------------
% 3.85/1.74  #Ref     : 0
% 3.85/1.74  #Sup     : 293
% 3.85/1.74  #Fact    : 8
% 3.85/1.74  #Define  : 0
% 3.85/1.74  #Split   : 5
% 3.85/1.74  #Chain   : 0
% 3.85/1.74  #Close   : 0
% 3.85/1.74  
% 3.85/1.74  Ordering : KBO
% 3.85/1.74  
% 3.85/1.74  Simplification rules
% 3.85/1.74  ----------------------
% 3.85/1.74  #Subsume      : 56
% 3.85/1.74  #Demod        : 42
% 3.85/1.74  #Tautology    : 98
% 3.85/1.74  #SimpNegUnit  : 16
% 3.85/1.74  #BackRed      : 0
% 3.85/1.74  
% 3.85/1.74  #Partial instantiations: 2070
% 3.85/1.74  #Strategies tried      : 1
% 3.85/1.74  
% 3.85/1.74  Timing (in seconds)
% 3.85/1.74  ----------------------
% 3.92/1.74  Preprocessing        : 0.31
% 3.92/1.74  Parsing              : 0.16
% 3.92/1.74  CNF conversion       : 0.02
% 3.92/1.74  Main loop            : 0.64
% 3.92/1.74  Inferencing          : 0.35
% 3.92/1.74  Reduction            : 0.14
% 3.92/1.74  Demodulation         : 0.10
% 3.92/1.74  BG Simplification    : 0.03
% 3.92/1.74  Subsumption          : 0.08
% 3.92/1.74  Abstraction          : 0.04
% 3.92/1.74  MUC search           : 0.00
% 3.92/1.74  Cooper               : 0.00
% 3.92/1.74  Total                : 0.99
% 3.92/1.74  Index Insertion      : 0.00
% 3.92/1.74  Index Deletion       : 0.00
% 3.92/1.74  Index Matching       : 0.00
% 3.92/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
