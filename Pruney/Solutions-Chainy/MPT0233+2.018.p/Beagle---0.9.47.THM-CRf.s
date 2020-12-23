%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:26 EST 2020

% Result     : Theorem 4.87s
% Output     : CNFRefutation 4.87s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 191 expanded)
%              Number of leaves         :   22 (  71 expanded)
%              Depth                    :   14
%              Number of atoms          :   86 ( 422 expanded)
%              Number of equality atoms :   55 ( 312 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
        & A != B
        & A != C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(c_36,plain,(
    '#skF_1' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_38,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_40,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1835,plain,(
    ! [B_119,C_120,A_121] :
      ( k2_tarski(B_119,C_120) = A_121
      | k1_tarski(C_120) = A_121
      | k1_tarski(B_119) = A_121
      | k1_xboole_0 = A_121
      | ~ r1_tarski(A_121,k2_tarski(B_119,C_120)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1880,plain,
    ( k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_1','#skF_2')
    | k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_4')
    | k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3')
    | k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_1835])).

tff(c_1998,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1880])).

tff(c_30,plain,(
    ! [B_24,C_25] : r1_tarski(k1_tarski(B_24),k2_tarski(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2023,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1998,c_30])).

tff(c_10,plain,(
    ! [A_8] : k2_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_460,plain,(
    ! [A_66,C_67,B_68] :
      ( r1_tarski(A_66,k2_xboole_0(C_67,B_68))
      | ~ r1_tarski(A_66,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_478,plain,(
    ! [A_66,A_8] :
      ( r1_tarski(A_66,A_8)
      | ~ r1_tarski(A_66,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_460])).

tff(c_2036,plain,(
    ! [A_8] : r1_tarski(k1_tarski('#skF_1'),A_8) ),
    inference(resolution,[status(thm)],[c_2023,c_478])).

tff(c_16,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1066,plain,(
    ! [C_93,A_94,B_95] :
      ( C_93 = A_94
      | B_95 = A_94
      | ~ r1_tarski(k1_tarski(A_94),k2_tarski(B_95,C_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2087,plain,(
    ! [A_129,A_128] :
      ( A_129 = A_128
      | A_129 = A_128
      | ~ r1_tarski(k1_tarski(A_128),k1_tarski(A_129)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1066])).

tff(c_2280,plain,(
    ! [A_1130] : A_1130 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2036,c_2087])).

tff(c_2434,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_2280,c_38])).

tff(c_2435,plain,
    ( k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3')
    | k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_4')
    | k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1880])).

tff(c_2437,plain,(
    k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2435])).

tff(c_2462,plain,(
    r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2437,c_30])).

tff(c_34,plain,(
    ! [C_28,A_26,B_27] :
      ( C_28 = A_26
      | B_27 = A_26
      | ~ r1_tarski(k1_tarski(A_26),k2_tarski(B_27,C_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2475,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2462,c_34])).

tff(c_2482,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_2475])).

tff(c_28,plain,(
    ! [C_25,B_24] : r1_tarski(k1_tarski(C_25),k2_tarski(B_24,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2465,plain,(
    r1_tarski(k1_tarski('#skF_4'),k2_tarski('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2437,c_28])).

tff(c_2492,plain,(
    r1_tarski(k1_tarski('#skF_4'),k2_tarski('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2482,c_2465])).

tff(c_2498,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2492,c_34])).

tff(c_2505,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_2498])).

tff(c_2485,plain,(
    k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2482,c_2437])).

tff(c_2633,plain,(
    k2_tarski('#skF_1','#skF_4') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2505,c_16,c_2505,c_2485])).

tff(c_2650,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2633,c_30])).

tff(c_2702,plain,(
    ! [A_2142,A_2141] :
      ( A_2142 = A_2141
      | A_2142 = A_2141
      | ~ r1_tarski(k1_tarski(A_2141),k1_tarski(A_2142)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1066])).

tff(c_2705,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2650,c_2702])).

tff(c_2719,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_36,c_2705])).

tff(c_2720,plain,
    ( k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_4')
    | k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2435])).

tff(c_2723,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2720])).

tff(c_2748,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2723,c_30])).

tff(c_2764,plain,(
    ! [A_2144,A_2143] :
      ( A_2144 = A_2143
      | A_2144 = A_2143
      | ~ r1_tarski(k1_tarski(A_2143),k1_tarski(A_2144)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1066])).

tff(c_2770,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2748,c_2764])).

tff(c_2785,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_38,c_2770])).

tff(c_2786,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2720])).

tff(c_2812,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2786,c_30])).

tff(c_3442,plain,(
    ! [A_2151,A_2150] :
      ( A_2151 = A_2150
      | A_2151 = A_2150
      | ~ r1_tarski(k1_tarski(A_2150),k1_tarski(A_2151)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1066])).

tff(c_3445,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2812,c_3442])).

tff(c_3462,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_36,c_3445])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:33:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.87/1.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.87/1.87  
% 4.87/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.87/1.87  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.87/1.87  
% 4.87/1.87  %Foreground sorts:
% 4.87/1.87  
% 4.87/1.87  
% 4.87/1.87  %Background operators:
% 4.87/1.87  
% 4.87/1.87  
% 4.87/1.87  %Foreground operators:
% 4.87/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.87/1.87  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.87/1.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.87/1.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.87/1.87  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.87/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.87/1.87  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.87/1.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.87/1.87  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.87/1.87  tff('#skF_2', type, '#skF_2': $i).
% 4.87/1.87  tff('#skF_3', type, '#skF_3': $i).
% 4.87/1.87  tff('#skF_1', type, '#skF_1': $i).
% 4.87/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.87/1.87  tff('#skF_4', type, '#skF_4': $i).
% 4.87/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.87/1.87  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.87/1.87  
% 4.87/1.88  tff(f_83, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 4.87/1.88  tff(f_64, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 4.87/1.88  tff(f_37, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.87/1.88  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 4.87/1.88  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.87/1.88  tff(f_73, axiom, (![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 4.87/1.88  tff(c_36, plain, ('#skF_1'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.87/1.88  tff(c_38, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.87/1.88  tff(c_40, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.87/1.88  tff(c_1835, plain, (![B_119, C_120, A_121]: (k2_tarski(B_119, C_120)=A_121 | k1_tarski(C_120)=A_121 | k1_tarski(B_119)=A_121 | k1_xboole_0=A_121 | ~r1_tarski(A_121, k2_tarski(B_119, C_120)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.87/1.88  tff(c_1880, plain, (k2_tarski('#skF_3', '#skF_4')=k2_tarski('#skF_1', '#skF_2') | k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_4') | k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_3') | k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_1835])).
% 4.87/1.88  tff(c_1998, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1880])).
% 4.87/1.88  tff(c_30, plain, (![B_24, C_25]: (r1_tarski(k1_tarski(B_24), k2_tarski(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.87/1.88  tff(c_2023, plain, (r1_tarski(k1_tarski('#skF_1'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1998, c_30])).
% 4.87/1.88  tff(c_10, plain, (![A_8]: (k2_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.87/1.88  tff(c_460, plain, (![A_66, C_67, B_68]: (r1_tarski(A_66, k2_xboole_0(C_67, B_68)) | ~r1_tarski(A_66, B_68))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.87/1.88  tff(c_478, plain, (![A_66, A_8]: (r1_tarski(A_66, A_8) | ~r1_tarski(A_66, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_460])).
% 4.87/1.88  tff(c_2036, plain, (![A_8]: (r1_tarski(k1_tarski('#skF_1'), A_8))), inference(resolution, [status(thm)], [c_2023, c_478])).
% 4.87/1.88  tff(c_16, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.87/1.88  tff(c_1066, plain, (![C_93, A_94, B_95]: (C_93=A_94 | B_95=A_94 | ~r1_tarski(k1_tarski(A_94), k2_tarski(B_95, C_93)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.87/1.88  tff(c_2087, plain, (![A_129, A_128]: (A_129=A_128 | A_129=A_128 | ~r1_tarski(k1_tarski(A_128), k1_tarski(A_129)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1066])).
% 4.87/1.88  tff(c_2280, plain, (![A_1130]: (A_1130='#skF_1')), inference(resolution, [status(thm)], [c_2036, c_2087])).
% 4.87/1.88  tff(c_2434, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_2280, c_38])).
% 4.87/1.88  tff(c_2435, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_3') | k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_4') | k2_tarski('#skF_3', '#skF_4')=k2_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_1880])).
% 4.87/1.88  tff(c_2437, plain, (k2_tarski('#skF_3', '#skF_4')=k2_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_2435])).
% 4.87/1.88  tff(c_2462, plain, (r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2437, c_30])).
% 4.87/1.88  tff(c_34, plain, (![C_28, A_26, B_27]: (C_28=A_26 | B_27=A_26 | ~r1_tarski(k1_tarski(A_26), k2_tarski(B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.87/1.88  tff(c_2475, plain, ('#skF_2'='#skF_3' | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_2462, c_34])).
% 4.87/1.88  tff(c_2482, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_38, c_2475])).
% 4.87/1.88  tff(c_28, plain, (![C_25, B_24]: (r1_tarski(k1_tarski(C_25), k2_tarski(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.87/1.88  tff(c_2465, plain, (r1_tarski(k1_tarski('#skF_4'), k2_tarski('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_2437, c_28])).
% 4.87/1.88  tff(c_2492, plain, (r1_tarski(k1_tarski('#skF_4'), k2_tarski('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2482, c_2465])).
% 4.87/1.88  tff(c_2498, plain, ('#skF_3'='#skF_4' | '#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_2492, c_34])).
% 4.87/1.88  tff(c_2505, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_36, c_2498])).
% 4.87/1.88  tff(c_2485, plain, (k2_tarski('#skF_3', '#skF_4')=k2_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2482, c_2437])).
% 4.87/1.88  tff(c_2633, plain, (k2_tarski('#skF_1', '#skF_4')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2505, c_16, c_2505, c_2485])).
% 4.87/1.88  tff(c_2650, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2633, c_30])).
% 4.87/1.88  tff(c_2702, plain, (![A_2142, A_2141]: (A_2142=A_2141 | A_2142=A_2141 | ~r1_tarski(k1_tarski(A_2141), k1_tarski(A_2142)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1066])).
% 4.87/1.88  tff(c_2705, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_2650, c_2702])).
% 4.87/1.88  tff(c_2719, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_36, c_2705])).
% 4.87/1.88  tff(c_2720, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_4') | k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_2435])).
% 4.87/1.88  tff(c_2723, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_3')), inference(splitLeft, [status(thm)], [c_2720])).
% 4.87/1.88  tff(c_2748, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2723, c_30])).
% 4.87/1.88  tff(c_2764, plain, (![A_2144, A_2143]: (A_2144=A_2143 | A_2144=A_2143 | ~r1_tarski(k1_tarski(A_2143), k1_tarski(A_2144)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1066])).
% 4.87/1.88  tff(c_2770, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_2748, c_2764])).
% 4.87/1.88  tff(c_2785, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_38, c_2770])).
% 4.87/1.88  tff(c_2786, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_2720])).
% 4.87/1.88  tff(c_2812, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2786, c_30])).
% 4.87/1.88  tff(c_3442, plain, (![A_2151, A_2150]: (A_2151=A_2150 | A_2151=A_2150 | ~r1_tarski(k1_tarski(A_2150), k1_tarski(A_2151)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1066])).
% 4.87/1.88  tff(c_3445, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_2812, c_3442])).
% 4.87/1.88  tff(c_3462, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_36, c_3445])).
% 4.87/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.87/1.88  
% 4.87/1.88  Inference rules
% 4.87/1.88  ----------------------
% 4.87/1.88  #Ref     : 1
% 4.87/1.88  #Sup     : 938
% 4.87/1.88  #Fact    : 0
% 4.87/1.88  #Define  : 0
% 4.87/1.88  #Split   : 3
% 4.87/1.88  #Chain   : 0
% 4.87/1.88  #Close   : 0
% 4.87/1.88  
% 4.87/1.88  Ordering : KBO
% 4.87/1.88  
% 4.87/1.88  Simplification rules
% 4.87/1.88  ----------------------
% 4.87/1.88  #Subsume      : 131
% 4.87/1.88  #Demod        : 523
% 4.87/1.88  #Tautology    : 506
% 4.87/1.88  #SimpNegUnit  : 7
% 4.87/1.88  #BackRed      : 31
% 4.87/1.88  
% 4.87/1.88  #Partial instantiations: 208
% 4.87/1.88  #Strategies tried      : 1
% 4.87/1.88  
% 4.87/1.88  Timing (in seconds)
% 4.87/1.88  ----------------------
% 4.87/1.88  Preprocessing        : 0.32
% 4.87/1.88  Parsing              : 0.17
% 4.87/1.88  CNF conversion       : 0.02
% 4.87/1.88  Main loop            : 0.79
% 4.87/1.88  Inferencing          : 0.26
% 4.87/1.88  Reduction            : 0.32
% 4.87/1.88  Demodulation         : 0.26
% 4.87/1.88  BG Simplification    : 0.03
% 4.87/1.88  Subsumption          : 0.13
% 4.87/1.88  Abstraction          : 0.03
% 4.87/1.89  MUC search           : 0.00
% 4.87/1.89  Cooper               : 0.00
% 4.87/1.89  Total                : 1.14
% 4.87/1.89  Index Insertion      : 0.00
% 4.87/1.89  Index Deletion       : 0.00
% 4.87/1.89  Index Matching       : 0.00
% 4.87/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
