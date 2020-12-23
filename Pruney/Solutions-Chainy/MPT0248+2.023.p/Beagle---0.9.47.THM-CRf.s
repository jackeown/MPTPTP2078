%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:07 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   56 (  88 expanded)
%              Number of leaves         :   21 (  38 expanded)
%              Depth                    :    7
%              Number of atoms          :   67 ( 190 expanded)
%              Number of equality atoms :   46 ( 163 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_32,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_51,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_30,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_50,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_36,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_218,plain,(
    ! [A_38,C_39,B_40] :
      ( r1_tarski(A_38,C_39)
      | ~ r1_tarski(k2_xboole_0(A_38,B_40),C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_254,plain,(
    ! [A_44,B_45] : r1_tarski(A_44,k2_xboole_0(A_44,B_45)) ),
    inference(resolution,[status(thm)],[c_8,c_218])).

tff(c_278,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_254])).

tff(c_371,plain,(
    ! [B_51,A_52] :
      ( k1_tarski(B_51) = A_52
      | k1_xboole_0 = A_52
      | ~ r1_tarski(A_52,k1_tarski(B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_377,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_278,c_371])).

tff(c_390,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_50,c_377])).

tff(c_391,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_392,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_12,plain,(
    ! [A_8] : k2_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_393,plain,(
    ! [A_8] : k2_xboole_0(A_8,'#skF_2') = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_12])).

tff(c_422,plain,(
    ! [B_56,A_57] : k2_xboole_0(B_56,A_57) = k2_xboole_0(A_57,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_437,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_36])).

tff(c_477,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_437])).

tff(c_479,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_391,c_477])).

tff(c_480,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_481,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_34,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_496,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_481,c_34])).

tff(c_506,plain,(
    ! [B_59,A_60] : k2_xboole_0(B_59,A_60) = k2_xboole_0(A_60,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_488,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_36])).

tff(c_521,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_488])).

tff(c_655,plain,(
    ! [A_67,C_68,B_69] :
      ( r1_tarski(A_67,C_68)
      | ~ r1_tarski(k2_xboole_0(A_67,B_69),C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_700,plain,(
    ! [A_72,B_73] : r1_tarski(A_72,k2_xboole_0(A_72,B_73)) ),
    inference(resolution,[status(thm)],[c_8,c_655])).

tff(c_718,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_521,c_700])).

tff(c_921,plain,(
    ! [B_86,A_87] :
      ( k1_tarski(B_86) = A_87
      | k1_xboole_0 = A_87
      | ~ r1_tarski(A_87,k1_tarski(B_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_928,plain,(
    ! [A_87] :
      ( k1_tarski('#skF_1') = A_87
      | k1_xboole_0 = A_87
      | ~ r1_tarski(A_87,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_481,c_921])).

tff(c_985,plain,(
    ! [A_90] :
      ( A_90 = '#skF_2'
      | k1_xboole_0 = A_90
      | ~ r1_tarski(A_90,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_928])).

tff(c_988,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_718,c_985])).

tff(c_1000,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_480,c_496,c_988])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:29:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.38  
% 2.50/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.38  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.50/1.38  
% 2.50/1.38  %Foreground sorts:
% 2.50/1.38  
% 2.50/1.38  
% 2.50/1.38  %Background operators:
% 2.50/1.38  
% 2.50/1.38  
% 2.50/1.38  %Foreground operators:
% 2.50/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.50/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.50/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.50/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.50/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.50/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.50/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.50/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.50/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.50/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.50/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.50/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.50/1.38  
% 2.74/1.39  tff(f_74, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.74/1.39  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.74/1.39  tff(f_37, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.74/1.39  tff(f_53, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.74/1.39  tff(f_39, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.74/1.39  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.74/1.39  tff(c_32, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.74/1.39  tff(c_51, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_32])).
% 2.74/1.39  tff(c_30, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.74/1.39  tff(c_50, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_30])).
% 2.74/1.39  tff(c_36, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.74/1.39  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.74/1.39  tff(c_218, plain, (![A_38, C_39, B_40]: (r1_tarski(A_38, C_39) | ~r1_tarski(k2_xboole_0(A_38, B_40), C_39))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.74/1.39  tff(c_254, plain, (![A_44, B_45]: (r1_tarski(A_44, k2_xboole_0(A_44, B_45)))), inference(resolution, [status(thm)], [c_8, c_218])).
% 2.74/1.39  tff(c_278, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_254])).
% 2.74/1.39  tff(c_371, plain, (![B_51, A_52]: (k1_tarski(B_51)=A_52 | k1_xboole_0=A_52 | ~r1_tarski(A_52, k1_tarski(B_51)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.74/1.39  tff(c_377, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_278, c_371])).
% 2.74/1.39  tff(c_390, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_50, c_377])).
% 2.74/1.39  tff(c_391, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_32])).
% 2.74/1.39  tff(c_392, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_32])).
% 2.74/1.39  tff(c_12, plain, (![A_8]: (k2_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.74/1.39  tff(c_393, plain, (![A_8]: (k2_xboole_0(A_8, '#skF_2')=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_392, c_12])).
% 2.74/1.39  tff(c_422, plain, (![B_56, A_57]: (k2_xboole_0(B_56, A_57)=k2_xboole_0(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.74/1.39  tff(c_437, plain, (k2_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_422, c_36])).
% 2.74/1.39  tff(c_477, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_393, c_437])).
% 2.74/1.39  tff(c_479, plain, $false, inference(negUnitSimplification, [status(thm)], [c_391, c_477])).
% 2.74/1.39  tff(c_480, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_30])).
% 2.74/1.39  tff(c_481, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_30])).
% 2.74/1.39  tff(c_34, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.74/1.39  tff(c_496, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_481, c_481, c_34])).
% 2.74/1.39  tff(c_506, plain, (![B_59, A_60]: (k2_xboole_0(B_59, A_60)=k2_xboole_0(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.74/1.39  tff(c_488, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_481, c_36])).
% 2.74/1.39  tff(c_521, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_506, c_488])).
% 2.74/1.39  tff(c_655, plain, (![A_67, C_68, B_69]: (r1_tarski(A_67, C_68) | ~r1_tarski(k2_xboole_0(A_67, B_69), C_68))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.74/1.39  tff(c_700, plain, (![A_72, B_73]: (r1_tarski(A_72, k2_xboole_0(A_72, B_73)))), inference(resolution, [status(thm)], [c_8, c_655])).
% 2.74/1.39  tff(c_718, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_521, c_700])).
% 2.74/1.39  tff(c_921, plain, (![B_86, A_87]: (k1_tarski(B_86)=A_87 | k1_xboole_0=A_87 | ~r1_tarski(A_87, k1_tarski(B_86)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.74/1.39  tff(c_928, plain, (![A_87]: (k1_tarski('#skF_1')=A_87 | k1_xboole_0=A_87 | ~r1_tarski(A_87, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_481, c_921])).
% 2.74/1.39  tff(c_985, plain, (![A_90]: (A_90='#skF_2' | k1_xboole_0=A_90 | ~r1_tarski(A_90, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_481, c_928])).
% 2.74/1.39  tff(c_988, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_718, c_985])).
% 2.74/1.39  tff(c_1000, plain, $false, inference(negUnitSimplification, [status(thm)], [c_480, c_496, c_988])).
% 2.74/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.39  
% 2.74/1.39  Inference rules
% 2.74/1.39  ----------------------
% 2.74/1.39  #Ref     : 0
% 2.74/1.39  #Sup     : 232
% 2.74/1.39  #Fact    : 0
% 2.74/1.39  #Define  : 0
% 2.74/1.39  #Split   : 3
% 2.74/1.39  #Chain   : 0
% 2.74/1.39  #Close   : 0
% 2.74/1.39  
% 2.74/1.39  Ordering : KBO
% 2.74/1.39  
% 2.74/1.39  Simplification rules
% 2.74/1.39  ----------------------
% 2.74/1.39  #Subsume      : 5
% 2.74/1.39  #Demod        : 76
% 2.74/1.39  #Tautology    : 144
% 2.74/1.39  #SimpNegUnit  : 6
% 2.74/1.39  #BackRed      : 2
% 2.74/1.39  
% 2.74/1.39  #Partial instantiations: 0
% 2.74/1.39  #Strategies tried      : 1
% 2.74/1.39  
% 2.74/1.39  Timing (in seconds)
% 2.74/1.39  ----------------------
% 2.74/1.39  Preprocessing        : 0.31
% 2.74/1.39  Parsing              : 0.16
% 2.74/1.39  CNF conversion       : 0.02
% 2.74/1.39  Main loop            : 0.32
% 2.74/1.39  Inferencing          : 0.12
% 2.74/1.40  Reduction            : 0.11
% 2.74/1.40  Demodulation         : 0.08
% 2.74/1.40  BG Simplification    : 0.02
% 2.74/1.40  Subsumption          : 0.05
% 2.74/1.40  Abstraction          : 0.02
% 2.74/1.40  MUC search           : 0.00
% 2.74/1.40  Cooper               : 0.00
% 2.74/1.40  Total                : 0.66
% 2.74/1.40  Index Insertion      : 0.00
% 2.74/1.40  Index Deletion       : 0.00
% 2.74/1.40  Index Matching       : 0.00
% 2.74/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
