%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:29 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 123 expanded)
%              Number of leaves         :   13 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :   61 ( 225 expanded)
%              Number of equality atoms :   58 ( 222 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_zfmisc_1(A,A,A) = k3_zfmisc_1(B,B,B)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_mcart_1)).

tff(f_47,axiom,(
    ! [A,B,C,D,E,F] :
      ( k3_zfmisc_1(A,B,C) = k3_zfmisc_1(D,E,F)
     => ( k3_zfmisc_1(A,B,C) = k1_xboole_0
        | ( A = D
          & B = E
          & C = F ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,A) = k2_zfmisc_1(B,B)
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_zfmisc_1)).

tff(c_18,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_20,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k3_zfmisc_1('#skF_1','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_188,plain,(
    ! [B_33,A_31,C_34,F_30,E_32,D_35] :
      ( E_32 = B_33
      | k3_zfmisc_1(A_31,B_33,C_34) = k1_xboole_0
      | k3_zfmisc_1(D_35,E_32,F_30) != k3_zfmisc_1(A_31,B_33,C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_209,plain,(
    ! [B_33,A_31,C_34] :
      ( B_33 = '#skF_2'
      | k3_zfmisc_1(A_31,B_33,C_34) = k1_xboole_0
      | k3_zfmisc_1(A_31,B_33,C_34) != k3_zfmisc_1('#skF_1','#skF_1','#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_188])).

tff(c_266,plain,
    ( '#skF_2' = '#skF_1'
    | k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(reflexivity,[status(thm),theory(equality)],[c_209])).

tff(c_267,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_266])).

tff(c_92,plain,(
    ! [A_21,B_22,C_23] : k2_zfmisc_1(k2_zfmisc_1(A_21,B_22),C_23) = k3_zfmisc_1(A_21,B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k1_xboole_0 = B_2
      | k1_xboole_0 = A_1
      | k2_zfmisc_1(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_217,plain,(
    ! [C_36,A_37,B_38] :
      ( k1_xboole_0 = C_36
      | k2_zfmisc_1(A_37,B_38) = k1_xboole_0
      | k3_zfmisc_1(A_37,B_38,C_36) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_2])).

tff(c_229,plain,
    ( k1_xboole_0 = '#skF_2'
    | k2_zfmisc_1('#skF_2','#skF_2') = k1_xboole_0
    | k3_zfmisc_1('#skF_1','#skF_1','#skF_1') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_217])).

tff(c_263,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_229])).

tff(c_320,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_263])).

tff(c_321,plain,
    ( k2_zfmisc_1('#skF_2','#skF_2') = k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_229])).

tff(c_394,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_321])).

tff(c_322,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_229])).

tff(c_113,plain,(
    ! [C_23,A_21,B_22] :
      ( k1_xboole_0 = C_23
      | k2_zfmisc_1(A_21,B_22) = k1_xboole_0
      | k3_zfmisc_1(A_21,B_22,C_23) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_2])).

tff(c_336,plain,
    ( k1_xboole_0 = '#skF_1'
    | k2_zfmisc_1('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_113])).

tff(c_578,plain,
    ( '#skF_2' = '#skF_1'
    | k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_394,c_336])).

tff(c_579,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_578])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    ! [B_18,A_19] :
      ( B_18 = A_19
      | k2_zfmisc_1(B_18,B_18) != k2_zfmisc_1(A_19,A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_66,plain,(
    ! [A_19] :
      ( k1_xboole_0 = A_19
      | k2_zfmisc_1(A_19,A_19) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_62])).

tff(c_404,plain,(
    ! [A_19] :
      ( A_19 = '#skF_2'
      | k2_zfmisc_1(A_19,A_19) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_394,c_66])).

tff(c_583,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_579,c_404])).

tff(c_598,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_583])).

tff(c_600,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_321])).

tff(c_599,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_321])).

tff(c_650,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_599,c_66])).

tff(c_668,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_600,c_650])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:13:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.39  
% 2.41/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.39  %$ k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 2.41/1.39  
% 2.41/1.39  %Foreground sorts:
% 2.41/1.39  
% 2.41/1.39  
% 2.41/1.39  %Background operators:
% 2.41/1.39  
% 2.41/1.39  
% 2.41/1.39  %Foreground operators:
% 2.41/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.41/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.41/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.41/1.39  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.41/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.41/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.39  
% 2.41/1.40  tff(f_52, negated_conjecture, ~(![A, B]: ((k3_zfmisc_1(A, A, A) = k3_zfmisc_1(B, B, B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_mcart_1)).
% 2.41/1.40  tff(f_47, axiom, (![A, B, C, D, E, F]: ((k3_zfmisc_1(A, B, C) = k3_zfmisc_1(D, E, F)) => ((k3_zfmisc_1(A, B, C) = k1_xboole_0) | (((A = D) & (B = E)) & (C = F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_mcart_1)).
% 2.41/1.40  tff(f_37, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 2.41/1.40  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.41/1.40  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, A) = k2_zfmisc_1(B, B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_zfmisc_1)).
% 2.41/1.40  tff(c_18, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.41/1.40  tff(c_20, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.41/1.40  tff(c_188, plain, (![B_33, A_31, C_34, F_30, E_32, D_35]: (E_32=B_33 | k3_zfmisc_1(A_31, B_33, C_34)=k1_xboole_0 | k3_zfmisc_1(D_35, E_32, F_30)!=k3_zfmisc_1(A_31, B_33, C_34))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.41/1.40  tff(c_209, plain, (![B_33, A_31, C_34]: (B_33='#skF_2' | k3_zfmisc_1(A_31, B_33, C_34)=k1_xboole_0 | k3_zfmisc_1(A_31, B_33, C_34)!=k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_20, c_188])).
% 2.41/1.40  tff(c_266, plain, ('#skF_2'='#skF_1' | k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(reflexivity, [status(thm), theory('equality')], [c_209])).
% 2.41/1.40  tff(c_267, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_18, c_266])).
% 2.41/1.40  tff(c_92, plain, (![A_21, B_22, C_23]: (k2_zfmisc_1(k2_zfmisc_1(A_21, B_22), C_23)=k3_zfmisc_1(A_21, B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.41/1.40  tff(c_2, plain, (![B_2, A_1]: (k1_xboole_0=B_2 | k1_xboole_0=A_1 | k2_zfmisc_1(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.41/1.40  tff(c_217, plain, (![C_36, A_37, B_38]: (k1_xboole_0=C_36 | k2_zfmisc_1(A_37, B_38)=k1_xboole_0 | k3_zfmisc_1(A_37, B_38, C_36)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_92, c_2])).
% 2.41/1.40  tff(c_229, plain, (k1_xboole_0='#skF_2' | k2_zfmisc_1('#skF_2', '#skF_2')=k1_xboole_0 | k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_20, c_217])).
% 2.41/1.40  tff(c_263, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_229])).
% 2.41/1.40  tff(c_320, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_267, c_263])).
% 2.41/1.40  tff(c_321, plain, (k2_zfmisc_1('#skF_2', '#skF_2')=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_229])).
% 2.41/1.40  tff(c_394, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_321])).
% 2.41/1.40  tff(c_322, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_229])).
% 2.41/1.40  tff(c_113, plain, (![C_23, A_21, B_22]: (k1_xboole_0=C_23 | k2_zfmisc_1(A_21, B_22)=k1_xboole_0 | k3_zfmisc_1(A_21, B_22, C_23)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_92, c_2])).
% 2.41/1.40  tff(c_336, plain, (k1_xboole_0='#skF_1' | k2_zfmisc_1('#skF_1', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_322, c_113])).
% 2.41/1.40  tff(c_578, plain, ('#skF_2'='#skF_1' | k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_394, c_394, c_336])).
% 2.41/1.40  tff(c_579, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_18, c_578])).
% 2.41/1.40  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.41/1.40  tff(c_62, plain, (![B_18, A_19]: (B_18=A_19 | k2_zfmisc_1(B_18, B_18)!=k2_zfmisc_1(A_19, A_19))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.41/1.40  tff(c_66, plain, (![A_19]: (k1_xboole_0=A_19 | k2_zfmisc_1(A_19, A_19)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_62])).
% 2.41/1.40  tff(c_404, plain, (![A_19]: (A_19='#skF_2' | k2_zfmisc_1(A_19, A_19)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_394, c_394, c_66])).
% 2.41/1.40  tff(c_583, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_579, c_404])).
% 2.41/1.40  tff(c_598, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_583])).
% 2.41/1.40  tff(c_600, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_321])).
% 2.41/1.40  tff(c_599, plain, (k2_zfmisc_1('#skF_2', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_321])).
% 2.41/1.40  tff(c_650, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_599, c_66])).
% 2.41/1.40  tff(c_668, plain, $false, inference(negUnitSimplification, [status(thm)], [c_600, c_650])).
% 2.41/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.40  
% 2.41/1.40  Inference rules
% 2.41/1.40  ----------------------
% 2.41/1.40  #Ref     : 7
% 2.41/1.40  #Sup     : 156
% 2.41/1.40  #Fact    : 0
% 2.41/1.40  #Define  : 0
% 2.41/1.40  #Split   : 2
% 2.41/1.40  #Chain   : 0
% 2.41/1.40  #Close   : 0
% 2.41/1.40  
% 2.41/1.40  Ordering : KBO
% 2.41/1.40  
% 2.41/1.40  Simplification rules
% 2.41/1.40  ----------------------
% 2.41/1.40  #Subsume      : 3
% 2.41/1.40  #Demod        : 83
% 2.41/1.40  #Tautology    : 128
% 2.41/1.40  #SimpNegUnit  : 5
% 2.41/1.40  #BackRed      : 15
% 2.41/1.40  
% 2.41/1.40  #Partial instantiations: 0
% 2.41/1.40  #Strategies tried      : 1
% 2.41/1.40  
% 2.41/1.40  Timing (in seconds)
% 2.41/1.40  ----------------------
% 2.41/1.41  Preprocessing        : 0.30
% 2.41/1.41  Parsing              : 0.16
% 2.41/1.41  CNF conversion       : 0.02
% 2.41/1.41  Main loop            : 0.29
% 2.41/1.41  Inferencing          : 0.10
% 2.41/1.41  Reduction            : 0.08
% 2.41/1.41  Demodulation         : 0.06
% 2.41/1.41  BG Simplification    : 0.02
% 2.41/1.41  Subsumption          : 0.07
% 2.41/1.41  Abstraction          : 0.02
% 2.41/1.41  MUC search           : 0.00
% 2.41/1.41  Cooper               : 0.00
% 2.41/1.41  Total                : 0.62
% 2.41/1.41  Index Insertion      : 0.00
% 2.41/1.41  Index Deletion       : 0.00
% 2.41/1.41  Index Matching       : 0.00
% 2.41/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
