%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:26 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 128 expanded)
%              Number of leaves         :   18 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :   65 ( 210 expanded)
%              Number of equality atoms :   37 ( 113 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( ~ ( ~ r1_xboole_0(A,A)
            & A = k1_xboole_0 )
        & ~ ( A != k1_xboole_0
            & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_53,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_57,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_18,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_10,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_362,plain,(
    ! [A_46,B_47,C_48] :
      ( ~ r1_xboole_0(A_46,B_47)
      | ~ r2_hidden(C_48,k3_xboole_0(A_46,B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_380,plain,(
    ! [A_50,B_51] :
      ( ~ r1_xboole_0(A_50,B_51)
      | k3_xboole_0(A_50,B_51) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_362])).

tff(c_392,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_380])).

tff(c_319,plain,(
    ! [A_43,B_44] : k4_xboole_0(A_43,k4_xboole_0(A_43,B_44)) = k3_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_334,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k3_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_319])).

tff(c_427,plain,(
    ! [A_54] : k4_xboole_0(A_54,A_54) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_334])).

tff(c_12,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_432,plain,(
    ! [A_54] : k4_xboole_0(A_54,k1_xboole_0) = k3_xboole_0(A_54,A_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_427,c_12])).

tff(c_444,plain,(
    ! [A_54] : k3_xboole_0(A_54,A_54) = A_54 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_432])).

tff(c_16,plain,
    ( r1_xboole_0('#skF_3','#skF_3')
    | k1_xboole_0 = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_34,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_36,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_24])).

tff(c_35,plain,(
    ! [A_10] : k4_xboole_0(A_10,'#skF_4') = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_10])).

tff(c_37,plain,(
    ! [A_13] : r1_xboole_0(A_13,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_14])).

tff(c_63,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | A_8 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_8])).

tff(c_89,plain,(
    ! [A_24,B_25,C_26] :
      ( ~ r1_xboole_0(A_24,B_25)
      | ~ r2_hidden(C_26,k3_xboole_0(A_24,B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_142,plain,(
    ! [A_31,B_32] :
      ( ~ r1_xboole_0(A_31,B_32)
      | k3_xboole_0(A_31,B_32) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_63,c_89])).

tff(c_154,plain,(
    ! [A_13] : k3_xboole_0(A_13,'#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_37,c_142])).

tff(c_71,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k4_xboole_0(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_213,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k3_xboole_0(A_35,B_36)) = k3_xboole_0(A_35,k4_xboole_0(A_35,B_36)) ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_12])).

tff(c_225,plain,(
    ! [A_13] : k3_xboole_0(A_13,k4_xboole_0(A_13,'#skF_4')) = k4_xboole_0(A_13,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_213])).

tff(c_258,plain,(
    ! [A_38] : k3_xboole_0(A_38,A_38) = A_38 ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_35,c_225])).

tff(c_20,plain,
    ( r1_xboole_0('#skF_3','#skF_3')
    | ~ r1_xboole_0('#skF_4','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_66,plain,(
    r1_xboole_0('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_20])).

tff(c_152,plain,(
    k3_xboole_0('#skF_3','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_66,c_142])).

tff(c_275,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_152])).

tff(c_301,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_275])).

tff(c_302,plain,(
    r1_xboole_0('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_391,plain,(
    k3_xboole_0('#skF_3','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_302,c_380])).

tff(c_477,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_444,c_391])).

tff(c_479,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_477])).

tff(c_480,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_482,plain,(
    ! [A_13] : r1_xboole_0(A_13,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_14])).

tff(c_481,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_488,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_481])).

tff(c_22,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ r1_xboole_0('#skF_4','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_505,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_482,c_488,c_480,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:01:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.30  
% 2.01/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.30  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.01/1.30  
% 2.01/1.30  %Foreground sorts:
% 2.01/1.30  
% 2.01/1.30  
% 2.01/1.30  %Background operators:
% 2.01/1.30  
% 2.01/1.30  
% 2.01/1.30  %Foreground operators:
% 2.01/1.30  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.01/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.01/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.01/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.01/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.01/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.01/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.01/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.01/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.01/1.30  
% 2.01/1.32  tff(f_70, negated_conjecture, ~(![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.01/1.32  tff(f_53, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.01/1.32  tff(f_57, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.01/1.32  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.01/1.32  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.01/1.32  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.01/1.32  tff(c_18, plain, (k1_xboole_0!='#skF_3' | k1_xboole_0='#skF_4'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.01/1.32  tff(c_24, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_18])).
% 2.01/1.32  tff(c_10, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.01/1.32  tff(c_14, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.01/1.32  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.01/1.32  tff(c_362, plain, (![A_46, B_47, C_48]: (~r1_xboole_0(A_46, B_47) | ~r2_hidden(C_48, k3_xboole_0(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.01/1.32  tff(c_380, plain, (![A_50, B_51]: (~r1_xboole_0(A_50, B_51) | k3_xboole_0(A_50, B_51)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_362])).
% 2.01/1.32  tff(c_392, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_380])).
% 2.01/1.32  tff(c_319, plain, (![A_43, B_44]: (k4_xboole_0(A_43, k4_xboole_0(A_43, B_44))=k3_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.01/1.32  tff(c_334, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k3_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_319])).
% 2.01/1.32  tff(c_427, plain, (![A_54]: (k4_xboole_0(A_54, A_54)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_392, c_334])).
% 2.01/1.32  tff(c_12, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.01/1.32  tff(c_432, plain, (![A_54]: (k4_xboole_0(A_54, k1_xboole_0)=k3_xboole_0(A_54, A_54))), inference(superposition, [status(thm), theory('equality')], [c_427, c_12])).
% 2.01/1.32  tff(c_444, plain, (![A_54]: (k3_xboole_0(A_54, A_54)=A_54)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_432])).
% 2.01/1.32  tff(c_16, plain, (r1_xboole_0('#skF_3', '#skF_3') | k1_xboole_0='#skF_4'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.01/1.32  tff(c_34, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_16])).
% 2.01/1.32  tff(c_36, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_24])).
% 2.01/1.32  tff(c_35, plain, (![A_10]: (k4_xboole_0(A_10, '#skF_4')=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_10])).
% 2.01/1.32  tff(c_37, plain, (![A_13]: (r1_xboole_0(A_13, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_14])).
% 2.01/1.32  tff(c_63, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | A_8='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_8])).
% 2.01/1.32  tff(c_89, plain, (![A_24, B_25, C_26]: (~r1_xboole_0(A_24, B_25) | ~r2_hidden(C_26, k3_xboole_0(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.01/1.32  tff(c_142, plain, (![A_31, B_32]: (~r1_xboole_0(A_31, B_32) | k3_xboole_0(A_31, B_32)='#skF_4')), inference(resolution, [status(thm)], [c_63, c_89])).
% 2.01/1.32  tff(c_154, plain, (![A_13]: (k3_xboole_0(A_13, '#skF_4')='#skF_4')), inference(resolution, [status(thm)], [c_37, c_142])).
% 2.01/1.32  tff(c_71, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k4_xboole_0(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.01/1.32  tff(c_213, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k3_xboole_0(A_35, B_36))=k3_xboole_0(A_35, k4_xboole_0(A_35, B_36)))), inference(superposition, [status(thm), theory('equality')], [c_71, c_12])).
% 2.01/1.32  tff(c_225, plain, (![A_13]: (k3_xboole_0(A_13, k4_xboole_0(A_13, '#skF_4'))=k4_xboole_0(A_13, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_154, c_213])).
% 2.01/1.32  tff(c_258, plain, (![A_38]: (k3_xboole_0(A_38, A_38)=A_38)), inference(demodulation, [status(thm), theory('equality')], [c_35, c_35, c_225])).
% 2.01/1.32  tff(c_20, plain, (r1_xboole_0('#skF_3', '#skF_3') | ~r1_xboole_0('#skF_4', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.01/1.32  tff(c_66, plain, (r1_xboole_0('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_37, c_20])).
% 2.01/1.32  tff(c_152, plain, (k3_xboole_0('#skF_3', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_66, c_142])).
% 2.01/1.32  tff(c_275, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_258, c_152])).
% 2.01/1.32  tff(c_301, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_275])).
% 2.01/1.32  tff(c_302, plain, (r1_xboole_0('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_16])).
% 2.01/1.32  tff(c_391, plain, (k3_xboole_0('#skF_3', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_302, c_380])).
% 2.01/1.32  tff(c_477, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_444, c_391])).
% 2.01/1.32  tff(c_479, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_477])).
% 2.01/1.32  tff(c_480, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_18])).
% 2.01/1.32  tff(c_482, plain, (![A_13]: (r1_xboole_0(A_13, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_480, c_14])).
% 2.01/1.32  tff(c_481, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_18])).
% 2.01/1.32  tff(c_488, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_480, c_481])).
% 2.01/1.32  tff(c_22, plain, (k1_xboole_0!='#skF_3' | ~r1_xboole_0('#skF_4', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.01/1.32  tff(c_505, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_482, c_488, c_480, c_22])).
% 2.01/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.32  
% 2.01/1.32  Inference rules
% 2.01/1.32  ----------------------
% 2.01/1.32  #Ref     : 0
% 2.01/1.32  #Sup     : 112
% 2.01/1.32  #Fact    : 0
% 2.01/1.32  #Define  : 0
% 2.01/1.32  #Split   : 2
% 2.01/1.32  #Chain   : 0
% 2.01/1.32  #Close   : 0
% 2.01/1.32  
% 2.01/1.32  Ordering : KBO
% 2.01/1.32  
% 2.01/1.32  Simplification rules
% 2.01/1.32  ----------------------
% 2.01/1.32  #Subsume      : 8
% 2.01/1.32  #Demod        : 51
% 2.01/1.32  #Tautology    : 76
% 2.01/1.32  #SimpNegUnit  : 9
% 2.01/1.32  #BackRed      : 7
% 2.01/1.32  
% 2.01/1.32  #Partial instantiations: 0
% 2.01/1.32  #Strategies tried      : 1
% 2.01/1.32  
% 2.01/1.32  Timing (in seconds)
% 2.01/1.32  ----------------------
% 2.01/1.32  Preprocessing        : 0.31
% 2.01/1.32  Parsing              : 0.16
% 2.01/1.32  CNF conversion       : 0.02
% 2.01/1.32  Main loop            : 0.21
% 2.01/1.32  Inferencing          : 0.08
% 2.01/1.32  Reduction            : 0.06
% 2.01/1.32  Demodulation         : 0.05
% 2.01/1.32  BG Simplification    : 0.01
% 2.01/1.32  Subsumption          : 0.03
% 2.01/1.32  Abstraction          : 0.01
% 2.01/1.32  MUC search           : 0.00
% 2.01/1.32  Cooper               : 0.00
% 2.01/1.32  Total                : 0.55
% 2.01/1.32  Index Insertion      : 0.00
% 2.01/1.32  Index Deletion       : 0.00
% 2.01/1.32  Index Matching       : 0.00
% 2.01/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
