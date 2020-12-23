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
% DateTime   : Thu Dec  3 09:44:27 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   55 (  79 expanded)
%              Number of leaves         :   20 (  34 expanded)
%              Depth                    :    6
%              Number of atoms          :   55 (  99 expanded)
%              Number of equality atoms :   24 (  42 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(A,B)
      <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_20,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | r1_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_37,plain,(
    ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_18,plain,
    ( k4_xboole_0('#skF_3','#skF_4') = '#skF_3'
    | k4_xboole_0('#skF_5','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_40,plain,(
    k4_xboole_0('#skF_5','#skF_6') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_8,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_22,plain,
    ( k4_xboole_0('#skF_3','#skF_4') = '#skF_3'
    | r1_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_39,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_6,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_90,plain,(
    ! [A_23,B_24,C_25] :
      ( ~ r1_xboole_0(A_23,B_24)
      | ~ r2_hidden(C_25,k3_xboole_0(A_23,B_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_113,plain,(
    ! [A_28,B_29] :
      ( ~ r1_xboole_0(A_28,B_29)
      | k3_xboole_0(A_28,B_29) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_90])).

tff(c_127,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_39,c_113])).

tff(c_236,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k3_xboole_0(A_35,B_36)) = k4_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_260,plain,(
    k4_xboole_0('#skF_5',k1_xboole_0) = k4_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_236])).

tff(c_267,plain,(
    k4_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_260])).

tff(c_269,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_267])).

tff(c_270,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_14,plain,(
    ! [A_13,B_14] : r1_xboole_0(k4_xboole_0(A_13,B_14),B_14) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_275,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_14])).

tff(c_279,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_275])).

tff(c_280,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_285,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_14])).

tff(c_289,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_285])).

tff(c_291,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_16,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | k4_xboole_0('#skF_5','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_292,plain,(
    k4_xboole_0('#skF_5','#skF_6') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_290,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_295,plain,(
    ! [A_38,B_39,C_40] :
      ( ~ r1_xboole_0(A_38,B_39)
      | ~ r2_hidden(C_40,k3_xboole_0(A_38,B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_301,plain,(
    ! [A_41,B_42] :
      ( ~ r1_xboole_0(A_41,B_42)
      | k3_xboole_0(A_41,B_42) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_295])).

tff(c_315,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_290,c_301])).

tff(c_379,plain,(
    ! [A_47,B_48] : k4_xboole_0(A_47,k3_xboole_0(A_47,B_48)) = k4_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_400,plain,(
    k4_xboole_0('#skF_5',k1_xboole_0) = k4_xboole_0('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_379])).

tff(c_408,plain,(
    k4_xboole_0('#skF_5','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_400])).

tff(c_410,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_292,c_408])).

tff(c_411,plain,(
    ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_414,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_411])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 11:19:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.22  
% 1.96/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.22  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 1.96/1.22  
% 1.96/1.22  %Foreground sorts:
% 1.96/1.22  
% 1.96/1.22  
% 1.96/1.22  %Background operators:
% 1.96/1.22  
% 1.96/1.22  
% 1.96/1.22  %Foreground operators:
% 1.96/1.22  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.96/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.96/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.96/1.22  tff('#skF_5', type, '#skF_5': $i).
% 1.96/1.22  tff('#skF_6', type, '#skF_6': $i).
% 1.96/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.96/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.96/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.96/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.96/1.22  
% 1.96/1.23  tff(f_60, negated_conjecture, ~(![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.96/1.23  tff(f_49, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.96/1.23  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.96/1.23  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.96/1.23  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 1.96/1.23  tff(f_55, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 1.96/1.23  tff(c_20, plain, (~r1_xboole_0('#skF_3', '#skF_4') | r1_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.96/1.23  tff(c_37, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_20])).
% 1.96/1.23  tff(c_18, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3' | k4_xboole_0('#skF_5', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.96/1.23  tff(c_40, plain, (k4_xboole_0('#skF_5', '#skF_6')!='#skF_5'), inference(splitLeft, [status(thm)], [c_18])).
% 1.96/1.23  tff(c_8, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.96/1.23  tff(c_22, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3' | r1_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.96/1.23  tff(c_39, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_22])).
% 1.96/1.23  tff(c_6, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.96/1.23  tff(c_90, plain, (![A_23, B_24, C_25]: (~r1_xboole_0(A_23, B_24) | ~r2_hidden(C_25, k3_xboole_0(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.96/1.23  tff(c_113, plain, (![A_28, B_29]: (~r1_xboole_0(A_28, B_29) | k3_xboole_0(A_28, B_29)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_90])).
% 1.96/1.23  tff(c_127, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_39, c_113])).
% 1.96/1.23  tff(c_236, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k3_xboole_0(A_35, B_36))=k4_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.96/1.23  tff(c_260, plain, (k4_xboole_0('#skF_5', k1_xboole_0)=k4_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_127, c_236])).
% 1.96/1.23  tff(c_267, plain, (k4_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_260])).
% 1.96/1.23  tff(c_269, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_267])).
% 1.96/1.23  tff(c_270, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_18])).
% 2.05/1.23  tff(c_14, plain, (![A_13, B_14]: (r1_xboole_0(k4_xboole_0(A_13, B_14), B_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.05/1.23  tff(c_275, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_270, c_14])).
% 2.05/1.23  tff(c_279, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37, c_275])).
% 2.05/1.23  tff(c_280, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_22])).
% 2.05/1.23  tff(c_285, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_280, c_14])).
% 2.05/1.23  tff(c_289, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37, c_285])).
% 2.05/1.23  tff(c_291, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_20])).
% 2.05/1.23  tff(c_16, plain, (~r1_xboole_0('#skF_3', '#skF_4') | k4_xboole_0('#skF_5', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.05/1.23  tff(c_292, plain, (k4_xboole_0('#skF_5', '#skF_6')!='#skF_5'), inference(splitLeft, [status(thm)], [c_16])).
% 2.05/1.23  tff(c_290, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_20])).
% 2.05/1.23  tff(c_295, plain, (![A_38, B_39, C_40]: (~r1_xboole_0(A_38, B_39) | ~r2_hidden(C_40, k3_xboole_0(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.05/1.23  tff(c_301, plain, (![A_41, B_42]: (~r1_xboole_0(A_41, B_42) | k3_xboole_0(A_41, B_42)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_295])).
% 2.05/1.23  tff(c_315, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_290, c_301])).
% 2.05/1.23  tff(c_379, plain, (![A_47, B_48]: (k4_xboole_0(A_47, k3_xboole_0(A_47, B_48))=k4_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.05/1.23  tff(c_400, plain, (k4_xboole_0('#skF_5', k1_xboole_0)=k4_xboole_0('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_315, c_379])).
% 2.05/1.23  tff(c_408, plain, (k4_xboole_0('#skF_5', '#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_400])).
% 2.05/1.23  tff(c_410, plain, $false, inference(negUnitSimplification, [status(thm)], [c_292, c_408])).
% 2.05/1.23  tff(c_411, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_16])).
% 2.05/1.23  tff(c_414, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_291, c_411])).
% 2.05/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.23  
% 2.05/1.23  Inference rules
% 2.05/1.23  ----------------------
% 2.05/1.23  #Ref     : 0
% 2.05/1.23  #Sup     : 93
% 2.05/1.23  #Fact    : 0
% 2.05/1.23  #Define  : 0
% 2.05/1.23  #Split   : 4
% 2.05/1.23  #Chain   : 0
% 2.05/1.23  #Close   : 0
% 2.05/1.23  
% 2.05/1.23  Ordering : KBO
% 2.05/1.23  
% 2.05/1.23  Simplification rules
% 2.05/1.23  ----------------------
% 2.05/1.23  #Subsume      : 8
% 2.05/1.23  #Demod        : 29
% 2.05/1.23  #Tautology    : 53
% 2.05/1.23  #SimpNegUnit  : 4
% 2.05/1.23  #BackRed      : 2
% 2.05/1.23  
% 2.05/1.23  #Partial instantiations: 0
% 2.05/1.23  #Strategies tried      : 1
% 2.05/1.23  
% 2.05/1.23  Timing (in seconds)
% 2.05/1.23  ----------------------
% 2.05/1.23  Preprocessing        : 0.26
% 2.05/1.24  Parsing              : 0.14
% 2.05/1.24  CNF conversion       : 0.02
% 2.05/1.24  Main loop            : 0.20
% 2.05/1.24  Inferencing          : 0.08
% 2.05/1.24  Reduction            : 0.06
% 2.05/1.24  Demodulation         : 0.04
% 2.05/1.24  BG Simplification    : 0.01
% 2.05/1.24  Subsumption          : 0.02
% 2.05/1.24  Abstraction          : 0.01
% 2.05/1.24  MUC search           : 0.00
% 2.05/1.24  Cooper               : 0.00
% 2.05/1.24  Total                : 0.49
% 2.05/1.24  Index Insertion      : 0.00
% 2.05/1.24  Index Deletion       : 0.00
% 2.05/1.24  Index Matching       : 0.00
% 2.05/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
