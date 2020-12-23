%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:26 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 104 expanded)
%              Number of leaves         :   21 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :   68 ( 127 expanded)
%              Number of equality atoms :   42 (  72 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(A,B)
      <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_43,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_111,plain,(
    ! [A_30,B_31] :
      ( r1_xboole_0(A_30,B_31)
      | k3_xboole_0(A_30,B_31) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_2')
    | r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_37,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_119,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_111,c_37])).

tff(c_20,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_125,plain,(
    k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_24,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_120,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_124,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_120,c_2])).

tff(c_8,plain,(
    ! [A_4,B_5] : r1_tarski(k4_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k2_xboole_0(A_8,k4_xboole_0(B_9,A_8)) = B_9
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_38,plain,(
    ! [A_19,B_20] :
      ( k2_xboole_0(A_19,B_20) = B_20
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_42,plain,(
    ! [A_4,B_5] : k2_xboole_0(k4_xboole_0(A_4,B_5),A_4) = A_4 ),
    inference(resolution,[status(thm)],[c_8,c_38])).

tff(c_14,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_190,plain,(
    ! [A_36,B_37] : k2_xboole_0(A_36,k4_xboole_0(B_37,A_36)) = k2_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_199,plain,(
    ! [A_10,B_11] : k2_xboole_0(k4_xboole_0(A_10,B_11),k3_xboole_0(A_10,B_11)) = k2_xboole_0(k4_xboole_0(A_10,B_11),A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_190])).

tff(c_290,plain,(
    ! [A_46,B_47] : k2_xboole_0(k4_xboole_0(A_46,B_47),k3_xboole_0(A_46,B_47)) = A_46 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_199])).

tff(c_302,plain,(
    k2_xboole_0(k4_xboole_0('#skF_3','#skF_4'),k1_xboole_0) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_290])).

tff(c_6,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_319,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_6])).

tff(c_326,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_319])).

tff(c_327,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_16,plain,(
    ! [A_12,B_13] : r1_xboole_0(k4_xboole_0(A_12,B_13),B_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_84,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(A_25,B_26) = k1_xboole_0
      | ~ r1_xboole_0(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_92,plain,(
    ! [A_12,B_13] : k3_xboole_0(k4_xboole_0(A_12,B_13),B_13) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_84])).

tff(c_332,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_92])).

tff(c_345,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_332])).

tff(c_346,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_355,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_92])).

tff(c_368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_355])).

tff(c_370,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_18,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_2')
    | k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_406,plain,(
    k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_370,c_18])).

tff(c_369,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_372,plain,(
    ! [A_48,B_49] :
      ( k3_xboole_0(A_48,B_49) = k1_xboole_0
      | ~ r1_xboole_0(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_383,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_369,c_372])).

tff(c_407,plain,(
    ! [A_54,B_55] :
      ( k2_xboole_0(A_54,B_55) = B_55
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_411,plain,(
    ! [A_4,B_5] : k2_xboole_0(k4_xboole_0(A_4,B_5),A_4) = A_4 ),
    inference(resolution,[status(thm)],[c_8,c_407])).

tff(c_605,plain,(
    ! [A_71,B_72] : k2_xboole_0(A_71,k4_xboole_0(B_72,A_71)) = k2_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_614,plain,(
    ! [A_10,B_11] : k2_xboole_0(k4_xboole_0(A_10,B_11),k3_xboole_0(A_10,B_11)) = k2_xboole_0(k4_xboole_0(A_10,B_11),A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_605])).

tff(c_650,plain,(
    ! [A_75,B_76] : k2_xboole_0(k4_xboole_0(A_75,B_76),k3_xboole_0(A_75,B_76)) = A_75 ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_614])).

tff(c_671,plain,(
    k2_xboole_0(k4_xboole_0('#skF_3','#skF_4'),k1_xboole_0) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_650])).

tff(c_682,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_671,c_6])).

tff(c_689,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_406,c_682])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:25:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.26  
% 2.20/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.27  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.20/1.27  
% 2.20/1.27  %Foreground sorts:
% 2.20/1.27  
% 2.20/1.27  
% 2.20/1.27  %Background operators:
% 2.20/1.27  
% 2.20/1.27  
% 2.20/1.27  %Foreground operators:
% 2.20/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.20/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.20/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.20/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.20/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.20/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.20/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.20/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.20/1.27  
% 2.20/1.28  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.20/1.28  tff(f_48, negated_conjecture, ~(![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.20/1.28  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.20/1.28  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.20/1.28  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 2.20/1.28  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.20/1.28  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.20/1.28  tff(f_43, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.20/1.28  tff(c_111, plain, (![A_30, B_31]: (r1_xboole_0(A_30, B_31) | k3_xboole_0(A_30, B_31)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.20/1.28  tff(c_22, plain, (~r1_xboole_0('#skF_1', '#skF_2') | r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.20/1.28  tff(c_37, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_22])).
% 2.20/1.28  tff(c_119, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_111, c_37])).
% 2.20/1.28  tff(c_20, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1' | k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.20/1.28  tff(c_125, plain, (k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_20])).
% 2.20/1.28  tff(c_24, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1' | r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.20/1.28  tff(c_120, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_24])).
% 2.20/1.28  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.20/1.28  tff(c_124, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_120, c_2])).
% 2.20/1.28  tff(c_8, plain, (![A_4, B_5]: (r1_tarski(k4_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.20/1.28  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.20/1.28  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k4_xboole_0(B_9, A_8))=B_9 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.20/1.28  tff(c_38, plain, (![A_19, B_20]: (k2_xboole_0(A_19, B_20)=B_20 | ~r1_tarski(A_19, B_20))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 2.20/1.28  tff(c_42, plain, (![A_4, B_5]: (k2_xboole_0(k4_xboole_0(A_4, B_5), A_4)=A_4)), inference(resolution, [status(thm)], [c_8, c_38])).
% 2.20/1.28  tff(c_14, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.20/1.28  tff(c_190, plain, (![A_36, B_37]: (k2_xboole_0(A_36, k4_xboole_0(B_37, A_36))=k2_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.20/1.28  tff(c_199, plain, (![A_10, B_11]: (k2_xboole_0(k4_xboole_0(A_10, B_11), k3_xboole_0(A_10, B_11))=k2_xboole_0(k4_xboole_0(A_10, B_11), A_10))), inference(superposition, [status(thm), theory('equality')], [c_14, c_190])).
% 2.20/1.28  tff(c_290, plain, (![A_46, B_47]: (k2_xboole_0(k4_xboole_0(A_46, B_47), k3_xboole_0(A_46, B_47))=A_46)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_199])).
% 2.20/1.28  tff(c_302, plain, (k2_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), k1_xboole_0)='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_124, c_290])).
% 2.20/1.28  tff(c_6, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.20/1.28  tff(c_319, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_302, c_6])).
% 2.20/1.28  tff(c_326, plain, $false, inference(negUnitSimplification, [status(thm)], [c_125, c_319])).
% 2.20/1.28  tff(c_327, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_20])).
% 2.20/1.28  tff(c_16, plain, (![A_12, B_13]: (r1_xboole_0(k4_xboole_0(A_12, B_13), B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.20/1.28  tff(c_84, plain, (![A_25, B_26]: (k3_xboole_0(A_25, B_26)=k1_xboole_0 | ~r1_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.20/1.28  tff(c_92, plain, (![A_12, B_13]: (k3_xboole_0(k4_xboole_0(A_12, B_13), B_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_84])).
% 2.20/1.28  tff(c_332, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_327, c_92])).
% 2.20/1.28  tff(c_345, plain, $false, inference(negUnitSimplification, [status(thm)], [c_119, c_332])).
% 2.20/1.28  tff(c_346, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_24])).
% 2.20/1.28  tff(c_355, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_346, c_92])).
% 2.20/1.28  tff(c_368, plain, $false, inference(negUnitSimplification, [status(thm)], [c_119, c_355])).
% 2.20/1.28  tff(c_370, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_22])).
% 2.20/1.28  tff(c_18, plain, (~r1_xboole_0('#skF_1', '#skF_2') | k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.20/1.28  tff(c_406, plain, (k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_370, c_18])).
% 2.20/1.28  tff(c_369, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_22])).
% 2.20/1.28  tff(c_372, plain, (![A_48, B_49]: (k3_xboole_0(A_48, B_49)=k1_xboole_0 | ~r1_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.20/1.28  tff(c_383, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_369, c_372])).
% 2.20/1.28  tff(c_407, plain, (![A_54, B_55]: (k2_xboole_0(A_54, B_55)=B_55 | ~r1_tarski(A_54, B_55))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 2.20/1.28  tff(c_411, plain, (![A_4, B_5]: (k2_xboole_0(k4_xboole_0(A_4, B_5), A_4)=A_4)), inference(resolution, [status(thm)], [c_8, c_407])).
% 2.20/1.28  tff(c_605, plain, (![A_71, B_72]: (k2_xboole_0(A_71, k4_xboole_0(B_72, A_71))=k2_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.20/1.28  tff(c_614, plain, (![A_10, B_11]: (k2_xboole_0(k4_xboole_0(A_10, B_11), k3_xboole_0(A_10, B_11))=k2_xboole_0(k4_xboole_0(A_10, B_11), A_10))), inference(superposition, [status(thm), theory('equality')], [c_14, c_605])).
% 2.20/1.28  tff(c_650, plain, (![A_75, B_76]: (k2_xboole_0(k4_xboole_0(A_75, B_76), k3_xboole_0(A_75, B_76))=A_75)), inference(demodulation, [status(thm), theory('equality')], [c_411, c_614])).
% 2.20/1.28  tff(c_671, plain, (k2_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), k1_xboole_0)='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_383, c_650])).
% 2.20/1.28  tff(c_682, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_671, c_6])).
% 2.20/1.28  tff(c_689, plain, $false, inference(negUnitSimplification, [status(thm)], [c_406, c_682])).
% 2.20/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.28  
% 2.20/1.28  Inference rules
% 2.20/1.28  ----------------------
% 2.20/1.28  #Ref     : 0
% 2.20/1.28  #Sup     : 177
% 2.20/1.28  #Fact    : 0
% 2.20/1.28  #Define  : 0
% 2.20/1.28  #Split   : 3
% 2.20/1.28  #Chain   : 0
% 2.20/1.28  #Close   : 0
% 2.20/1.28  
% 2.20/1.28  Ordering : KBO
% 2.20/1.28  
% 2.20/1.28  Simplification rules
% 2.20/1.28  ----------------------
% 2.20/1.28  #Subsume      : 2
% 2.20/1.28  #Demod        : 66
% 2.20/1.28  #Tautology    : 104
% 2.20/1.28  #SimpNegUnit  : 4
% 2.20/1.28  #BackRed      : 0
% 2.20/1.28  
% 2.20/1.28  #Partial instantiations: 0
% 2.20/1.28  #Strategies tried      : 1
% 2.20/1.28  
% 2.20/1.28  Timing (in seconds)
% 2.20/1.28  ----------------------
% 2.20/1.28  Preprocessing        : 0.25
% 2.20/1.29  Parsing              : 0.14
% 2.20/1.29  CNF conversion       : 0.02
% 2.20/1.29  Main loop            : 0.28
% 2.20/1.29  Inferencing          : 0.12
% 2.20/1.29  Reduction            : 0.09
% 2.20/1.29  Demodulation         : 0.07
% 2.20/1.29  BG Simplification    : 0.01
% 2.20/1.29  Subsumption          : 0.04
% 2.20/1.29  Abstraction          : 0.01
% 2.20/1.29  MUC search           : 0.00
% 2.20/1.29  Cooper               : 0.00
% 2.20/1.29  Total                : 0.56
% 2.20/1.29  Index Insertion      : 0.00
% 2.20/1.29  Index Deletion       : 0.00
% 2.20/1.29  Index Matching       : 0.00
% 2.20/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
