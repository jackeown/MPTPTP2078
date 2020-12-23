%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:26 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   65 (  92 expanded)
%              Number of leaves         :   21 (  38 expanded)
%              Depth                    :    6
%              Number of atoms          :   65 ( 109 expanded)
%              Number of equality atoms :   39 (  59 expanded)
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

tff(f_48,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(A,B)
      <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_43,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_22,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_2')
    | r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_36,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_49,plain,(
    ! [A_23,B_24] :
      ( r1_xboole_0(A_23,B_24)
      | k3_xboole_0(A_23,B_24) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_57,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_49,c_36])).

tff(c_20,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_89,plain,(
    k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_24,plain,
    ( k4_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_58,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_62,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_2])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_67,plain,(
    ! [A_25,B_26] :
      ( k2_xboole_0(A_25,B_26) = B_26
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_71,plain,(
    ! [A_6,B_7] : k2_xboole_0(k4_xboole_0(A_6,B_7),A_6) = A_6 ),
    inference(resolution,[status(thm)],[c_10,c_67])).

tff(c_14,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_169,plain,(
    ! [A_34,B_35] : k2_xboole_0(A_34,k4_xboole_0(B_35,A_34)) = k2_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_178,plain,(
    ! [A_10,B_11] : k2_xboole_0(k4_xboole_0(A_10,B_11),k3_xboole_0(A_10,B_11)) = k2_xboole_0(k4_xboole_0(A_10,B_11),A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_169])).

tff(c_290,plain,(
    ! [A_46,B_47] : k2_xboole_0(k4_xboole_0(A_46,B_47),k3_xboole_0(A_46,B_47)) = A_46 ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_178])).

tff(c_308,plain,(
    k2_xboole_0(k4_xboole_0('#skF_3','#skF_4'),k1_xboole_0) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_290])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_319,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_8])).

tff(c_326,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_319])).

tff(c_327,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_16,plain,(
    ! [A_12,B_13] : r1_xboole_0(k4_xboole_0(A_12,B_13),B_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_37,plain,(
    ! [A_19,B_20] :
      ( k3_xboole_0(A_19,B_20) = k1_xboole_0
      | ~ r1_xboole_0(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_41,plain,(
    ! [A_12,B_13] : k3_xboole_0(k4_xboole_0(A_12,B_13),B_13) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_37])).

tff(c_335,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_41])).

tff(c_345,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_335])).

tff(c_346,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_362,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_16])).

tff(c_366,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_362])).

tff(c_368,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_18,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_2')
    | k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_370,plain,(
    k4_xboole_0('#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_18])).

tff(c_367,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_371,plain,(
    ! [A_48,B_49] :
      ( k3_xboole_0(A_48,B_49) = k1_xboole_0
      | ~ r1_xboole_0(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_382,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_367,c_371])).

tff(c_400,plain,(
    ! [A_52,B_53] :
      ( k2_xboole_0(A_52,B_53) = B_53
      | ~ r1_tarski(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_404,plain,(
    ! [A_6,B_7] : k2_xboole_0(k4_xboole_0(A_6,B_7),A_6) = A_6 ),
    inference(resolution,[status(thm)],[c_10,c_400])).

tff(c_533,plain,(
    ! [A_65,B_66] : k2_xboole_0(A_65,k4_xboole_0(B_66,A_65)) = k2_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_542,plain,(
    ! [A_10,B_11] : k2_xboole_0(k4_xboole_0(A_10,B_11),k3_xboole_0(A_10,B_11)) = k2_xboole_0(k4_xboole_0(A_10,B_11),A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_533])).

tff(c_648,plain,(
    ! [A_75,B_76] : k2_xboole_0(k4_xboole_0(A_75,B_76),k3_xboole_0(A_75,B_76)) = A_75 ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_542])).

tff(c_669,plain,(
    k2_xboole_0(k4_xboole_0('#skF_3','#skF_4'),k1_xboole_0) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_648])).

tff(c_680,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_669,c_8])).

tff(c_687,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_370,c_680])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:04:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.31  
% 2.34/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.31  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.34/1.31  
% 2.34/1.31  %Foreground sorts:
% 2.34/1.31  
% 2.34/1.31  
% 2.34/1.31  %Background operators:
% 2.34/1.31  
% 2.34/1.31  
% 2.34/1.31  %Foreground operators:
% 2.34/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.34/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.34/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.34/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.34/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.34/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.34/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.34/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.34/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.34/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.34/1.31  
% 2.34/1.32  tff(f_48, negated_conjecture, ~(![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.34/1.32  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.34/1.32  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.34/1.32  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.34/1.32  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.34/1.32  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.34/1.32  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.34/1.32  tff(f_43, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.34/1.32  tff(c_22, plain, (~r1_xboole_0('#skF_1', '#skF_2') | r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.34/1.32  tff(c_36, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_22])).
% 2.34/1.32  tff(c_49, plain, (![A_23, B_24]: (r1_xboole_0(A_23, B_24) | k3_xboole_0(A_23, B_24)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.34/1.32  tff(c_57, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_49, c_36])).
% 2.34/1.32  tff(c_20, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1' | k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.34/1.32  tff(c_89, plain, (k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(splitLeft, [status(thm)], [c_20])).
% 2.34/1.32  tff(c_24, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1' | r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.34/1.32  tff(c_58, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_24])).
% 2.34/1.32  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.34/1.32  tff(c_62, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_2])).
% 2.34/1.32  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.34/1.32  tff(c_67, plain, (![A_25, B_26]: (k2_xboole_0(A_25, B_26)=B_26 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.34/1.32  tff(c_71, plain, (![A_6, B_7]: (k2_xboole_0(k4_xboole_0(A_6, B_7), A_6)=A_6)), inference(resolution, [status(thm)], [c_10, c_67])).
% 2.34/1.32  tff(c_14, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.34/1.32  tff(c_169, plain, (![A_34, B_35]: (k2_xboole_0(A_34, k4_xboole_0(B_35, A_34))=k2_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.34/1.32  tff(c_178, plain, (![A_10, B_11]: (k2_xboole_0(k4_xboole_0(A_10, B_11), k3_xboole_0(A_10, B_11))=k2_xboole_0(k4_xboole_0(A_10, B_11), A_10))), inference(superposition, [status(thm), theory('equality')], [c_14, c_169])).
% 2.34/1.32  tff(c_290, plain, (![A_46, B_47]: (k2_xboole_0(k4_xboole_0(A_46, B_47), k3_xboole_0(A_46, B_47))=A_46)), inference(demodulation, [status(thm), theory('equality')], [c_71, c_178])).
% 2.34/1.32  tff(c_308, plain, (k2_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), k1_xboole_0)='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_62, c_290])).
% 2.34/1.32  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.34/1.32  tff(c_319, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_308, c_8])).
% 2.34/1.32  tff(c_326, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_319])).
% 2.34/1.32  tff(c_327, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_20])).
% 2.34/1.32  tff(c_16, plain, (![A_12, B_13]: (r1_xboole_0(k4_xboole_0(A_12, B_13), B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.34/1.32  tff(c_37, plain, (![A_19, B_20]: (k3_xboole_0(A_19, B_20)=k1_xboole_0 | ~r1_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.34/1.32  tff(c_41, plain, (![A_12, B_13]: (k3_xboole_0(k4_xboole_0(A_12, B_13), B_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_37])).
% 2.34/1.32  tff(c_335, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_327, c_41])).
% 2.34/1.32  tff(c_345, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_335])).
% 2.34/1.32  tff(c_346, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_24])).
% 2.34/1.32  tff(c_362, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_346, c_16])).
% 2.34/1.32  tff(c_366, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_362])).
% 2.34/1.32  tff(c_368, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_22])).
% 2.34/1.32  tff(c_18, plain, (~r1_xboole_0('#skF_1', '#skF_2') | k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.34/1.32  tff(c_370, plain, (k4_xboole_0('#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_368, c_18])).
% 2.34/1.32  tff(c_367, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_22])).
% 2.34/1.32  tff(c_371, plain, (![A_48, B_49]: (k3_xboole_0(A_48, B_49)=k1_xboole_0 | ~r1_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.34/1.32  tff(c_382, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_367, c_371])).
% 2.34/1.32  tff(c_400, plain, (![A_52, B_53]: (k2_xboole_0(A_52, B_53)=B_53 | ~r1_tarski(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.34/1.32  tff(c_404, plain, (![A_6, B_7]: (k2_xboole_0(k4_xboole_0(A_6, B_7), A_6)=A_6)), inference(resolution, [status(thm)], [c_10, c_400])).
% 2.34/1.32  tff(c_533, plain, (![A_65, B_66]: (k2_xboole_0(A_65, k4_xboole_0(B_66, A_65))=k2_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.34/1.32  tff(c_542, plain, (![A_10, B_11]: (k2_xboole_0(k4_xboole_0(A_10, B_11), k3_xboole_0(A_10, B_11))=k2_xboole_0(k4_xboole_0(A_10, B_11), A_10))), inference(superposition, [status(thm), theory('equality')], [c_14, c_533])).
% 2.34/1.32  tff(c_648, plain, (![A_75, B_76]: (k2_xboole_0(k4_xboole_0(A_75, B_76), k3_xboole_0(A_75, B_76))=A_75)), inference(demodulation, [status(thm), theory('equality')], [c_404, c_542])).
% 2.34/1.32  tff(c_669, plain, (k2_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), k1_xboole_0)='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_382, c_648])).
% 2.34/1.32  tff(c_680, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_669, c_8])).
% 2.34/1.32  tff(c_687, plain, $false, inference(negUnitSimplification, [status(thm)], [c_370, c_680])).
% 2.34/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.32  
% 2.34/1.32  Inference rules
% 2.34/1.32  ----------------------
% 2.34/1.32  #Ref     : 0
% 2.34/1.32  #Sup     : 176
% 2.34/1.32  #Fact    : 0
% 2.34/1.32  #Define  : 0
% 2.34/1.32  #Split   : 4
% 2.34/1.32  #Chain   : 0
% 2.34/1.32  #Close   : 0
% 2.34/1.32  
% 2.34/1.32  Ordering : KBO
% 2.34/1.32  
% 2.34/1.32  Simplification rules
% 2.34/1.32  ----------------------
% 2.34/1.32  #Subsume      : 2
% 2.34/1.32  #Demod        : 65
% 2.34/1.32  #Tautology    : 104
% 2.34/1.32  #SimpNegUnit  : 4
% 2.34/1.32  #BackRed      : 0
% 2.34/1.32  
% 2.34/1.32  #Partial instantiations: 0
% 2.34/1.32  #Strategies tried      : 1
% 2.34/1.32  
% 2.34/1.32  Timing (in seconds)
% 2.34/1.32  ----------------------
% 2.34/1.33  Preprocessing        : 0.26
% 2.34/1.33  Parsing              : 0.15
% 2.34/1.33  CNF conversion       : 0.02
% 2.34/1.33  Main loop            : 0.28
% 2.34/1.33  Inferencing          : 0.12
% 2.34/1.33  Reduction            : 0.09
% 2.34/1.33  Demodulation         : 0.06
% 2.34/1.33  BG Simplification    : 0.01
% 2.34/1.33  Subsumption          : 0.04
% 2.34/1.33  Abstraction          : 0.01
% 2.34/1.33  MUC search           : 0.00
% 2.34/1.33  Cooper               : 0.00
% 2.34/1.33  Total                : 0.58
% 2.34/1.33  Index Insertion      : 0.00
% 2.34/1.33  Index Deletion       : 0.00
% 2.34/1.33  Index Matching       : 0.00
% 2.34/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
