%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:43 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   60 (  79 expanded)
%              Number of leaves         :   23 (  36 expanded)
%              Depth                    :    6
%              Number of atoms          :   66 ( 100 expanded)
%              Number of equality atoms :   22 (  32 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_28,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_43,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_238,plain,(
    ! [A_56,B_57] :
      ( k4_xboole_0(k1_tarski(A_56),B_57) = k1_tarski(A_56)
      | r2_hidden(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_xboole_0(k4_xboole_0(A_7,B_8),B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_61,plain,(
    ! [A_29,B_30] :
      ( k3_xboole_0(A_29,B_30) = k1_xboole_0
      | ~ r1_xboole_0(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_77,plain,(
    ! [A_7,B_8] : k3_xboole_0(k4_xboole_0(A_7,B_8),B_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_61])).

tff(c_261,plain,(
    ! [A_56,B_57] :
      ( k3_xboole_0(k1_tarski(A_56),B_57) = k1_xboole_0
      | r2_hidden(A_56,B_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_77])).

tff(c_57,plain,(
    ! [A_27,B_28] :
      ( r1_xboole_0(A_27,B_28)
      | k3_xboole_0(A_27,B_28) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_182,plain,(
    ! [B_46,A_47] :
      ( r1_xboole_0(B_46,A_47)
      | k3_xboole_0(A_47,B_46) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_57,c_6])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = A_9
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_561,plain,(
    ! [B_80,A_81] :
      ( k4_xboole_0(B_80,A_81) = B_80
      | k3_xboole_0(A_81,B_80) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_182,c_12])).

tff(c_26,plain,
    ( k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_199,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_648,plain,(
    k3_xboole_0(k1_tarski('#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_561,c_199])).

tff(c_663,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_648])).

tff(c_667,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_663])).

tff(c_668,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_669,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_30,plain,
    ( k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1'
    | k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_731,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_669,c_30])).

tff(c_44,plain,(
    ! [B_21,A_22] :
      ( r1_xboole_0(B_21,A_22)
      | ~ r1_xboole_0(A_22,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_47,plain,(
    ! [B_8,A_7] : r1_xboole_0(B_8,k4_xboole_0(A_7,B_8)) ),
    inference(resolution,[status(thm)],[c_10,c_44])).

tff(c_140,plain,(
    ! [A_39,B_40] :
      ( ~ r2_hidden(A_39,B_40)
      | ~ r1_xboole_0(k1_tarski(A_39),B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_154,plain,(
    ! [A_39,A_7] : ~ r2_hidden(A_39,k4_xboole_0(A_7,k1_tarski(A_39))) ),
    inference(resolution,[status(thm)],[c_47,c_140])).

tff(c_735,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_731,c_154])).

tff(c_755,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_668,c_735])).

tff(c_756,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_757,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_32,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_833,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_757,c_32])).

tff(c_758,plain,(
    ! [B_84,A_85] :
      ( r1_xboole_0(B_84,A_85)
      | ~ r1_xboole_0(A_85,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_761,plain,(
    ! [B_8,A_7] : r1_xboole_0(B_8,k4_xboole_0(A_7,B_8)) ),
    inference(resolution,[status(thm)],[c_10,c_758])).

tff(c_840,plain,(
    r1_xboole_0(k1_tarski('#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_833,c_761])).

tff(c_880,plain,(
    ! [A_98,B_99] :
      ( ~ r2_hidden(A_98,B_99)
      | ~ r1_xboole_0(k1_tarski(A_98),B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_883,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_840,c_880])).

tff(c_899,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_756,c_883])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:44:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.41  
% 2.43/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.41  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.43/1.41  
% 2.43/1.41  %Foreground sorts:
% 2.43/1.41  
% 2.43/1.41  
% 2.43/1.41  %Background operators:
% 2.43/1.41  
% 2.43/1.41  
% 2.43/1.41  %Foreground operators:
% 2.43/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.43/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.43/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.43/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.43/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.43/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.43/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.43/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.43/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.43/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.43/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.43/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.43/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.43/1.41  
% 2.43/1.42  tff(f_61, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.43/1.42  tff(f_55, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 2.43/1.42  tff(f_37, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.43/1.42  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.43/1.42  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.43/1.42  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.43/1.42  tff(f_50, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.43/1.42  tff(c_28, plain, (~r2_hidden('#skF_2', '#skF_1') | r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.43/1.42  tff(c_43, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_28])).
% 2.43/1.42  tff(c_238, plain, (![A_56, B_57]: (k4_xboole_0(k1_tarski(A_56), B_57)=k1_tarski(A_56) | r2_hidden(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.43/1.42  tff(c_10, plain, (![A_7, B_8]: (r1_xboole_0(k4_xboole_0(A_7, B_8), B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.43/1.42  tff(c_61, plain, (![A_29, B_30]: (k3_xboole_0(A_29, B_30)=k1_xboole_0 | ~r1_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.43/1.42  tff(c_77, plain, (![A_7, B_8]: (k3_xboole_0(k4_xboole_0(A_7, B_8), B_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_61])).
% 2.43/1.42  tff(c_261, plain, (![A_56, B_57]: (k3_xboole_0(k1_tarski(A_56), B_57)=k1_xboole_0 | r2_hidden(A_56, B_57))), inference(superposition, [status(thm), theory('equality')], [c_238, c_77])).
% 2.43/1.42  tff(c_57, plain, (![A_27, B_28]: (r1_xboole_0(A_27, B_28) | k3_xboole_0(A_27, B_28)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.43/1.42  tff(c_6, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.43/1.42  tff(c_182, plain, (![B_46, A_47]: (r1_xboole_0(B_46, A_47) | k3_xboole_0(A_47, B_46)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_57, c_6])).
% 2.43/1.42  tff(c_12, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=A_9 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.43/1.42  tff(c_561, plain, (![B_80, A_81]: (k4_xboole_0(B_80, A_81)=B_80 | k3_xboole_0(A_81, B_80)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_182, c_12])).
% 2.43/1.42  tff(c_26, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1' | r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.43/1.42  tff(c_199, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_26])).
% 2.43/1.42  tff(c_648, plain, (k3_xboole_0(k1_tarski('#skF_2'), '#skF_1')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_561, c_199])).
% 2.43/1.42  tff(c_663, plain, (r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_261, c_648])).
% 2.43/1.42  tff(c_667, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43, c_663])).
% 2.43/1.42  tff(c_668, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_26])).
% 2.43/1.42  tff(c_669, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))='#skF_1'), inference(splitRight, [status(thm)], [c_26])).
% 2.43/1.42  tff(c_30, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1' | k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.43/1.42  tff(c_731, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_669, c_30])).
% 2.43/1.42  tff(c_44, plain, (![B_21, A_22]: (r1_xboole_0(B_21, A_22) | ~r1_xboole_0(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.43/1.42  tff(c_47, plain, (![B_8, A_7]: (r1_xboole_0(B_8, k4_xboole_0(A_7, B_8)))), inference(resolution, [status(thm)], [c_10, c_44])).
% 2.43/1.42  tff(c_140, plain, (![A_39, B_40]: (~r2_hidden(A_39, B_40) | ~r1_xboole_0(k1_tarski(A_39), B_40))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.43/1.42  tff(c_154, plain, (![A_39, A_7]: (~r2_hidden(A_39, k4_xboole_0(A_7, k1_tarski(A_39))))), inference(resolution, [status(thm)], [c_47, c_140])).
% 2.43/1.42  tff(c_735, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_731, c_154])).
% 2.43/1.42  tff(c_755, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_668, c_735])).
% 2.43/1.42  tff(c_756, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_28])).
% 2.43/1.42  tff(c_757, plain, (r2_hidden('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_28])).
% 2.43/1.42  tff(c_32, plain, (~r2_hidden('#skF_2', '#skF_1') | k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.43/1.42  tff(c_833, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_757, c_32])).
% 2.43/1.42  tff(c_758, plain, (![B_84, A_85]: (r1_xboole_0(B_84, A_85) | ~r1_xboole_0(A_85, B_84))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.43/1.42  tff(c_761, plain, (![B_8, A_7]: (r1_xboole_0(B_8, k4_xboole_0(A_7, B_8)))), inference(resolution, [status(thm)], [c_10, c_758])).
% 2.43/1.42  tff(c_840, plain, (r1_xboole_0(k1_tarski('#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_833, c_761])).
% 2.43/1.42  tff(c_880, plain, (![A_98, B_99]: (~r2_hidden(A_98, B_99) | ~r1_xboole_0(k1_tarski(A_98), B_99))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.43/1.42  tff(c_883, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_840, c_880])).
% 2.43/1.42  tff(c_899, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_756, c_883])).
% 2.43/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.42  
% 2.43/1.42  Inference rules
% 2.43/1.42  ----------------------
% 2.43/1.42  #Ref     : 0
% 2.43/1.42  #Sup     : 207
% 2.43/1.42  #Fact    : 0
% 2.43/1.42  #Define  : 0
% 2.43/1.42  #Split   : 2
% 2.43/1.42  #Chain   : 0
% 2.43/1.42  #Close   : 0
% 2.43/1.42  
% 2.43/1.42  Ordering : KBO
% 2.43/1.42  
% 2.43/1.42  Simplification rules
% 2.43/1.42  ----------------------
% 2.43/1.42  #Subsume      : 30
% 2.43/1.42  #Demod        : 47
% 2.43/1.42  #Tautology    : 99
% 2.43/1.42  #SimpNegUnit  : 5
% 2.43/1.42  #BackRed      : 0
% 2.43/1.42  
% 2.43/1.42  #Partial instantiations: 0
% 2.43/1.42  #Strategies tried      : 1
% 2.43/1.42  
% 2.43/1.42  Timing (in seconds)
% 2.43/1.42  ----------------------
% 2.43/1.43  Preprocessing        : 0.31
% 2.43/1.43  Parsing              : 0.17
% 2.43/1.43  CNF conversion       : 0.02
% 2.43/1.43  Main loop            : 0.29
% 2.43/1.43  Inferencing          : 0.12
% 2.43/1.43  Reduction            : 0.08
% 2.43/1.43  Demodulation         : 0.06
% 2.43/1.43  BG Simplification    : 0.02
% 2.43/1.43  Subsumption          : 0.05
% 2.43/1.43  Abstraction          : 0.02
% 2.43/1.43  MUC search           : 0.00
% 2.43/1.43  Cooper               : 0.00
% 2.43/1.43  Total                : 0.64
% 2.43/1.43  Index Insertion      : 0.00
% 2.43/1.43  Index Deletion       : 0.00
% 2.43/1.43  Index Matching       : 0.00
% 2.43/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
