%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:07 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :   61 (  98 expanded)
%              Number of leaves         :   25 (  43 expanded)
%              Depth                    :    7
%              Number of atoms          :   64 ( 203 expanded)
%              Number of equality atoms :   52 ( 188 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_42,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_76,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_40,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_74,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_46,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_20,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_80,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_20])).

tff(c_580,plain,(
    ! [B_78,A_79] :
      ( k1_tarski(B_78) = A_79
      | k1_xboole_0 = A_79
      | ~ r1_tarski(A_79,k1_tarski(B_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_596,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_80,c_580])).

tff(c_609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_74,c_596])).

tff(c_610,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_611,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_18,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_612,plain,(
    ! [A_12] : k5_xboole_0(A_12,'#skF_2') = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_18])).

tff(c_16,plain,(
    ! [A_11] : k4_xboole_0(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_614,plain,(
    ! [A_11] : k4_xboole_0('#skF_2',A_11) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_611,c_16])).

tff(c_840,plain,(
    ! [A_103,B_104] : k5_xboole_0(A_103,k4_xboole_0(B_104,A_103)) = k2_xboole_0(A_103,B_104) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_849,plain,(
    ! [A_11] : k5_xboole_0(A_11,'#skF_2') = k2_xboole_0(A_11,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_614,c_840])).

tff(c_852,plain,(
    ! [A_11] : k2_xboole_0(A_11,'#skF_2') = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_612,c_849])).

tff(c_661,plain,(
    ! [B_85,A_86] : k2_xboole_0(B_85,A_86) = k2_xboole_0(A_86,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_676,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_661,c_46])).

tff(c_866,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_852,c_676])).

tff(c_868,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_610,c_866])).

tff(c_869,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_870,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_44,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_899,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_870,c_870,c_44])).

tff(c_900,plain,(
    ! [B_110,A_111] : k2_xboole_0(B_110,A_111) = k2_xboole_0(A_111,B_110) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_889,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_870,c_46])).

tff(c_915,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_900,c_889])).

tff(c_954,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_915,c_20])).

tff(c_1359,plain,(
    ! [B_146,A_147] :
      ( k1_tarski(B_146) = A_147
      | k1_xboole_0 = A_147
      | ~ r1_tarski(A_147,k1_tarski(B_146)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1366,plain,(
    ! [A_147] :
      ( k1_tarski('#skF_1') = A_147
      | k1_xboole_0 = A_147
      | ~ r1_tarski(A_147,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_870,c_1359])).

tff(c_1376,plain,(
    ! [A_148] :
      ( A_148 = '#skF_2'
      | k1_xboole_0 = A_148
      | ~ r1_tarski(A_148,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_870,c_1366])).

tff(c_1386,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_954,c_1376])).

tff(c_1399,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_869,c_899,c_1386])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:31:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.50  
% 2.96/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.50  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.96/1.50  
% 2.96/1.50  %Foreground sorts:
% 2.96/1.50  
% 2.96/1.50  
% 2.96/1.50  %Background operators:
% 2.96/1.50  
% 2.96/1.50  
% 2.96/1.50  %Foreground operators:
% 2.96/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.96/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.96/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.96/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.96/1.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.96/1.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.96/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.96/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.96/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.96/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.96/1.50  tff('#skF_2', type, '#skF_2': $i).
% 2.96/1.50  tff('#skF_3', type, '#skF_3': $i).
% 2.96/1.50  tff('#skF_1', type, '#skF_1': $i).
% 2.96/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.96/1.50  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.96/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.96/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.96/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.96/1.50  
% 3.07/1.51  tff(f_84, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.07/1.51  tff(f_47, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.07/1.51  tff(f_63, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.07/1.51  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.07/1.51  tff(f_43, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 3.07/1.51  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.07/1.51  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.07/1.51  tff(c_42, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.07/1.51  tff(c_76, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_42])).
% 3.07/1.51  tff(c_40, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.07/1.51  tff(c_74, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_40])).
% 3.07/1.51  tff(c_46, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.07/1.51  tff(c_20, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.07/1.51  tff(c_80, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_20])).
% 3.07/1.51  tff(c_580, plain, (![B_78, A_79]: (k1_tarski(B_78)=A_79 | k1_xboole_0=A_79 | ~r1_tarski(A_79, k1_tarski(B_78)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.07/1.51  tff(c_596, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_80, c_580])).
% 3.07/1.51  tff(c_609, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_74, c_596])).
% 3.07/1.51  tff(c_610, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_42])).
% 3.07/1.51  tff(c_611, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_42])).
% 3.07/1.51  tff(c_18, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.07/1.51  tff(c_612, plain, (![A_12]: (k5_xboole_0(A_12, '#skF_2')=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_611, c_18])).
% 3.07/1.51  tff(c_16, plain, (![A_11]: (k4_xboole_0(k1_xboole_0, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.07/1.51  tff(c_614, plain, (![A_11]: (k4_xboole_0('#skF_2', A_11)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_611, c_611, c_16])).
% 3.07/1.51  tff(c_840, plain, (![A_103, B_104]: (k5_xboole_0(A_103, k4_xboole_0(B_104, A_103))=k2_xboole_0(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.07/1.51  tff(c_849, plain, (![A_11]: (k5_xboole_0(A_11, '#skF_2')=k2_xboole_0(A_11, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_614, c_840])).
% 3.07/1.51  tff(c_852, plain, (![A_11]: (k2_xboole_0(A_11, '#skF_2')=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_612, c_849])).
% 3.07/1.51  tff(c_661, plain, (![B_85, A_86]: (k2_xboole_0(B_85, A_86)=k2_xboole_0(A_86, B_85))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.07/1.51  tff(c_676, plain, (k2_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_661, c_46])).
% 3.07/1.51  tff(c_866, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_852, c_676])).
% 3.07/1.51  tff(c_868, plain, $false, inference(negUnitSimplification, [status(thm)], [c_610, c_866])).
% 3.07/1.51  tff(c_869, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_40])).
% 3.07/1.51  tff(c_870, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_40])).
% 3.07/1.51  tff(c_44, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.07/1.51  tff(c_899, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_870, c_870, c_44])).
% 3.07/1.51  tff(c_900, plain, (![B_110, A_111]: (k2_xboole_0(B_110, A_111)=k2_xboole_0(A_111, B_110))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.07/1.51  tff(c_889, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_870, c_46])).
% 3.07/1.51  tff(c_915, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_900, c_889])).
% 3.07/1.51  tff(c_954, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_915, c_20])).
% 3.07/1.51  tff(c_1359, plain, (![B_146, A_147]: (k1_tarski(B_146)=A_147 | k1_xboole_0=A_147 | ~r1_tarski(A_147, k1_tarski(B_146)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.07/1.51  tff(c_1366, plain, (![A_147]: (k1_tarski('#skF_1')=A_147 | k1_xboole_0=A_147 | ~r1_tarski(A_147, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_870, c_1359])).
% 3.07/1.51  tff(c_1376, plain, (![A_148]: (A_148='#skF_2' | k1_xboole_0=A_148 | ~r1_tarski(A_148, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_870, c_1366])).
% 3.07/1.51  tff(c_1386, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_954, c_1376])).
% 3.07/1.51  tff(c_1399, plain, $false, inference(negUnitSimplification, [status(thm)], [c_869, c_899, c_1386])).
% 3.07/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.51  
% 3.07/1.51  Inference rules
% 3.07/1.51  ----------------------
% 3.07/1.51  #Ref     : 0
% 3.07/1.51  #Sup     : 329
% 3.07/1.51  #Fact    : 0
% 3.07/1.51  #Define  : 0
% 3.07/1.51  #Split   : 5
% 3.07/1.51  #Chain   : 0
% 3.07/1.51  #Close   : 0
% 3.07/1.51  
% 3.07/1.51  Ordering : KBO
% 3.07/1.51  
% 3.07/1.51  Simplification rules
% 3.07/1.51  ----------------------
% 3.07/1.51  #Subsume      : 25
% 3.07/1.51  #Demod        : 104
% 3.07/1.51  #Tautology    : 218
% 3.07/1.51  #SimpNegUnit  : 7
% 3.07/1.51  #BackRed      : 5
% 3.07/1.51  
% 3.07/1.51  #Partial instantiations: 0
% 3.07/1.51  #Strategies tried      : 1
% 3.07/1.51  
% 3.07/1.51  Timing (in seconds)
% 3.07/1.51  ----------------------
% 3.07/1.52  Preprocessing        : 0.31
% 3.07/1.52  Parsing              : 0.17
% 3.07/1.52  CNF conversion       : 0.02
% 3.07/1.52  Main loop            : 0.40
% 3.07/1.52  Inferencing          : 0.14
% 3.07/1.52  Reduction            : 0.13
% 3.07/1.52  Demodulation         : 0.10
% 3.07/1.52  BG Simplification    : 0.02
% 3.07/1.52  Subsumption          : 0.07
% 3.07/1.52  Abstraction          : 0.02
% 3.07/1.52  MUC search           : 0.00
% 3.07/1.52  Cooper               : 0.00
% 3.07/1.52  Total                : 0.74
% 3.07/1.52  Index Insertion      : 0.00
% 3.07/1.52  Index Deletion       : 0.00
% 3.07/1.52  Index Matching       : 0.00
% 3.07/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
