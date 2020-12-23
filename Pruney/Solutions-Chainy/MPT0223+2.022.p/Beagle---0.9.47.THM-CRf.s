%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:19 EST 2020

% Result     : Theorem 12.17s
% Output     : CNFRefutation 12.17s
% Verified   : 
% Statistics : Number of formulae       :   60 (  62 expanded)
%              Number of leaves         :   33 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :   58 (  63 expanded)
%              Number of equality atoms :   21 (  25 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_52,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_80,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_60,plain,(
    ! [C_35] : r2_hidden(C_35,k1_tarski(C_35)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_82,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_160,plain,(
    k3_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k1_tarski('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_82])).

tff(c_20,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_3226,plain,(
    ! [A_2703,B_2704,C_2705] :
      ( r2_hidden(A_2703,B_2704)
      | ~ r2_hidden(A_2703,C_2705)
      | r2_hidden(A_2703,k5_xboole_0(B_2704,C_2705)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_25326,plain,(
    ! [A_6805,A_6806,B_6807] :
      ( r2_hidden(A_6805,A_6806)
      | ~ r2_hidden(A_6805,k3_xboole_0(A_6806,B_6807))
      | r2_hidden(A_6805,k4_xboole_0(A_6806,B_6807)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_3226])).

tff(c_30,plain,(
    ! [A_21] : r1_xboole_0(A_21,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_146,plain,(
    ! [B_59,A_60] :
      ( r1_xboole_0(B_59,A_60)
      | ~ r1_xboole_0(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_149,plain,(
    ! [A_21] : r1_xboole_0(k1_xboole_0,A_21) ),
    inference(resolution,[status(thm)],[c_30,c_146])).

tff(c_579,plain,(
    ! [A_101,B_102,C_103] : k4_xboole_0(k3_xboole_0(A_101,B_102),C_103) = k3_xboole_0(A_101,k4_xboole_0(B_102,C_103)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_302,plain,(
    ! [A_87,B_88] : k2_xboole_0(k3_xboole_0(A_87,B_88),k4_xboole_0(A_87,B_88)) = A_87 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_24,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k2_xboole_0(A_14,B_15)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_308,plain,(
    ! [A_87,B_88] : k4_xboole_0(k3_xboole_0(A_87,B_88),A_87) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_24])).

tff(c_1498,plain,(
    ! [C_1592,B_1593] : k3_xboole_0(C_1592,k4_xboole_0(B_1593,C_1592)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_579,c_308])).

tff(c_32,plain,(
    ! [A_22,B_23] :
      ( ~ r1_xboole_0(k3_xboole_0(A_22,B_23),B_23)
      | r1_xboole_0(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1524,plain,(
    ! [B_1593,C_1592] :
      ( ~ r1_xboole_0(k1_xboole_0,k4_xboole_0(B_1593,C_1592))
      | r1_xboole_0(C_1592,k4_xboole_0(B_1593,C_1592)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1498,c_32])).

tff(c_1571,plain,(
    ! [C_1629,B_1630] : r1_xboole_0(C_1629,k4_xboole_0(B_1630,C_1629)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_1524])).

tff(c_78,plain,(
    ! [A_46,B_47] :
      ( ~ r2_hidden(A_46,B_47)
      | ~ r1_xboole_0(k1_tarski(A_46),B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1600,plain,(
    ! [A_46,B_1630] : ~ r2_hidden(A_46,k4_xboole_0(B_1630,k1_tarski(A_46))) ),
    inference(resolution,[status(thm)],[c_1571,c_78])).

tff(c_46293,plain,(
    ! [A_9466,A_9467] :
      ( r2_hidden(A_9466,A_9467)
      | ~ r2_hidden(A_9466,k3_xboole_0(A_9467,k1_tarski(A_9466))) ) ),
    inference(resolution,[status(thm)],[c_25326,c_1600])).

tff(c_46355,plain,
    ( r2_hidden('#skF_5',k1_tarski('#skF_6'))
    | ~ r2_hidden('#skF_5',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_46293])).

tff(c_46384,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_46355])).

tff(c_58,plain,(
    ! [C_35,A_31] :
      ( C_35 = A_31
      | ~ r2_hidden(C_35,k1_tarski(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_46396,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_46384,c_58])).

tff(c_46437,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_46396])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:55:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.17/5.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.17/5.64  
% 12.17/5.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.17/5.64  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_5 > #skF_2 > #skF_6 > #skF_1 > #skF_4
% 12.17/5.64  
% 12.17/5.64  %Foreground sorts:
% 12.17/5.64  
% 12.17/5.64  
% 12.17/5.64  %Background operators:
% 12.17/5.64  
% 12.17/5.64  
% 12.17/5.64  %Foreground operators:
% 12.17/5.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.17/5.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.17/5.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.17/5.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.17/5.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.17/5.64  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 12.17/5.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.17/5.64  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 12.17/5.64  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.17/5.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.17/5.64  tff('#skF_5', type, '#skF_5': $i).
% 12.17/5.64  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 12.17/5.64  tff('#skF_6', type, '#skF_6': $i).
% 12.17/5.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.17/5.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 12.17/5.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.17/5.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.17/5.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.17/5.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.17/5.64  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 12.17/5.64  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 12.17/5.64  
% 12.17/5.65  tff(f_98, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 12.17/5.65  tff(f_80, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 12.17/5.65  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 12.17/5.65  tff(f_42, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 12.17/5.65  tff(f_40, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 12.17/5.65  tff(f_52, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 12.17/5.65  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 12.17/5.65  tff(f_48, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 12.17/5.65  tff(f_50, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 12.17/5.65  tff(f_46, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 12.17/5.65  tff(f_58, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_xboole_1)).
% 12.17/5.65  tff(f_93, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 12.17/5.65  tff(c_80, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_98])).
% 12.17/5.65  tff(c_60, plain, (![C_35]: (r2_hidden(C_35, k1_tarski(C_35)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.17/5.65  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.17/5.65  tff(c_82, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 12.17/5.65  tff(c_160, plain, (k3_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k1_tarski('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2, c_82])).
% 12.17/5.65  tff(c_20, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.17/5.65  tff(c_3226, plain, (![A_2703, B_2704, C_2705]: (r2_hidden(A_2703, B_2704) | ~r2_hidden(A_2703, C_2705) | r2_hidden(A_2703, k5_xboole_0(B_2704, C_2705)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 12.17/5.65  tff(c_25326, plain, (![A_6805, A_6806, B_6807]: (r2_hidden(A_6805, A_6806) | ~r2_hidden(A_6805, k3_xboole_0(A_6806, B_6807)) | r2_hidden(A_6805, k4_xboole_0(A_6806, B_6807)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_3226])).
% 12.17/5.65  tff(c_30, plain, (![A_21]: (r1_xboole_0(A_21, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_52])).
% 12.17/5.65  tff(c_146, plain, (![B_59, A_60]: (r1_xboole_0(B_59, A_60) | ~r1_xboole_0(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.17/5.65  tff(c_149, plain, (![A_21]: (r1_xboole_0(k1_xboole_0, A_21))), inference(resolution, [status(thm)], [c_30, c_146])).
% 12.17/5.65  tff(c_579, plain, (![A_101, B_102, C_103]: (k4_xboole_0(k3_xboole_0(A_101, B_102), C_103)=k3_xboole_0(A_101, k4_xboole_0(B_102, C_103)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.17/5.65  tff(c_302, plain, (![A_87, B_88]: (k2_xboole_0(k3_xboole_0(A_87, B_88), k4_xboole_0(A_87, B_88))=A_87)), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.17/5.65  tff(c_24, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k2_xboole_0(A_14, B_15))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.17/5.65  tff(c_308, plain, (![A_87, B_88]: (k4_xboole_0(k3_xboole_0(A_87, B_88), A_87)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_302, c_24])).
% 12.17/5.65  tff(c_1498, plain, (![C_1592, B_1593]: (k3_xboole_0(C_1592, k4_xboole_0(B_1593, C_1592))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_579, c_308])).
% 12.17/5.65  tff(c_32, plain, (![A_22, B_23]: (~r1_xboole_0(k3_xboole_0(A_22, B_23), B_23) | r1_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_58])).
% 12.17/5.65  tff(c_1524, plain, (![B_1593, C_1592]: (~r1_xboole_0(k1_xboole_0, k4_xboole_0(B_1593, C_1592)) | r1_xboole_0(C_1592, k4_xboole_0(B_1593, C_1592)))), inference(superposition, [status(thm), theory('equality')], [c_1498, c_32])).
% 12.17/5.65  tff(c_1571, plain, (![C_1629, B_1630]: (r1_xboole_0(C_1629, k4_xboole_0(B_1630, C_1629)))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_1524])).
% 12.17/5.65  tff(c_78, plain, (![A_46, B_47]: (~r2_hidden(A_46, B_47) | ~r1_xboole_0(k1_tarski(A_46), B_47))), inference(cnfTransformation, [status(thm)], [f_93])).
% 12.17/5.65  tff(c_1600, plain, (![A_46, B_1630]: (~r2_hidden(A_46, k4_xboole_0(B_1630, k1_tarski(A_46))))), inference(resolution, [status(thm)], [c_1571, c_78])).
% 12.17/5.65  tff(c_46293, plain, (![A_9466, A_9467]: (r2_hidden(A_9466, A_9467) | ~r2_hidden(A_9466, k3_xboole_0(A_9467, k1_tarski(A_9466))))), inference(resolution, [status(thm)], [c_25326, c_1600])).
% 12.17/5.65  tff(c_46355, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6')) | ~r2_hidden('#skF_5', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_160, c_46293])).
% 12.17/5.65  tff(c_46384, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_46355])).
% 12.17/5.65  tff(c_58, plain, (![C_35, A_31]: (C_35=A_31 | ~r2_hidden(C_35, k1_tarski(A_31)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.17/5.65  tff(c_46396, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_46384, c_58])).
% 12.17/5.65  tff(c_46437, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_46396])).
% 12.17/5.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.17/5.65  
% 12.17/5.65  Inference rules
% 12.17/5.65  ----------------------
% 12.17/5.65  #Ref     : 0
% 12.17/5.65  #Sup     : 10505
% 12.17/5.65  #Fact    : 6
% 12.17/5.65  #Define  : 0
% 12.17/5.65  #Split   : 5
% 12.17/5.65  #Chain   : 0
% 12.17/5.65  #Close   : 0
% 12.17/5.65  
% 12.17/5.65  Ordering : KBO
% 12.17/5.65  
% 12.17/5.65  Simplification rules
% 12.17/5.65  ----------------------
% 12.17/5.65  #Subsume      : 655
% 12.17/5.65  #Demod        : 11748
% 12.17/5.65  #Tautology    : 7516
% 12.17/5.65  #SimpNegUnit  : 135
% 12.17/5.65  #BackRed      : 10
% 12.17/5.65  
% 12.17/5.65  #Partial instantiations: 4064
% 12.17/5.65  #Strategies tried      : 1
% 12.17/5.65  
% 12.17/5.65  Timing (in seconds)
% 12.17/5.65  ----------------------
% 12.17/5.66  Preprocessing        : 0.33
% 12.17/5.66  Parsing              : 0.17
% 12.17/5.66  CNF conversion       : 0.02
% 12.17/5.66  Main loop            : 4.56
% 12.17/5.66  Inferencing          : 0.92
% 12.17/5.66  Reduction            : 2.56
% 12.17/5.66  Demodulation         : 2.26
% 12.17/5.66  BG Simplification    : 0.09
% 12.17/5.66  Subsumption          : 0.78
% 12.17/5.66  Abstraction          : 0.14
% 12.17/5.66  MUC search           : 0.00
% 12.17/5.66  Cooper               : 0.00
% 12.17/5.66  Total                : 4.92
% 12.17/5.66  Index Insertion      : 0.00
% 12.17/5.66  Index Deletion       : 0.00
% 12.17/5.66  Index Matching       : 0.00
% 12.17/5.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
