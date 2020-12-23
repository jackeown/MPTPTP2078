%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:42 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   52 (  78 expanded)
%              Number of leaves         :   23 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   48 (  90 expanded)
%              Number of equality atoms :   34 (  61 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,B)
          & r1_xboole_0(A,B)
          & r1_xboole_0(C,B) )
       => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_53,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k3_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(c_20,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_14,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_148,plain,(
    ! [A_29,B_30,C_31] :
      ( ~ r1_xboole_0(A_29,B_30)
      | ~ r2_hidden(C_31,k3_xboole_0(A_29,B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_160,plain,(
    ! [A_32,B_33] :
      ( ~ r1_xboole_0(A_32,B_33)
      | k3_xboole_0(A_32,B_33) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_148])).

tff(c_168,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_160])).

tff(c_231,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_168])).

tff(c_12,plain,(
    ! [A_13] : k2_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_82,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k2_xboole_0(A_23,B_24)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_92,plain,(
    ! [A_13] : k4_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_82])).

tff(c_272,plain,(
    ! [A_37,B_38,C_39] : k2_xboole_0(k4_xboole_0(A_37,B_38),k4_xboole_0(A_37,C_39)) = k4_xboole_0(A_37,k3_xboole_0(B_38,C_39)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_308,plain,(
    ! [A_13,B_38] : k4_xboole_0(A_13,k3_xboole_0(B_38,A_13)) = k2_xboole_0(k4_xboole_0(A_13,B_38),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_272])).

tff(c_404,plain,(
    ! [A_47,B_48] : k4_xboole_0(A_47,k3_xboole_0(B_48,A_47)) = k4_xboole_0(A_47,B_48) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_308])).

tff(c_419,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_404])).

tff(c_439,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_419])).

tff(c_16,plain,(
    ! [A_15,B_16] : k4_xboole_0(k2_xboole_0(A_15,B_16),B_16) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_26,plain,(
    k2_xboole_0('#skF_5','#skF_4') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_117,plain,(
    ! [A_27,B_28] : k4_xboole_0(k2_xboole_0(A_27,B_28),B_28) = k4_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_130,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3','#skF_4'),'#skF_4') = k4_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_117])).

tff(c_141,plain,(
    k4_xboole_0('#skF_5','#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_130])).

tff(c_22,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_167,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_160])).

tff(c_189,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_2])).

tff(c_422,plain,(
    k4_xboole_0('#skF_5',k1_xboole_0) = k4_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_404])).

tff(c_440,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_14,c_422])).

tff(c_587,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_439,c_440])).

tff(c_589,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_587])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:41:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.30  
% 2.13/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.30  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.13/1.30  
% 2.13/1.30  %Foreground sorts:
% 2.13/1.30  
% 2.13/1.30  
% 2.13/1.30  %Background operators:
% 2.13/1.30  
% 2.13/1.30  
% 2.13/1.30  %Foreground operators:
% 2.13/1.30  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.13/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.13/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.13/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.13/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.13/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.13/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.13/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.13/1.30  
% 2.13/1.32  tff(f_68, negated_conjecture, ~(![A, B, C]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, B)) & r1_xboole_0(A, B)) & r1_xboole_0(C, B)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_xboole_1)).
% 2.13/1.32  tff(f_55, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.13/1.32  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.13/1.32  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.13/1.32  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.13/1.32  tff(f_53, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.13/1.32  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.13/1.32  tff(f_51, axiom, (![A, B, C]: (k4_xboole_0(A, k3_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l36_xboole_1)).
% 2.13/1.32  tff(f_57, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.13/1.32  tff(c_20, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.13/1.32  tff(c_14, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.13/1.32  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.13/1.32  tff(c_24, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.13/1.32  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.13/1.32  tff(c_148, plain, (![A_29, B_30, C_31]: (~r1_xboole_0(A_29, B_30) | ~r2_hidden(C_31, k3_xboole_0(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.13/1.32  tff(c_160, plain, (![A_32, B_33]: (~r1_xboole_0(A_32, B_33) | k3_xboole_0(A_32, B_33)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_148])).
% 2.13/1.32  tff(c_168, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_160])).
% 2.13/1.32  tff(c_231, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2, c_168])).
% 2.13/1.32  tff(c_12, plain, (![A_13]: (k2_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.13/1.32  tff(c_82, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k2_xboole_0(A_23, B_24))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.13/1.32  tff(c_92, plain, (![A_13]: (k4_xboole_0(A_13, A_13)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_82])).
% 2.13/1.32  tff(c_272, plain, (![A_37, B_38, C_39]: (k2_xboole_0(k4_xboole_0(A_37, B_38), k4_xboole_0(A_37, C_39))=k4_xboole_0(A_37, k3_xboole_0(B_38, C_39)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.13/1.32  tff(c_308, plain, (![A_13, B_38]: (k4_xboole_0(A_13, k3_xboole_0(B_38, A_13))=k2_xboole_0(k4_xboole_0(A_13, B_38), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_92, c_272])).
% 2.13/1.32  tff(c_404, plain, (![A_47, B_48]: (k4_xboole_0(A_47, k3_xboole_0(B_48, A_47))=k4_xboole_0(A_47, B_48))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_308])).
% 2.13/1.32  tff(c_419, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_231, c_404])).
% 2.13/1.32  tff(c_439, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_419])).
% 2.13/1.32  tff(c_16, plain, (![A_15, B_16]: (k4_xboole_0(k2_xboole_0(A_15, B_16), B_16)=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.13/1.32  tff(c_26, plain, (k2_xboole_0('#skF_5', '#skF_4')=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.13/1.32  tff(c_117, plain, (![A_27, B_28]: (k4_xboole_0(k2_xboole_0(A_27, B_28), B_28)=k4_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.13/1.32  tff(c_130, plain, (k4_xboole_0(k2_xboole_0('#skF_3', '#skF_4'), '#skF_4')=k4_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_26, c_117])).
% 2.13/1.32  tff(c_141, plain, (k4_xboole_0('#skF_5', '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_130])).
% 2.13/1.32  tff(c_22, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.13/1.32  tff(c_167, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_160])).
% 2.13/1.32  tff(c_189, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_167, c_2])).
% 2.13/1.32  tff(c_422, plain, (k4_xboole_0('#skF_5', k1_xboole_0)=k4_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_189, c_404])).
% 2.13/1.32  tff(c_440, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_141, c_14, c_422])).
% 2.13/1.32  tff(c_587, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_439, c_440])).
% 2.13/1.32  tff(c_589, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_587])).
% 2.13/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.32  
% 2.13/1.32  Inference rules
% 2.13/1.32  ----------------------
% 2.13/1.32  #Ref     : 0
% 2.13/1.32  #Sup     : 152
% 2.13/1.32  #Fact    : 0
% 2.13/1.32  #Define  : 0
% 2.13/1.32  #Split   : 0
% 2.13/1.32  #Chain   : 0
% 2.13/1.32  #Close   : 0
% 2.13/1.32  
% 2.13/1.32  Ordering : KBO
% 2.13/1.32  
% 2.13/1.32  Simplification rules
% 2.13/1.32  ----------------------
% 2.13/1.32  #Subsume      : 10
% 2.13/1.32  #Demod        : 57
% 2.13/1.32  #Tautology    : 79
% 2.13/1.32  #SimpNegUnit  : 4
% 2.13/1.32  #BackRed      : 2
% 2.13/1.32  
% 2.13/1.32  #Partial instantiations: 0
% 2.13/1.32  #Strategies tried      : 1
% 2.13/1.32  
% 2.13/1.32  Timing (in seconds)
% 2.13/1.32  ----------------------
% 2.13/1.32  Preprocessing        : 0.28
% 2.13/1.32  Parsing              : 0.15
% 2.13/1.32  CNF conversion       : 0.02
% 2.13/1.32  Main loop            : 0.27
% 2.13/1.32  Inferencing          : 0.10
% 2.13/1.32  Reduction            : 0.10
% 2.13/1.32  Demodulation         : 0.08
% 2.13/1.32  BG Simplification    : 0.01
% 2.13/1.32  Subsumption          : 0.04
% 2.13/1.32  Abstraction          : 0.01
% 2.13/1.32  MUC search           : 0.00
% 2.13/1.32  Cooper               : 0.00
% 2.13/1.32  Total                : 0.58
% 2.13/1.32  Index Insertion      : 0.00
% 2.13/1.32  Index Deletion       : 0.00
% 2.13/1.32  Index Matching       : 0.00
% 2.13/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
