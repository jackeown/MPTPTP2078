%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:45 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 204 expanded)
%              Number of leaves         :   24 (  79 expanded)
%              Depth                    :   11
%              Number of atoms          :   48 ( 236 expanded)
%              Number of equality atoms :   15 ( 120 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_57,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_59,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_18,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_137,plain,(
    ! [A_37,B_38] :
      ( k2_xboole_0(A_37,B_38) = B_38
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_179,plain,(
    ! [A_40] : k2_xboole_0(k1_xboole_0,A_40) = A_40 ),
    inference(resolution,[status(thm)],[c_18,c_137])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_192,plain,(
    ! [A_40] : k2_xboole_0(A_40,k1_xboole_0) = A_40 ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_2])).

tff(c_36,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_49,plain,(
    ! [B_31,A_32] : k2_xboole_0(B_31,A_32) = k2_xboole_0(A_32,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_14,B_15] : r1_tarski(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_100,plain,(
    ! [B_33,A_34] : r1_tarski(B_33,k2_xboole_0(A_34,B_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_22])).

tff(c_109,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_100])).

tff(c_156,plain,(
    k2_xboole_0('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_109,c_137])).

tff(c_275,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_156])).

tff(c_282,plain,(
    ! [A_12] : r1_tarski('#skF_4',A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_18])).

tff(c_281,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_3'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_36])).

tff(c_209,plain,(
    ! [B_2] : k2_xboole_0(B_2,k1_xboole_0) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_179])).

tff(c_295,plain,(
    ! [B_2] : k2_xboole_0(B_2,'#skF_4') = B_2 ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_209])).

tff(c_408,plain,(
    k2_tarski('#skF_2','#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_295])).

tff(c_640,plain,(
    ! [B_67,C_68,A_69] :
      ( r2_hidden(B_67,C_68)
      | ~ r1_tarski(k2_tarski(A_69,B_67),C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_643,plain,(
    ! [C_68] :
      ( r2_hidden('#skF_3',C_68)
      | ~ r1_tarski('#skF_4',C_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_640])).

tff(c_657,plain,(
    ! [C_68] : r2_hidden('#skF_3',C_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_643])).

tff(c_20,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_283,plain,(
    ! [A_13] : r1_xboole_0(A_13,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_20])).

tff(c_718,plain,(
    ! [A_79,B_80,C_81] :
      ( ~ r1_xboole_0(A_79,B_80)
      | ~ r2_hidden(C_81,B_80)
      | ~ r2_hidden(C_81,A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_722,plain,(
    ! [C_82,A_83] :
      ( ~ r2_hidden(C_82,'#skF_4')
      | ~ r2_hidden(C_82,A_83) ) ),
    inference(resolution,[status(thm)],[c_283,c_718])).

tff(c_725,plain,(
    ! [A_83] : ~ r2_hidden('#skF_3',A_83) ),
    inference(resolution,[status(thm)],[c_657,c_722])).

tff(c_738,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_657,c_725])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.01/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.30  % Computer   : n017.cluster.edu
% 0.12/0.30  % Model      : x86_64 x86_64
% 0.12/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.30  % Memory     : 8042.1875MB
% 0.12/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.30  % CPULimit   : 60
% 0.12/0.30  % DateTime   : Tue Dec  1 18:40:31 EST 2020
% 0.12/0.30  % CPUTime    : 
% 0.16/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.23  
% 2.47/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.24  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.47/1.24  
% 2.47/1.24  %Foreground sorts:
% 2.47/1.24  
% 2.47/1.24  
% 2.47/1.24  %Background operators:
% 2.47/1.24  
% 2.47/1.24  
% 2.47/1.24  %Foreground operators:
% 2.47/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.47/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.47/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.47/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.47/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.47/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.47/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.47/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.47/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.47/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.47/1.24  
% 2.47/1.25  tff(f_57, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.47/1.25  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.47/1.25  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.47/1.25  tff(f_77, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.47/1.25  tff(f_61, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.47/1.25  tff(f_73, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.47/1.25  tff(f_59, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.47/1.25  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.47/1.25  tff(c_18, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.47/1.25  tff(c_137, plain, (![A_37, B_38]: (k2_xboole_0(A_37, B_38)=B_38 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.47/1.25  tff(c_179, plain, (![A_40]: (k2_xboole_0(k1_xboole_0, A_40)=A_40)), inference(resolution, [status(thm)], [c_18, c_137])).
% 2.47/1.25  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.47/1.25  tff(c_192, plain, (![A_40]: (k2_xboole_0(A_40, k1_xboole_0)=A_40)), inference(superposition, [status(thm), theory('equality')], [c_179, c_2])).
% 2.47/1.25  tff(c_36, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.47/1.25  tff(c_49, plain, (![B_31, A_32]: (k2_xboole_0(B_31, A_32)=k2_xboole_0(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.47/1.25  tff(c_22, plain, (![A_14, B_15]: (r1_tarski(A_14, k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.47/1.25  tff(c_100, plain, (![B_33, A_34]: (r1_tarski(B_33, k2_xboole_0(A_34, B_33)))), inference(superposition, [status(thm), theory('equality')], [c_49, c_22])).
% 2.47/1.25  tff(c_109, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_36, c_100])).
% 2.47/1.25  tff(c_156, plain, (k2_xboole_0('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_109, c_137])).
% 2.47/1.25  tff(c_275, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_192, c_156])).
% 2.47/1.25  tff(c_282, plain, (![A_12]: (r1_tarski('#skF_4', A_12))), inference(demodulation, [status(thm), theory('equality')], [c_275, c_18])).
% 2.47/1.25  tff(c_281, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_3'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_275, c_36])).
% 2.47/1.25  tff(c_209, plain, (![B_2]: (k2_xboole_0(B_2, k1_xboole_0)=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_179])).
% 2.47/1.25  tff(c_295, plain, (![B_2]: (k2_xboole_0(B_2, '#skF_4')=B_2)), inference(demodulation, [status(thm), theory('equality')], [c_275, c_209])).
% 2.47/1.25  tff(c_408, plain, (k2_tarski('#skF_2', '#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_281, c_295])).
% 2.47/1.25  tff(c_640, plain, (![B_67, C_68, A_69]: (r2_hidden(B_67, C_68) | ~r1_tarski(k2_tarski(A_69, B_67), C_68))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.47/1.25  tff(c_643, plain, (![C_68]: (r2_hidden('#skF_3', C_68) | ~r1_tarski('#skF_4', C_68))), inference(superposition, [status(thm), theory('equality')], [c_408, c_640])).
% 2.47/1.25  tff(c_657, plain, (![C_68]: (r2_hidden('#skF_3', C_68))), inference(demodulation, [status(thm), theory('equality')], [c_282, c_643])).
% 2.47/1.25  tff(c_20, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.47/1.25  tff(c_283, plain, (![A_13]: (r1_xboole_0(A_13, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_275, c_20])).
% 2.47/1.25  tff(c_718, plain, (![A_79, B_80, C_81]: (~r1_xboole_0(A_79, B_80) | ~r2_hidden(C_81, B_80) | ~r2_hidden(C_81, A_79))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.47/1.25  tff(c_722, plain, (![C_82, A_83]: (~r2_hidden(C_82, '#skF_4') | ~r2_hidden(C_82, A_83))), inference(resolution, [status(thm)], [c_283, c_718])).
% 2.47/1.25  tff(c_725, plain, (![A_83]: (~r2_hidden('#skF_3', A_83))), inference(resolution, [status(thm)], [c_657, c_722])).
% 2.47/1.25  tff(c_738, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_657, c_725])).
% 2.47/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.25  
% 2.47/1.25  Inference rules
% 2.47/1.25  ----------------------
% 2.47/1.25  #Ref     : 0
% 2.47/1.25  #Sup     : 163
% 2.47/1.25  #Fact    : 0
% 2.47/1.25  #Define  : 0
% 2.47/1.25  #Split   : 2
% 2.47/1.25  #Chain   : 0
% 2.47/1.25  #Close   : 0
% 2.47/1.25  
% 2.47/1.25  Ordering : KBO
% 2.47/1.25  
% 2.47/1.25  Simplification rules
% 2.47/1.25  ----------------------
% 2.47/1.25  #Subsume      : 0
% 2.47/1.25  #Demod        : 110
% 2.47/1.25  #Tautology    : 133
% 2.47/1.25  #SimpNegUnit  : 0
% 2.47/1.25  #BackRed      : 9
% 2.47/1.25  
% 2.47/1.25  #Partial instantiations: 0
% 2.47/1.25  #Strategies tried      : 1
% 2.47/1.25  
% 2.47/1.25  Timing (in seconds)
% 2.47/1.25  ----------------------
% 2.47/1.25  Preprocessing        : 0.31
% 2.47/1.25  Parsing              : 0.17
% 2.47/1.25  CNF conversion       : 0.02
% 2.47/1.25  Main loop            : 0.27
% 2.47/1.25  Inferencing          : 0.09
% 2.47/1.25  Reduction            : 0.10
% 2.47/1.25  Demodulation         : 0.08
% 2.47/1.25  BG Simplification    : 0.01
% 2.47/1.25  Subsumption          : 0.05
% 2.47/1.25  Abstraction          : 0.01
% 2.47/1.25  MUC search           : 0.00
% 2.47/1.25  Cooper               : 0.00
% 2.47/1.25  Total                : 0.60
% 2.47/1.25  Index Insertion      : 0.00
% 2.47/1.25  Index Deletion       : 0.00
% 2.47/1.25  Index Matching       : 0.00
% 2.47/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
