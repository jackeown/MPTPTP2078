%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:11 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :   44 (  52 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :   46 (  62 expanded)
%              Number of equality atoms :   19 (  24 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_60,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_58,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_22,plain,(
    ! [A_22,B_23] : k4_xboole_0(A_22,k4_xboole_0(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_28,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_353,plain,(
    ! [A_69,B_70] :
      ( r2_hidden('#skF_2'(A_69,B_70),k3_xboole_0(A_69,B_70))
      | r1_xboole_0(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_117,plain,(
    ! [A_39,B_40,C_41] :
      ( ~ r1_xboole_0(A_39,B_40)
      | ~ r2_hidden(C_41,k3_xboole_0(A_39,B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_127,plain,(
    ! [B_4,A_3,C_41] :
      ( ~ r1_xboole_0(B_4,A_3)
      | ~ r2_hidden(C_41,k3_xboole_0(A_3,B_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_117])).

tff(c_392,plain,(
    ! [B_71,A_72] :
      ( ~ r1_xboole_0(B_71,A_72)
      | r1_xboole_0(A_72,B_71) ) ),
    inference(resolution,[status(thm)],[c_353,c_127])).

tff(c_395,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_392])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_223,plain,(
    ! [A_55,B_56,B_57] :
      ( ~ r1_xboole_0(A_55,B_56)
      | r1_tarski(k3_xboole_0(A_55,B_56),B_57) ) ),
    inference(resolution,[status(thm)],[c_10,c_117])).

tff(c_16,plain,(
    ! [A_15,B_16] :
      ( k2_xboole_0(A_15,B_16) = B_16
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_287,plain,(
    ! [A_64,B_65,B_66] :
      ( k2_xboole_0(k3_xboole_0(A_64,B_65),B_66) = B_66
      | ~ r1_xboole_0(A_64,B_65) ) ),
    inference(resolution,[status(thm)],[c_223,c_16])).

tff(c_157,plain,(
    ! [A_45,B_46] : k2_xboole_0(k3_xboole_0(A_45,B_46),k4_xboole_0(A_45,B_46)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_169,plain,(
    ! [B_4,A_3] : k2_xboole_0(k3_xboole_0(B_4,A_3),k4_xboole_0(A_3,B_4)) = A_3 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_157])).

tff(c_294,plain,(
    ! [B_65,A_64] :
      ( k4_xboole_0(B_65,A_64) = B_65
      | ~ r1_xboole_0(A_64,B_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_169])).

tff(c_403,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_395,c_294])).

tff(c_20,plain,(
    ! [A_19,B_20,C_21] : k4_xboole_0(k4_xboole_0(A_19,B_20),C_21) = k4_xboole_0(A_19,k2_xboole_0(B_20,C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_778,plain,(
    ! [C_80] : k4_xboole_0('#skF_3',k2_xboole_0('#skF_4',C_80)) = k4_xboole_0('#skF_3',C_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_20])).

tff(c_796,plain,(
    ! [C_80] : k4_xboole_0('#skF_3',k4_xboole_0('#skF_3',C_80)) = k3_xboole_0('#skF_3',k2_xboole_0('#skF_4',C_80)) ),
    inference(superposition,[status(thm),theory(equality)],[c_778,c_22])).

tff(c_825,plain,(
    ! [C_80] : k3_xboole_0('#skF_3',k2_xboole_0('#skF_4',C_80)) = k3_xboole_0('#skF_3',C_80) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_796])).

tff(c_26,plain,(
    k3_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) != k3_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1067,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_825,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:50:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.00/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.46  
% 3.00/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.46  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.00/1.46  
% 3.00/1.46  %Foreground sorts:
% 3.00/1.46  
% 3.00/1.46  
% 3.00/1.46  %Background operators:
% 3.00/1.46  
% 3.00/1.46  
% 3.00/1.46  %Foreground operators:
% 3.00/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.00/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.00/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.00/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.00/1.46  tff('#skF_5', type, '#skF_5': $i).
% 3.00/1.46  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.00/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.00/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.00/1.46  tff('#skF_4', type, '#skF_4': $i).
% 3.00/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.00/1.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.00/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.00/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.00/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.00/1.46  
% 3.00/1.47  tff(f_60, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.00/1.47  tff(f_67, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_xboole_1)).
% 3.00/1.47  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.00/1.47  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.00/1.47  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.00/1.47  tff(f_54, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.00/1.47  tff(f_62, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.00/1.47  tff(f_58, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.00/1.47  tff(c_22, plain, (![A_22, B_23]: (k4_xboole_0(A_22, k4_xboole_0(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.00/1.47  tff(c_28, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.00/1.47  tff(c_353, plain, (![A_69, B_70]: (r2_hidden('#skF_2'(A_69, B_70), k3_xboole_0(A_69, B_70)) | r1_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.00/1.47  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.00/1.47  tff(c_117, plain, (![A_39, B_40, C_41]: (~r1_xboole_0(A_39, B_40) | ~r2_hidden(C_41, k3_xboole_0(A_39, B_40)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.00/1.47  tff(c_127, plain, (![B_4, A_3, C_41]: (~r1_xboole_0(B_4, A_3) | ~r2_hidden(C_41, k3_xboole_0(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_117])).
% 3.00/1.47  tff(c_392, plain, (![B_71, A_72]: (~r1_xboole_0(B_71, A_72) | r1_xboole_0(A_72, B_71))), inference(resolution, [status(thm)], [c_353, c_127])).
% 3.00/1.47  tff(c_395, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_392])).
% 3.00/1.47  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.00/1.47  tff(c_223, plain, (![A_55, B_56, B_57]: (~r1_xboole_0(A_55, B_56) | r1_tarski(k3_xboole_0(A_55, B_56), B_57))), inference(resolution, [status(thm)], [c_10, c_117])).
% 3.00/1.47  tff(c_16, plain, (![A_15, B_16]: (k2_xboole_0(A_15, B_16)=B_16 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.00/1.47  tff(c_287, plain, (![A_64, B_65, B_66]: (k2_xboole_0(k3_xboole_0(A_64, B_65), B_66)=B_66 | ~r1_xboole_0(A_64, B_65))), inference(resolution, [status(thm)], [c_223, c_16])).
% 3.00/1.47  tff(c_157, plain, (![A_45, B_46]: (k2_xboole_0(k3_xboole_0(A_45, B_46), k4_xboole_0(A_45, B_46))=A_45)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.00/1.47  tff(c_169, plain, (![B_4, A_3]: (k2_xboole_0(k3_xboole_0(B_4, A_3), k4_xboole_0(A_3, B_4))=A_3)), inference(superposition, [status(thm), theory('equality')], [c_4, c_157])).
% 3.00/1.47  tff(c_294, plain, (![B_65, A_64]: (k4_xboole_0(B_65, A_64)=B_65 | ~r1_xboole_0(A_64, B_65))), inference(superposition, [status(thm), theory('equality')], [c_287, c_169])).
% 3.00/1.47  tff(c_403, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_395, c_294])).
% 3.00/1.47  tff(c_20, plain, (![A_19, B_20, C_21]: (k4_xboole_0(k4_xboole_0(A_19, B_20), C_21)=k4_xboole_0(A_19, k2_xboole_0(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.00/1.47  tff(c_778, plain, (![C_80]: (k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', C_80))=k4_xboole_0('#skF_3', C_80))), inference(superposition, [status(thm), theory('equality')], [c_403, c_20])).
% 3.00/1.47  tff(c_796, plain, (![C_80]: (k4_xboole_0('#skF_3', k4_xboole_0('#skF_3', C_80))=k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', C_80)))), inference(superposition, [status(thm), theory('equality')], [c_778, c_22])).
% 3.00/1.47  tff(c_825, plain, (![C_80]: (k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', C_80))=k3_xboole_0('#skF_3', C_80))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_796])).
% 3.00/1.47  tff(c_26, plain, (k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))!=k3_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.00/1.47  tff(c_1067, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_825, c_26])).
% 3.00/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.47  
% 3.00/1.47  Inference rules
% 3.00/1.47  ----------------------
% 3.00/1.47  #Ref     : 0
% 3.00/1.47  #Sup     : 274
% 3.00/1.47  #Fact    : 0
% 3.00/1.47  #Define  : 0
% 3.00/1.47  #Split   : 2
% 3.00/1.47  #Chain   : 0
% 3.00/1.47  #Close   : 0
% 3.00/1.47  
% 3.00/1.47  Ordering : KBO
% 3.00/1.47  
% 3.00/1.47  Simplification rules
% 3.00/1.48  ----------------------
% 3.00/1.48  #Subsume      : 21
% 3.00/1.48  #Demod        : 143
% 3.00/1.48  #Tautology    : 126
% 3.00/1.48  #SimpNegUnit  : 1
% 3.00/1.48  #BackRed      : 2
% 3.00/1.48  
% 3.00/1.48  #Partial instantiations: 0
% 3.00/1.48  #Strategies tried      : 1
% 3.00/1.48  
% 3.00/1.48  Timing (in seconds)
% 3.00/1.48  ----------------------
% 3.00/1.48  Preprocessing        : 0.26
% 3.00/1.48  Parsing              : 0.14
% 3.00/1.48  CNF conversion       : 0.02
% 3.00/1.48  Main loop            : 0.41
% 3.00/1.48  Inferencing          : 0.14
% 3.00/1.48  Reduction            : 0.16
% 3.00/1.48  Demodulation         : 0.13
% 3.00/1.48  BG Simplification    : 0.02
% 3.00/1.48  Subsumption          : 0.07
% 3.00/1.48  Abstraction          : 0.02
% 3.00/1.48  MUC search           : 0.00
% 3.00/1.48  Cooper               : 0.00
% 3.00/1.48  Total                : 0.71
% 3.00/1.48  Index Insertion      : 0.00
% 3.00/1.48  Index Deletion       : 0.00
% 3.00/1.48  Index Matching       : 0.00
% 3.00/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
