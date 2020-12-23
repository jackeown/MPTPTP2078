%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:44 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 114 expanded)
%              Number of leaves         :   28 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :   51 ( 149 expanded)
%              Number of equality atoms :   23 (  82 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_61,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_65,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_52,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_73,plain,(
    ! [B_40,A_41] : k2_xboole_0(B_40,A_41) = k2_xboole_0(A_41,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_112,plain,(
    k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_73])).

tff(c_24,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k2_xboole_0(A_15,B_16)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_131,plain,(
    k4_xboole_0('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_24])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | k4_xboole_0(A_10,B_11) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_22,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_373,plain,(
    ! [B_59,A_60] :
      ( B_59 = A_60
      | ~ r1_tarski(B_59,A_60)
      | ~ r1_tarski(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_386,plain,(
    ! [A_61] :
      ( k1_xboole_0 = A_61
      | ~ r1_tarski(A_61,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_373])).

tff(c_404,plain,(
    ! [A_62] :
      ( k1_xboole_0 = A_62
      | k4_xboole_0(A_62,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_16,c_386])).

tff(c_423,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_404])).

tff(c_63,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k2_xboole_0(A_38,B_39)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_70,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_63])).

tff(c_424,plain,(
    k2_tarski('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_404])).

tff(c_471,plain,(
    k2_tarski('#skF_4','#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_424])).

tff(c_32,plain,(
    ! [D_23,B_19] : r2_hidden(D_23,k2_tarski(D_23,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_483,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_32])).

tff(c_26,plain,(
    ! [A_17] : r1_xboole_0(A_17,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_441,plain,(
    ! [A_17] : r1_xboole_0(A_17,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_26])).

tff(c_811,plain,(
    ! [A_90,B_91,C_92] :
      ( ~ r1_xboole_0(A_90,B_91)
      | ~ r2_hidden(C_92,B_91)
      | ~ r2_hidden(C_92,A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_815,plain,(
    ! [C_93,A_94] :
      ( ~ r2_hidden(C_93,'#skF_6')
      | ~ r2_hidden(C_93,A_94) ) ),
    inference(resolution,[status(thm)],[c_441,c_811])).

tff(c_827,plain,(
    ! [A_94] : ~ r2_hidden('#skF_4',A_94) ),
    inference(resolution,[status(thm)],[c_483,c_815])).

tff(c_832,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_827,c_483])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:33:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.64/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.40  
% 2.64/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.40  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.64/1.40  
% 2.64/1.40  %Foreground sorts:
% 2.64/1.40  
% 2.64/1.40  
% 2.64/1.40  %Background operators:
% 2.64/1.40  
% 2.64/1.40  
% 2.64/1.40  %Foreground operators:
% 2.64/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.64/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.64/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.64/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.64/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.64/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.64/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.64/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.64/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.64/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.64/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.64/1.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.64/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.64/1.40  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.64/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.64/1.40  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.64/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.64/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.64/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.64/1.40  
% 2.64/1.41  tff(f_84, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.64/1.41  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.64/1.41  tff(f_63, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.64/1.41  tff(f_55, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.64/1.41  tff(f_61, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.64/1.41  tff(f_51, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.64/1.41  tff(f_74, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.64/1.41  tff(f_65, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.64/1.41  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.64/1.41  tff(c_52, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.64/1.41  tff(c_73, plain, (![B_40, A_41]: (k2_xboole_0(B_40, A_41)=k2_xboole_0(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.64/1.41  tff(c_112, plain, (k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_52, c_73])).
% 2.64/1.41  tff(c_24, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k2_xboole_0(A_15, B_16))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.64/1.41  tff(c_131, plain, (k4_xboole_0('#skF_6', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_112, c_24])).
% 2.64/1.41  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | k4_xboole_0(A_10, B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.64/1.41  tff(c_22, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.64/1.41  tff(c_373, plain, (![B_59, A_60]: (B_59=A_60 | ~r1_tarski(B_59, A_60) | ~r1_tarski(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.64/1.41  tff(c_386, plain, (![A_61]: (k1_xboole_0=A_61 | ~r1_tarski(A_61, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_373])).
% 2.64/1.41  tff(c_404, plain, (![A_62]: (k1_xboole_0=A_62 | k4_xboole_0(A_62, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_386])).
% 2.64/1.41  tff(c_423, plain, (k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_131, c_404])).
% 2.64/1.41  tff(c_63, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k2_xboole_0(A_38, B_39))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.64/1.41  tff(c_70, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_52, c_63])).
% 2.64/1.41  tff(c_424, plain, (k2_tarski('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_70, c_404])).
% 2.64/1.41  tff(c_471, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_423, c_424])).
% 2.64/1.41  tff(c_32, plain, (![D_23, B_19]: (r2_hidden(D_23, k2_tarski(D_23, B_19)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.64/1.41  tff(c_483, plain, (r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_471, c_32])).
% 2.64/1.41  tff(c_26, plain, (![A_17]: (r1_xboole_0(A_17, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.64/1.41  tff(c_441, plain, (![A_17]: (r1_xboole_0(A_17, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_423, c_26])).
% 2.64/1.41  tff(c_811, plain, (![A_90, B_91, C_92]: (~r1_xboole_0(A_90, B_91) | ~r2_hidden(C_92, B_91) | ~r2_hidden(C_92, A_90))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.64/1.41  tff(c_815, plain, (![C_93, A_94]: (~r2_hidden(C_93, '#skF_6') | ~r2_hidden(C_93, A_94))), inference(resolution, [status(thm)], [c_441, c_811])).
% 2.64/1.41  tff(c_827, plain, (![A_94]: (~r2_hidden('#skF_4', A_94))), inference(resolution, [status(thm)], [c_483, c_815])).
% 2.64/1.41  tff(c_832, plain, $false, inference(negUnitSimplification, [status(thm)], [c_827, c_483])).
% 2.64/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.41  
% 2.64/1.41  Inference rules
% 2.64/1.41  ----------------------
% 2.64/1.41  #Ref     : 0
% 2.64/1.41  #Sup     : 185
% 2.64/1.41  #Fact    : 0
% 2.64/1.41  #Define  : 0
% 2.64/1.41  #Split   : 0
% 2.64/1.41  #Chain   : 0
% 2.64/1.41  #Close   : 0
% 2.64/1.41  
% 2.64/1.41  Ordering : KBO
% 2.64/1.41  
% 2.64/1.41  Simplification rules
% 2.64/1.41  ----------------------
% 2.64/1.41  #Subsume      : 2
% 2.64/1.41  #Demod        : 84
% 2.64/1.41  #Tautology    : 158
% 2.64/1.41  #SimpNegUnit  : 1
% 2.64/1.41  #BackRed      : 18
% 2.64/1.41  
% 2.64/1.41  #Partial instantiations: 0
% 2.64/1.41  #Strategies tried      : 1
% 2.64/1.41  
% 2.64/1.41  Timing (in seconds)
% 2.64/1.41  ----------------------
% 2.64/1.41  Preprocessing        : 0.33
% 2.64/1.41  Parsing              : 0.18
% 2.64/1.41  CNF conversion       : 0.02
% 2.64/1.41  Main loop            : 0.29
% 2.64/1.41  Inferencing          : 0.10
% 2.64/1.41  Reduction            : 0.10
% 2.64/1.41  Demodulation         : 0.08
% 2.64/1.41  BG Simplification    : 0.02
% 2.64/1.41  Subsumption          : 0.05
% 2.64/1.41  Abstraction          : 0.02
% 2.64/1.42  MUC search           : 0.00
% 2.64/1.42  Cooper               : 0.00
% 2.64/1.42  Total                : 0.65
% 2.64/1.42  Index Insertion      : 0.00
% 2.64/1.42  Index Deletion       : 0.00
% 2.64/1.42  Index Matching       : 0.00
% 2.64/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
