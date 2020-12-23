%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:27 EST 2020

% Result     : Theorem 6.22s
% Output     : CNFRefutation 6.52s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 445 expanded)
%              Number of leaves         :   26 ( 159 expanded)
%              Depth                    :   10
%              Number of atoms          :   56 ( 746 expanded)
%              Number of equality atoms :   22 ( 354 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_60,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_58,plain,(
    ! [A_22] : k2_tarski(A_22,A_22) = k1_tarski(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_98,plain,(
    ! [D_35,B_36] : r2_hidden(D_35,k2_tarski(D_35,B_36)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_101,plain,(
    ! [A_22] : r2_hidden(A_22,k1_tarski(A_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_98])).

tff(c_66,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_223,plain,(
    ! [D_45,A_46,B_47] :
      ( ~ r2_hidden(D_45,A_46)
      | r2_hidden(D_45,k2_xboole_0(A_46,B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_242,plain,(
    ! [D_48] :
      ( ~ r2_hidden(D_48,k1_tarski('#skF_5'))
      | r2_hidden(D_48,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_223])).

tff(c_247,plain,(
    r2_hidden('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_101,c_242])).

tff(c_108,plain,(
    ! [B_40,A_41] : k2_xboole_0(B_40,A_41) = k2_xboole_0(A_41,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_130,plain,(
    ! [A_41] : k2_xboole_0(k1_xboole_0,A_41) = A_41 ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_34])).

tff(c_249,plain,(
    ! [D_50,A_51] :
      ( ~ r2_hidden(D_50,k1_xboole_0)
      | r2_hidden(D_50,A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_223])).

tff(c_255,plain,(
    ! [A_51] : r2_hidden('#skF_5',A_51) ),
    inference(resolution,[status(thm)],[c_247,c_249])).

tff(c_326,plain,(
    ! [D_61,B_62,A_63] :
      ( D_61 = B_62
      | D_61 = A_63
      | ~ r2_hidden(D_61,k2_tarski(A_63,B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_340,plain,(
    ! [B_62,A_63] :
      ( B_62 = '#skF_5'
      | A_63 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_255,c_326])).

tff(c_482,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_340])).

tff(c_346,plain,(
    ! [A_64] : A_64 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_340])).

tff(c_42,plain,(
    ! [D_21,A_16] : r2_hidden(D_21,k2_tarski(A_16,D_21)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_479,plain,(
    ! [D_1628] : r2_hidden(D_1628,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_42])).

tff(c_483,plain,(
    ! [D_1628] : r2_hidden(D_1628,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_482,c_479])).

tff(c_126,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_66])).

tff(c_229,plain,(
    ! [D_45] :
      ( ~ r2_hidden(D_45,'#skF_6')
      | r2_hidden(D_45,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_223])).

tff(c_254,plain,(
    ! [D_45,A_51] :
      ( r2_hidden(D_45,A_51)
      | ~ r2_hidden(D_45,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_229,c_249])).

tff(c_557,plain,(
    ! [D_45,A_51] : r2_hidden(D_45,A_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_483,c_254])).

tff(c_22,plain,(
    ! [A_9,C_11,B_10] :
      ( ~ r2_hidden(A_9,C_11)
      | ~ r2_hidden(A_9,B_10)
      | ~ r2_hidden(A_9,k5_xboole_0(B_10,C_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8960,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_557,c_557,c_557,c_22])).

tff(c_9151,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_340])).

tff(c_8962,plain,(
    ! [B_6606] : B_6606 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_340])).

tff(c_9148,plain,(
    ! [D_8259] : r2_hidden(D_8259,'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_8962,c_42])).

tff(c_9152,plain,(
    ! [D_8259] : r2_hidden(D_8259,'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_9151,c_9148])).

tff(c_9157,plain,(
    ! [D_45,A_51] : r2_hidden(D_45,A_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9152,c_254])).

tff(c_16773,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9157,c_9157,c_9157,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n021.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 20:06:04 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.22/2.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.22/2.29  
% 6.22/2.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.52/2.29  %$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 6.52/2.29  
% 6.52/2.29  %Foreground sorts:
% 6.52/2.29  
% 6.52/2.29  
% 6.52/2.29  %Background operators:
% 6.52/2.29  
% 6.52/2.29  
% 6.52/2.29  %Foreground operators:
% 6.52/2.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.52/2.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.52/2.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.52/2.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.52/2.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.52/2.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.52/2.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.52/2.29  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.52/2.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.52/2.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.52/2.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.52/2.29  tff('#skF_5', type, '#skF_5': $i).
% 6.52/2.29  tff('#skF_6', type, '#skF_6': $i).
% 6.52/2.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.52/2.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.52/2.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.52/2.29  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.52/2.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.52/2.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.52/2.29  
% 6.52/2.31  tff(f_60, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.52/2.31  tff(f_58, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 6.52/2.31  tff(f_70, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 6.52/2.31  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 6.52/2.31  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.52/2.31  tff(f_45, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 6.52/2.31  tff(f_43, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 6.52/2.31  tff(c_58, plain, (![A_22]: (k2_tarski(A_22, A_22)=k1_tarski(A_22))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.52/2.31  tff(c_98, plain, (![D_35, B_36]: (r2_hidden(D_35, k2_tarski(D_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.52/2.31  tff(c_101, plain, (![A_22]: (r2_hidden(A_22, k1_tarski(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_98])).
% 6.52/2.31  tff(c_66, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.52/2.31  tff(c_223, plain, (![D_45, A_46, B_47]: (~r2_hidden(D_45, A_46) | r2_hidden(D_45, k2_xboole_0(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.52/2.31  tff(c_242, plain, (![D_48]: (~r2_hidden(D_48, k1_tarski('#skF_5')) | r2_hidden(D_48, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_66, c_223])).
% 6.52/2.31  tff(c_247, plain, (r2_hidden('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_101, c_242])).
% 6.52/2.31  tff(c_108, plain, (![B_40, A_41]: (k2_xboole_0(B_40, A_41)=k2_xboole_0(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.52/2.31  tff(c_34, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.52/2.31  tff(c_130, plain, (![A_41]: (k2_xboole_0(k1_xboole_0, A_41)=A_41)), inference(superposition, [status(thm), theory('equality')], [c_108, c_34])).
% 6.52/2.31  tff(c_249, plain, (![D_50, A_51]: (~r2_hidden(D_50, k1_xboole_0) | r2_hidden(D_50, A_51))), inference(superposition, [status(thm), theory('equality')], [c_130, c_223])).
% 6.52/2.31  tff(c_255, plain, (![A_51]: (r2_hidden('#skF_5', A_51))), inference(resolution, [status(thm)], [c_247, c_249])).
% 6.52/2.31  tff(c_326, plain, (![D_61, B_62, A_63]: (D_61=B_62 | D_61=A_63 | ~r2_hidden(D_61, k2_tarski(A_63, B_62)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.52/2.31  tff(c_340, plain, (![B_62, A_63]: (B_62='#skF_5' | A_63='#skF_5')), inference(resolution, [status(thm)], [c_255, c_326])).
% 6.52/2.31  tff(c_482, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_340])).
% 6.52/2.31  tff(c_346, plain, (![A_64]: (A_64='#skF_5')), inference(splitLeft, [status(thm)], [c_340])).
% 6.52/2.31  tff(c_42, plain, (![D_21, A_16]: (r2_hidden(D_21, k2_tarski(A_16, D_21)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.52/2.31  tff(c_479, plain, (![D_1628]: (r2_hidden(D_1628, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_346, c_42])).
% 6.52/2.31  tff(c_483, plain, (![D_1628]: (r2_hidden(D_1628, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_482, c_479])).
% 6.52/2.31  tff(c_126, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_108, c_66])).
% 6.52/2.31  tff(c_229, plain, (![D_45]: (~r2_hidden(D_45, '#skF_6') | r2_hidden(D_45, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_126, c_223])).
% 6.52/2.31  tff(c_254, plain, (![D_45, A_51]: (r2_hidden(D_45, A_51) | ~r2_hidden(D_45, '#skF_6'))), inference(resolution, [status(thm)], [c_229, c_249])).
% 6.52/2.31  tff(c_557, plain, (![D_45, A_51]: (r2_hidden(D_45, A_51))), inference(demodulation, [status(thm), theory('equality')], [c_483, c_254])).
% 6.52/2.31  tff(c_22, plain, (![A_9, C_11, B_10]: (~r2_hidden(A_9, C_11) | ~r2_hidden(A_9, B_10) | ~r2_hidden(A_9, k5_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.52/2.31  tff(c_8960, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_557, c_557, c_557, c_22])).
% 6.52/2.31  tff(c_9151, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_340])).
% 6.52/2.31  tff(c_8962, plain, (![B_6606]: (B_6606='#skF_5')), inference(splitRight, [status(thm)], [c_340])).
% 6.52/2.31  tff(c_9148, plain, (![D_8259]: (r2_hidden(D_8259, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_8962, c_42])).
% 6.52/2.31  tff(c_9152, plain, (![D_8259]: (r2_hidden(D_8259, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_9151, c_9148])).
% 6.52/2.31  tff(c_9157, plain, (![D_45, A_51]: (r2_hidden(D_45, A_51))), inference(demodulation, [status(thm), theory('equality')], [c_9152, c_254])).
% 6.52/2.31  tff(c_16773, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9157, c_9157, c_9157, c_22])).
% 6.52/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.52/2.31  
% 6.52/2.31  Inference rules
% 6.52/2.31  ----------------------
% 6.52/2.31  #Ref     : 0
% 6.52/2.31  #Sup     : 2976
% 6.52/2.31  #Fact    : 16
% 6.52/2.31  #Define  : 0
% 6.52/2.31  #Split   : 1
% 6.52/2.31  #Chain   : 0
% 6.52/2.31  #Close   : 0
% 6.52/2.31  
% 6.52/2.31  Ordering : KBO
% 6.52/2.31  
% 6.52/2.31  Simplification rules
% 6.52/2.31  ----------------------
% 6.52/2.31  #Subsume      : 2509
% 6.52/2.31  #Demod        : 1282
% 6.52/2.31  #Tautology    : 230
% 6.52/2.31  #SimpNegUnit  : 0
% 6.52/2.31  #BackRed      : 15
% 6.52/2.31  
% 6.52/2.31  #Partial instantiations: 3146
% 6.52/2.31  #Strategies tried      : 1
% 6.52/2.31  
% 6.52/2.31  Timing (in seconds)
% 6.52/2.31  ----------------------
% 6.52/2.32  Preprocessing        : 0.34
% 6.52/2.32  Parsing              : 0.17
% 6.52/2.32  CNF conversion       : 0.03
% 6.52/2.32  Main loop            : 1.21
% 6.52/2.32  Inferencing          : 0.52
% 6.52/2.32  Reduction            : 0.42
% 6.52/2.32  Demodulation         : 0.33
% 6.52/2.32  BG Simplification    : 0.03
% 6.52/2.32  Subsumption          : 0.19
% 6.52/2.32  Abstraction          : 0.09
% 6.52/2.32  MUC search           : 0.00
% 6.52/2.32  Cooper               : 0.00
% 6.52/2.32  Total                : 1.59
% 6.52/2.32  Index Insertion      : 0.00
% 6.52/2.32  Index Deletion       : 0.00
% 6.52/2.32  Index Matching       : 0.00
% 6.52/2.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
