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
% DateTime   : Thu Dec  3 09:49:45 EST 2020

% Result     : Theorem 9.89s
% Output     : CNFRefutation 10.03s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 212 expanded)
%              Number of leaves         :   21 (  81 expanded)
%              Depth                    :   16
%              Number of atoms          :   78 ( 388 expanded)
%              Number of equality atoms :   32 ( 212 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_38,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A] : k1_enumset1(A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_53,negated_conjecture,(
    ~ ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(c_56,plain,(
    ! [A_37,B_38] : k1_enumset1(A_37,A_37,B_38) = k2_tarski(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_24,plain,(
    ! [A_12] : k1_enumset1(A_12,A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_83,plain,(
    ! [B_42] : k2_tarski(B_42,B_42) = k1_tarski(B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_24])).

tff(c_4,plain,(
    ! [D_6,A_1] : r2_hidden(D_6,k2_tarski(A_1,D_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_92,plain,(
    ! [B_42] : r2_hidden(B_42,k1_tarski(B_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_4])).

tff(c_44,plain,(
    k3_tarski(k1_tarski('#skF_7')) != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_40,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_4'(A_13,B_14),A_13)
      | r2_hidden('#skF_5'(A_13,B_14),B_14)
      | k3_tarski(A_13) = B_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1001,plain,(
    ! [A_145,B_146,D_147] :
      ( r2_hidden('#skF_4'(A_145,B_146),A_145)
      | ~ r2_hidden(D_147,A_145)
      | ~ r2_hidden('#skF_5'(A_145,B_146),D_147)
      | k3_tarski(A_145) = B_146 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1105,plain,(
    ! [B_148,A_149] :
      ( ~ r2_hidden(B_148,A_149)
      | r2_hidden('#skF_4'(A_149,B_148),A_149)
      | k3_tarski(A_149) = B_148 ) ),
    inference(resolution,[status(thm)],[c_40,c_1001])).

tff(c_2,plain,(
    ! [D_6,B_2,A_1] :
      ( D_6 = B_2
      | D_6 = A_1
      | ~ r2_hidden(D_6,k2_tarski(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_89,plain,(
    ! [D_6,B_42] :
      ( D_6 = B_42
      | D_6 = B_42
      | ~ r2_hidden(D_6,k1_tarski(B_42)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_2])).

tff(c_9356,plain,(
    ! [B_5738,B_5739] :
      ( '#skF_4'(k1_tarski(B_5738),B_5739) = B_5738
      | ~ r2_hidden(B_5739,k1_tarski(B_5738))
      | k3_tarski(k1_tarski(B_5738)) = B_5739 ) ),
    inference(resolution,[status(thm)],[c_1105,c_89])).

tff(c_9466,plain,(
    ! [B_5887] :
      ( '#skF_4'(k1_tarski(B_5887),B_5887) = B_5887
      | k3_tarski(k1_tarski(B_5887)) = B_5887 ) ),
    inference(resolution,[status(thm)],[c_92,c_9356])).

tff(c_9590,plain,(
    '#skF_4'(k1_tarski('#skF_7'),'#skF_7') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_9466,c_44])).

tff(c_42,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_3'(A_13,B_14),'#skF_4'(A_13,B_14))
      | r2_hidden('#skF_5'(A_13,B_14),B_14)
      | k3_tarski(A_13) = B_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_9600,plain,
    ( r2_hidden('#skF_3'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7')
    | r2_hidden('#skF_5'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7')
    | k3_tarski(k1_tarski('#skF_7')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_9590,c_42])).

tff(c_9637,plain,
    ( r2_hidden('#skF_3'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7')
    | r2_hidden('#skF_5'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_9600])).

tff(c_9641,plain,(
    r2_hidden('#skF_5'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_9637])).

tff(c_36,plain,(
    ! [A_13,B_14,D_27] :
      ( r2_hidden('#skF_3'(A_13,B_14),'#skF_4'(A_13,B_14))
      | ~ r2_hidden(D_27,A_13)
      | ~ r2_hidden('#skF_5'(A_13,B_14),D_27)
      | k3_tarski(A_13) = B_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_9643,plain,
    ( r2_hidden('#skF_3'(k1_tarski('#skF_7'),'#skF_7'),'#skF_4'(k1_tarski('#skF_7'),'#skF_7'))
    | ~ r2_hidden('#skF_7',k1_tarski('#skF_7'))
    | k3_tarski(k1_tarski('#skF_7')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_9641,c_36])).

tff(c_9683,plain,
    ( r2_hidden('#skF_3'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7')
    | k3_tarski(k1_tarski('#skF_7')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_9590,c_9643])).

tff(c_9684,plain,(
    r2_hidden('#skF_3'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_9683])).

tff(c_32,plain,(
    ! [A_13,B_14,D_27] :
      ( ~ r2_hidden('#skF_3'(A_13,B_14),B_14)
      | ~ r2_hidden(D_27,A_13)
      | ~ r2_hidden('#skF_5'(A_13,B_14),D_27)
      | k3_tarski(A_13) = B_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_9694,plain,(
    ! [D_27] :
      ( ~ r2_hidden(D_27,k1_tarski('#skF_7'))
      | ~ r2_hidden('#skF_5'(k1_tarski('#skF_7'),'#skF_7'),D_27)
      | k3_tarski(k1_tarski('#skF_7')) = '#skF_7' ) ),
    inference(resolution,[status(thm)],[c_9684,c_32])).

tff(c_9865,plain,(
    ! [D_6397] :
      ( ~ r2_hidden(D_6397,k1_tarski('#skF_7'))
      | ~ r2_hidden('#skF_5'(k1_tarski('#skF_7'),'#skF_7'),D_6397) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_9694])).

tff(c_9868,plain,(
    ~ r2_hidden('#skF_7',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_9641,c_9865])).

tff(c_10035,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_9868])).

tff(c_10037,plain,(
    ~ r2_hidden('#skF_5'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_9637])).

tff(c_10036,plain,(
    r2_hidden('#skF_3'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_9637])).

tff(c_38,plain,(
    ! [A_13,B_14] :
      ( ~ r2_hidden('#skF_3'(A_13,B_14),B_14)
      | r2_hidden('#skF_5'(A_13,B_14),B_14)
      | k3_tarski(A_13) = B_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10046,plain,
    ( r2_hidden('#skF_5'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7')
    | k3_tarski(k1_tarski('#skF_7')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_10036,c_38])).

tff(c_10085,plain,(
    r2_hidden('#skF_5'(k1_tarski('#skF_7'),'#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_10046])).

tff(c_10097,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10037,c_10085])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:57:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.89/3.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.89/3.40  
% 9.89/3.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.89/3.41  %$ r2_hidden > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_2 > #skF_5 > #skF_4
% 9.89/3.41  
% 9.89/3.41  %Foreground sorts:
% 9.89/3.41  
% 9.89/3.41  
% 9.89/3.41  %Background operators:
% 9.89/3.41  
% 9.89/3.41  
% 9.89/3.41  %Foreground operators:
% 9.89/3.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 9.89/3.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.89/3.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.89/3.41  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 9.89/3.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.89/3.41  tff('#skF_7', type, '#skF_7': $i).
% 9.89/3.41  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.89/3.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.89/3.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.89/3.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.89/3.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.89/3.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.89/3.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.89/3.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.89/3.41  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 9.89/3.41  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.89/3.41  
% 10.03/3.43  tff(f_38, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 10.03/3.43  tff(f_40, axiom, (![A]: (k1_enumset1(A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_enumset1)).
% 10.03/3.43  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 10.03/3.43  tff(f_53, negated_conjecture, ~(![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 10.03/3.43  tff(f_50, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 10.03/3.43  tff(c_56, plain, (![A_37, B_38]: (k1_enumset1(A_37, A_37, B_38)=k2_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.03/3.43  tff(c_24, plain, (![A_12]: (k1_enumset1(A_12, A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_40])).
% 10.03/3.43  tff(c_83, plain, (![B_42]: (k2_tarski(B_42, B_42)=k1_tarski(B_42))), inference(superposition, [status(thm), theory('equality')], [c_56, c_24])).
% 10.03/3.43  tff(c_4, plain, (![D_6, A_1]: (r2_hidden(D_6, k2_tarski(A_1, D_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.03/3.43  tff(c_92, plain, (![B_42]: (r2_hidden(B_42, k1_tarski(B_42)))), inference(superposition, [status(thm), theory('equality')], [c_83, c_4])).
% 10.03/3.43  tff(c_44, plain, (k3_tarski(k1_tarski('#skF_7'))!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.03/3.43  tff(c_40, plain, (![A_13, B_14]: (r2_hidden('#skF_4'(A_13, B_14), A_13) | r2_hidden('#skF_5'(A_13, B_14), B_14) | k3_tarski(A_13)=B_14)), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.03/3.43  tff(c_1001, plain, (![A_145, B_146, D_147]: (r2_hidden('#skF_4'(A_145, B_146), A_145) | ~r2_hidden(D_147, A_145) | ~r2_hidden('#skF_5'(A_145, B_146), D_147) | k3_tarski(A_145)=B_146)), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.03/3.43  tff(c_1105, plain, (![B_148, A_149]: (~r2_hidden(B_148, A_149) | r2_hidden('#skF_4'(A_149, B_148), A_149) | k3_tarski(A_149)=B_148)), inference(resolution, [status(thm)], [c_40, c_1001])).
% 10.03/3.43  tff(c_2, plain, (![D_6, B_2, A_1]: (D_6=B_2 | D_6=A_1 | ~r2_hidden(D_6, k2_tarski(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 10.03/3.43  tff(c_89, plain, (![D_6, B_42]: (D_6=B_42 | D_6=B_42 | ~r2_hidden(D_6, k1_tarski(B_42)))), inference(superposition, [status(thm), theory('equality')], [c_83, c_2])).
% 10.03/3.43  tff(c_9356, plain, (![B_5738, B_5739]: ('#skF_4'(k1_tarski(B_5738), B_5739)=B_5738 | ~r2_hidden(B_5739, k1_tarski(B_5738)) | k3_tarski(k1_tarski(B_5738))=B_5739)), inference(resolution, [status(thm)], [c_1105, c_89])).
% 10.03/3.43  tff(c_9466, plain, (![B_5887]: ('#skF_4'(k1_tarski(B_5887), B_5887)=B_5887 | k3_tarski(k1_tarski(B_5887))=B_5887)), inference(resolution, [status(thm)], [c_92, c_9356])).
% 10.03/3.43  tff(c_9590, plain, ('#skF_4'(k1_tarski('#skF_7'), '#skF_7')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_9466, c_44])).
% 10.03/3.43  tff(c_42, plain, (![A_13, B_14]: (r2_hidden('#skF_3'(A_13, B_14), '#skF_4'(A_13, B_14)) | r2_hidden('#skF_5'(A_13, B_14), B_14) | k3_tarski(A_13)=B_14)), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.03/3.43  tff(c_9600, plain, (r2_hidden('#skF_3'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7') | r2_hidden('#skF_5'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7') | k3_tarski(k1_tarski('#skF_7'))='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_9590, c_42])).
% 10.03/3.43  tff(c_9637, plain, (r2_hidden('#skF_3'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7') | r2_hidden('#skF_5'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_44, c_9600])).
% 10.03/3.43  tff(c_9641, plain, (r2_hidden('#skF_5'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7')), inference(splitLeft, [status(thm)], [c_9637])).
% 10.03/3.43  tff(c_36, plain, (![A_13, B_14, D_27]: (r2_hidden('#skF_3'(A_13, B_14), '#skF_4'(A_13, B_14)) | ~r2_hidden(D_27, A_13) | ~r2_hidden('#skF_5'(A_13, B_14), D_27) | k3_tarski(A_13)=B_14)), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.03/3.43  tff(c_9643, plain, (r2_hidden('#skF_3'(k1_tarski('#skF_7'), '#skF_7'), '#skF_4'(k1_tarski('#skF_7'), '#skF_7')) | ~r2_hidden('#skF_7', k1_tarski('#skF_7')) | k3_tarski(k1_tarski('#skF_7'))='#skF_7'), inference(resolution, [status(thm)], [c_9641, c_36])).
% 10.03/3.43  tff(c_9683, plain, (r2_hidden('#skF_3'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7') | k3_tarski(k1_tarski('#skF_7'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_9590, c_9643])).
% 10.03/3.43  tff(c_9684, plain, (r2_hidden('#skF_3'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_44, c_9683])).
% 10.03/3.43  tff(c_32, plain, (![A_13, B_14, D_27]: (~r2_hidden('#skF_3'(A_13, B_14), B_14) | ~r2_hidden(D_27, A_13) | ~r2_hidden('#skF_5'(A_13, B_14), D_27) | k3_tarski(A_13)=B_14)), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.03/3.43  tff(c_9694, plain, (![D_27]: (~r2_hidden(D_27, k1_tarski('#skF_7')) | ~r2_hidden('#skF_5'(k1_tarski('#skF_7'), '#skF_7'), D_27) | k3_tarski(k1_tarski('#skF_7'))='#skF_7')), inference(resolution, [status(thm)], [c_9684, c_32])).
% 10.03/3.43  tff(c_9865, plain, (![D_6397]: (~r2_hidden(D_6397, k1_tarski('#skF_7')) | ~r2_hidden('#skF_5'(k1_tarski('#skF_7'), '#skF_7'), D_6397))), inference(negUnitSimplification, [status(thm)], [c_44, c_9694])).
% 10.03/3.43  tff(c_9868, plain, (~r2_hidden('#skF_7', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_9641, c_9865])).
% 10.03/3.43  tff(c_10035, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_9868])).
% 10.03/3.43  tff(c_10037, plain, (~r2_hidden('#skF_5'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7')), inference(splitRight, [status(thm)], [c_9637])).
% 10.03/3.43  tff(c_10036, plain, (r2_hidden('#skF_3'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7')), inference(splitRight, [status(thm)], [c_9637])).
% 10.03/3.43  tff(c_38, plain, (![A_13, B_14]: (~r2_hidden('#skF_3'(A_13, B_14), B_14) | r2_hidden('#skF_5'(A_13, B_14), B_14) | k3_tarski(A_13)=B_14)), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.03/3.43  tff(c_10046, plain, (r2_hidden('#skF_5'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7') | k3_tarski(k1_tarski('#skF_7'))='#skF_7'), inference(resolution, [status(thm)], [c_10036, c_38])).
% 10.03/3.43  tff(c_10085, plain, (r2_hidden('#skF_5'(k1_tarski('#skF_7'), '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_44, c_10046])).
% 10.03/3.43  tff(c_10097, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10037, c_10085])).
% 10.03/3.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.03/3.43  
% 10.03/3.43  Inference rules
% 10.03/3.43  ----------------------
% 10.03/3.43  #Ref     : 0
% 10.03/3.43  #Sup     : 965
% 10.03/3.43  #Fact    : 4
% 10.03/3.43  #Define  : 0
% 10.03/3.43  #Split   : 1
% 10.03/3.43  #Chain   : 0
% 10.03/3.43  #Close   : 0
% 10.03/3.43  
% 10.03/3.43  Ordering : KBO
% 10.03/3.43  
% 10.03/3.43  Simplification rules
% 10.03/3.43  ----------------------
% 10.03/3.43  #Subsume      : 32
% 10.03/3.43  #Demod        : 79
% 10.03/3.43  #Tautology    : 102
% 10.03/3.43  #SimpNegUnit  : 10
% 10.03/3.43  #BackRed      : 0
% 10.03/3.43  
% 10.03/3.43  #Partial instantiations: 3168
% 10.03/3.43  #Strategies tried      : 1
% 10.03/3.43  
% 10.03/3.43  Timing (in seconds)
% 10.03/3.43  ----------------------
% 10.03/3.43  Preprocessing        : 0.51
% 10.03/3.43  Parsing              : 0.24
% 10.03/3.43  CNF conversion       : 0.04
% 10.03/3.43  Main loop            : 2.18
% 10.03/3.43  Inferencing          : 1.02
% 10.03/3.43  Reduction            : 0.52
% 10.03/3.43  Demodulation         : 0.40
% 10.03/3.43  BG Simplification    : 0.08
% 10.03/3.43  Subsumption          : 0.43
% 10.03/3.43  Abstraction          : 0.09
% 10.03/3.43  MUC search           : 0.00
% 10.03/3.43  Cooper               : 0.00
% 10.03/3.43  Total                : 2.73
% 10.03/3.43  Index Insertion      : 0.00
% 10.03/3.43  Index Deletion       : 0.00
% 10.03/3.43  Index Matching       : 0.00
% 10.03/3.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
