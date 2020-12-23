%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:12 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 118 expanded)
%              Number of leaves         :   31 (  56 expanded)
%              Depth                    :    7
%              Number of atoms          :   71 ( 160 expanded)
%              Number of equality atoms :   58 ( 134 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_75,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_332,plain,(
    ! [A_79,B_80] : k4_xboole_0(A_79,k2_xboole_0(A_79,B_80)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_339,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_332])).

tff(c_30,plain,(
    ! [B_23] : k4_xboole_0(k1_tarski(B_23),k1_tarski(B_23)) != k1_tarski(B_23) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_413,plain,(
    ! [B_23] : k1_tarski(B_23) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_30])).

tff(c_40,plain,(
    ! [A_28] :
      ( r2_hidden('#skF_3'(A_28),A_28)
      | k1_xboole_0 = A_28 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_349,plain,(
    ! [C_82,A_83] :
      ( C_82 = A_83
      | ~ r2_hidden(C_82,k1_tarski(A_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_357,plain,(
    ! [A_83] :
      ( '#skF_3'(k1_tarski(A_83)) = A_83
      | k1_tarski(A_83) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_349])).

tff(c_435,plain,(
    ! [A_83] : '#skF_3'(k1_tarski(A_83)) = A_83 ),
    inference(negUnitSimplification,[status(thm)],[c_413,c_357])).

tff(c_12,plain,(
    ! [C_13] : r2_hidden(C_13,k1_tarski(C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_494,plain,(
    ! [D_107,A_108,C_109] :
      ( ~ r2_hidden(D_107,A_108)
      | k4_tarski(C_109,D_107) != '#skF_3'(A_108)
      | k1_xboole_0 = A_108 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_498,plain,(
    ! [C_109,C_13] :
      ( k4_tarski(C_109,C_13) != '#skF_3'(k1_tarski(C_13))
      | k1_tarski(C_13) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_494])).

tff(c_501,plain,(
    ! [C_109,C_13] :
      ( k4_tarski(C_109,C_13) != C_13
      | k1_tarski(C_13) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_498])).

tff(c_502,plain,(
    ! [C_109,C_13] : k4_tarski(C_109,C_13) != C_13 ),
    inference(negUnitSimplification,[status(thm)],[c_413,c_501])).

tff(c_149,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k2_xboole_0(A_51,B_52)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_156,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_149])).

tff(c_219,plain,(
    ! [B_23] : k1_tarski(B_23) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_30])).

tff(c_143,plain,(
    ! [A_50] :
      ( r2_hidden('#skF_3'(A_50),A_50)
      | k1_xboole_0 = A_50 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_10,plain,(
    ! [C_13,A_9] :
      ( C_13 = A_9
      | ~ r2_hidden(C_13,k1_tarski(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_148,plain,(
    ! [A_9] :
      ( '#skF_3'(k1_tarski(A_9)) = A_9
      | k1_tarski(A_9) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_143,c_10])).

tff(c_221,plain,(
    ! [A_9] : '#skF_3'(k1_tarski(A_9)) = A_9 ),
    inference(negUnitSimplification,[status(thm)],[c_219,c_148])).

tff(c_287,plain,(
    ! [C_72,A_73,D_74] :
      ( ~ r2_hidden(C_72,A_73)
      | k4_tarski(C_72,D_74) != '#skF_3'(A_73)
      | k1_xboole_0 = A_73 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_291,plain,(
    ! [C_13,D_74] :
      ( k4_tarski(C_13,D_74) != '#skF_3'(k1_tarski(C_13))
      | k1_tarski(C_13) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_12,c_287])).

tff(c_294,plain,(
    ! [C_13,D_74] :
      ( k4_tarski(C_13,D_74) != C_13
      | k1_tarski(C_13) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_291])).

tff(c_295,plain,(
    ! [C_13,D_74] : k4_tarski(C_13,D_74) != C_13 ),
    inference(negUnitSimplification,[status(thm)],[c_219,c_294])).

tff(c_48,plain,(
    k4_tarski('#skF_5','#skF_6') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_84,plain,(
    ! [A_45,B_46] : k1_mcart_1(k4_tarski(A_45,B_46)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_93,plain,(
    k1_mcart_1('#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_84])).

tff(c_72,plain,(
    ! [A_43,B_44] : k2_mcart_1(k4_tarski(A_43,B_44)) = B_44 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_81,plain,(
    k2_mcart_1('#skF_4') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_72])).

tff(c_46,plain,
    ( k2_mcart_1('#skF_4') = '#skF_4'
    | k1_mcart_1('#skF_4') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_113,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_81,c_46])).

tff(c_114,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_116,plain,(
    k4_tarski('#skF_4','#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_48])).

tff(c_306,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_295,c_116])).

tff(c_307,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_310,plain,(
    k4_tarski('#skF_5','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_48])).

tff(c_504,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_502,c_310])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:51:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.40  
% 2.31/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.40  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.31/1.40  
% 2.31/1.40  %Foreground sorts:
% 2.31/1.40  
% 2.31/1.40  
% 2.31/1.40  %Background operators:
% 2.31/1.40  
% 2.31/1.40  
% 2.31/1.40  %Foreground operators:
% 2.31/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.31/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.31/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.31/1.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.31/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.31/1.40  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.31/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.31/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.31/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.31/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.31/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.31/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.40  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.31/1.40  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.31/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.31/1.40  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.31/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.31/1.40  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.31/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.31/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.31/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.31/1.40  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.31/1.40  
% 2.31/1.41  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.31/1.41  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.31/1.41  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.31/1.41  tff(f_75, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 2.31/1.41  tff(f_40, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.31/1.41  tff(f_85, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.31/1.41  tff(f_59, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.31/1.41  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.31/1.41  tff(c_332, plain, (![A_79, B_80]: (k4_xboole_0(A_79, k2_xboole_0(A_79, B_80))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.31/1.41  tff(c_339, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_332])).
% 2.31/1.41  tff(c_30, plain, (![B_23]: (k4_xboole_0(k1_tarski(B_23), k1_tarski(B_23))!=k1_tarski(B_23))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.31/1.41  tff(c_413, plain, (![B_23]: (k1_tarski(B_23)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_339, c_30])).
% 2.31/1.41  tff(c_40, plain, (![A_28]: (r2_hidden('#skF_3'(A_28), A_28) | k1_xboole_0=A_28)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.31/1.41  tff(c_349, plain, (![C_82, A_83]: (C_82=A_83 | ~r2_hidden(C_82, k1_tarski(A_83)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.31/1.41  tff(c_357, plain, (![A_83]: ('#skF_3'(k1_tarski(A_83))=A_83 | k1_tarski(A_83)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_349])).
% 2.31/1.41  tff(c_435, plain, (![A_83]: ('#skF_3'(k1_tarski(A_83))=A_83)), inference(negUnitSimplification, [status(thm)], [c_413, c_357])).
% 2.31/1.41  tff(c_12, plain, (![C_13]: (r2_hidden(C_13, k1_tarski(C_13)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.31/1.41  tff(c_494, plain, (![D_107, A_108, C_109]: (~r2_hidden(D_107, A_108) | k4_tarski(C_109, D_107)!='#skF_3'(A_108) | k1_xboole_0=A_108)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.31/1.41  tff(c_498, plain, (![C_109, C_13]: (k4_tarski(C_109, C_13)!='#skF_3'(k1_tarski(C_13)) | k1_tarski(C_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_494])).
% 2.31/1.41  tff(c_501, plain, (![C_109, C_13]: (k4_tarski(C_109, C_13)!=C_13 | k1_tarski(C_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_435, c_498])).
% 2.31/1.41  tff(c_502, plain, (![C_109, C_13]: (k4_tarski(C_109, C_13)!=C_13)), inference(negUnitSimplification, [status(thm)], [c_413, c_501])).
% 2.31/1.41  tff(c_149, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k2_xboole_0(A_51, B_52))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.31/1.41  tff(c_156, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_149])).
% 2.31/1.41  tff(c_219, plain, (![B_23]: (k1_tarski(B_23)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_156, c_30])).
% 2.31/1.41  tff(c_143, plain, (![A_50]: (r2_hidden('#skF_3'(A_50), A_50) | k1_xboole_0=A_50)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.31/1.41  tff(c_10, plain, (![C_13, A_9]: (C_13=A_9 | ~r2_hidden(C_13, k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.31/1.41  tff(c_148, plain, (![A_9]: ('#skF_3'(k1_tarski(A_9))=A_9 | k1_tarski(A_9)=k1_xboole_0)), inference(resolution, [status(thm)], [c_143, c_10])).
% 2.31/1.41  tff(c_221, plain, (![A_9]: ('#skF_3'(k1_tarski(A_9))=A_9)), inference(negUnitSimplification, [status(thm)], [c_219, c_148])).
% 2.31/1.41  tff(c_287, plain, (![C_72, A_73, D_74]: (~r2_hidden(C_72, A_73) | k4_tarski(C_72, D_74)!='#skF_3'(A_73) | k1_xboole_0=A_73)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.31/1.41  tff(c_291, plain, (![C_13, D_74]: (k4_tarski(C_13, D_74)!='#skF_3'(k1_tarski(C_13)) | k1_tarski(C_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_287])).
% 2.31/1.41  tff(c_294, plain, (![C_13, D_74]: (k4_tarski(C_13, D_74)!=C_13 | k1_tarski(C_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_221, c_291])).
% 2.31/1.41  tff(c_295, plain, (![C_13, D_74]: (k4_tarski(C_13, D_74)!=C_13)), inference(negUnitSimplification, [status(thm)], [c_219, c_294])).
% 2.31/1.41  tff(c_48, plain, (k4_tarski('#skF_5', '#skF_6')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.31/1.41  tff(c_84, plain, (![A_45, B_46]: (k1_mcart_1(k4_tarski(A_45, B_46))=A_45)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.31/1.41  tff(c_93, plain, (k1_mcart_1('#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_48, c_84])).
% 2.31/1.41  tff(c_72, plain, (![A_43, B_44]: (k2_mcart_1(k4_tarski(A_43, B_44))=B_44)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.31/1.41  tff(c_81, plain, (k2_mcart_1('#skF_4')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_48, c_72])).
% 2.31/1.41  tff(c_46, plain, (k2_mcart_1('#skF_4')='#skF_4' | k1_mcart_1('#skF_4')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.31/1.41  tff(c_113, plain, ('#skF_6'='#skF_4' | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_93, c_81, c_46])).
% 2.31/1.41  tff(c_114, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_113])).
% 2.31/1.41  tff(c_116, plain, (k4_tarski('#skF_4', '#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_114, c_48])).
% 2.31/1.41  tff(c_306, plain, $false, inference(negUnitSimplification, [status(thm)], [c_295, c_116])).
% 2.31/1.41  tff(c_307, plain, ('#skF_6'='#skF_4'), inference(splitRight, [status(thm)], [c_113])).
% 2.31/1.41  tff(c_310, plain, (k4_tarski('#skF_5', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_307, c_48])).
% 2.31/1.41  tff(c_504, plain, $false, inference(negUnitSimplification, [status(thm)], [c_502, c_310])).
% 2.31/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.41  
% 2.31/1.41  Inference rules
% 2.31/1.41  ----------------------
% 2.31/1.41  #Ref     : 0
% 2.31/1.41  #Sup     : 109
% 2.31/1.41  #Fact    : 0
% 2.31/1.41  #Define  : 0
% 2.31/1.41  #Split   : 1
% 2.31/1.41  #Chain   : 0
% 2.31/1.41  #Close   : 0
% 2.31/1.41  
% 2.31/1.41  Ordering : KBO
% 2.31/1.42  
% 2.31/1.42  Simplification rules
% 2.31/1.42  ----------------------
% 2.31/1.42  #Subsume      : 2
% 2.31/1.42  #Demod        : 24
% 2.31/1.42  #Tautology    : 88
% 2.31/1.42  #SimpNegUnit  : 14
% 2.31/1.42  #BackRed      : 6
% 2.31/1.42  
% 2.31/1.42  #Partial instantiations: 0
% 2.31/1.42  #Strategies tried      : 1
% 2.31/1.42  
% 2.31/1.42  Timing (in seconds)
% 2.31/1.42  ----------------------
% 2.31/1.42  Preprocessing        : 0.36
% 2.31/1.42  Parsing              : 0.18
% 2.31/1.42  CNF conversion       : 0.02
% 2.31/1.42  Main loop            : 0.22
% 2.31/1.42  Inferencing          : 0.08
% 2.31/1.42  Reduction            : 0.07
% 2.31/1.42  Demodulation         : 0.05
% 2.31/1.42  BG Simplification    : 0.02
% 2.31/1.42  Subsumption          : 0.03
% 2.31/1.42  Abstraction          : 0.02
% 2.31/1.42  MUC search           : 0.00
% 2.31/1.42  Cooper               : 0.00
% 2.31/1.42  Total                : 0.61
% 2.31/1.42  Index Insertion      : 0.00
% 2.31/1.42  Index Deletion       : 0.00
% 2.31/1.42  Index Matching       : 0.00
% 2.31/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
