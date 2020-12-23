%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:26 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 120 expanded)
%              Number of leaves         :   22 (  51 expanded)
%              Depth                    :   15
%              Number of atoms          :   79 ( 228 expanded)
%              Number of equality atoms :   49 ( 153 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_48,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_48,plain,(
    k1_zfmisc_1(k1_xboole_0) != k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_75,plain,(
    ! [A_37,B_38] : k1_enumset1(A_37,A_37,B_38) = k2_tarski(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    ! [E_9,A_3,C_5] : r2_hidden(E_9,k1_enumset1(A_3,E_9,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_93,plain,(
    ! [A_39,B_40] : r2_hidden(A_39,k2_tarski(A_39,B_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_10])).

tff(c_96,plain,(
    ! [A_10] : r2_hidden(A_10,k1_tarski(A_10)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_93])).

tff(c_170,plain,(
    ! [A_63,B_64] :
      ( r1_tarski('#skF_3'(A_63,B_64),A_63)
      | r2_hidden('#skF_4'(A_63,B_64),B_64)
      | k1_zfmisc_1(A_63) = B_64 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_32,plain,(
    ! [A_11,B_12] : k1_enumset1(A_11,A_11,B_12) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_113,plain,(
    ! [E_47,C_48,B_49,A_50] :
      ( E_47 = C_48
      | E_47 = B_49
      | E_47 = A_50
      | ~ r2_hidden(E_47,k1_enumset1(A_50,B_49,C_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_132,plain,(
    ! [E_51,B_52,A_53] :
      ( E_51 = B_52
      | E_51 = A_53
      | E_51 = A_53
      | ~ r2_hidden(E_51,k2_tarski(A_53,B_52)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_113])).

tff(c_141,plain,(
    ! [E_51,A_10] :
      ( E_51 = A_10
      | E_51 = A_10
      | E_51 = A_10
      | ~ r2_hidden(E_51,k1_tarski(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_132])).

tff(c_193,plain,(
    ! [A_65,A_66] :
      ( '#skF_4'(A_65,k1_tarski(A_66)) = A_66
      | r1_tarski('#skF_3'(A_65,k1_tarski(A_66)),A_65)
      | k1_zfmisc_1(A_65) = k1_tarski(A_66) ) ),
    inference(resolution,[status(thm)],[c_170,c_141])).

tff(c_4,plain,(
    ! [A_2] :
      ( k1_xboole_0 = A_2
      | ~ r1_tarski(A_2,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_200,plain,(
    ! [A_67] :
      ( '#skF_3'(k1_xboole_0,k1_tarski(A_67)) = k1_xboole_0
      | '#skF_4'(k1_xboole_0,k1_tarski(A_67)) = A_67
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_67) ) ),
    inference(resolution,[status(thm)],[c_193,c_4])).

tff(c_44,plain,(
    ! [A_16,B_17] :
      ( ~ r2_hidden('#skF_3'(A_16,B_17),B_17)
      | r2_hidden('#skF_4'(A_16,B_17),B_17)
      | k1_zfmisc_1(A_16) = B_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_371,plain,(
    ! [A_138] :
      ( ~ r2_hidden(k1_xboole_0,k1_tarski(A_138))
      | r2_hidden('#skF_4'(k1_xboole_0,k1_tarski(A_138)),k1_tarski(A_138))
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_138)
      | '#skF_4'(k1_xboole_0,k1_tarski(A_138)) = A_138
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_138) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_44])).

tff(c_376,plain,(
    ! [A_139] :
      ( ~ r2_hidden(k1_xboole_0,k1_tarski(A_139))
      | '#skF_4'(k1_xboole_0,k1_tarski(A_139)) = A_139
      | k1_zfmisc_1(k1_xboole_0) = k1_tarski(A_139) ) ),
    inference(resolution,[status(thm)],[c_371,c_141])).

tff(c_380,plain,
    ( '#skF_4'(k1_xboole_0,k1_tarski(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_96,c_376])).

tff(c_383,plain,(
    '#skF_4'(k1_xboole_0,k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_380])).

tff(c_152,plain,(
    ! [A_56,B_57] :
      ( r1_tarski('#skF_3'(A_56,B_57),A_56)
      | ~ r1_tarski('#skF_4'(A_56,B_57),A_56)
      | k1_zfmisc_1(A_56) = B_57 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_157,plain,(
    ! [B_57] :
      ( '#skF_3'(k1_xboole_0,B_57) = k1_xboole_0
      | ~ r1_tarski('#skF_4'(k1_xboole_0,B_57),k1_xboole_0)
      | k1_zfmisc_1(k1_xboole_0) = B_57 ) ),
    inference(resolution,[status(thm)],[c_152,c_4])).

tff(c_390,plain,
    ( '#skF_3'(k1_xboole_0,k1_tarski(k1_xboole_0)) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_157])).

tff(c_396,plain,
    ( '#skF_3'(k1_xboole_0,k1_tarski(k1_xboole_0)) = k1_xboole_0
    | k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_390])).

tff(c_397,plain,(
    '#skF_3'(k1_xboole_0,k1_tarski(k1_xboole_0)) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_396])).

tff(c_40,plain,(
    ! [A_16,B_17] :
      ( ~ r2_hidden('#skF_3'(A_16,B_17),B_17)
      | ~ r1_tarski('#skF_4'(A_16,B_17),A_16)
      | k1_zfmisc_1(A_16) = B_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_408,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
    | ~ r1_tarski('#skF_4'(k1_xboole_0,k1_tarski(k1_xboole_0)),k1_xboole_0)
    | k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_40])).

tff(c_426,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_383,c_96,c_408])).

tff(c_428,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_426])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:14:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.30  
% 2.34/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.30  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1 > #skF_4
% 2.34/1.30  
% 2.34/1.30  %Foreground sorts:
% 2.34/1.30  
% 2.34/1.30  
% 2.34/1.30  %Background operators:
% 2.34/1.30  
% 2.34/1.30  
% 2.34/1.30  %Foreground operators:
% 2.34/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.34/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.34/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.34/1.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.34/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.34/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.34/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.34/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.34/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.34/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.34/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.34/1.30  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.34/1.30  
% 2.34/1.31  tff(f_61, negated_conjecture, ~(k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 2.34/1.31  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.34/1.31  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.34/1.31  tff(f_50, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.34/1.31  tff(f_46, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.34/1.31  tff(f_59, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.34/1.31  tff(f_31, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.34/1.31  tff(c_48, plain, (k1_zfmisc_1(k1_xboole_0)!=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.34/1.31  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.34/1.31  tff(c_30, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.34/1.31  tff(c_75, plain, (![A_37, B_38]: (k1_enumset1(A_37, A_37, B_38)=k2_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.34/1.31  tff(c_10, plain, (![E_9, A_3, C_5]: (r2_hidden(E_9, k1_enumset1(A_3, E_9, C_5)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.34/1.31  tff(c_93, plain, (![A_39, B_40]: (r2_hidden(A_39, k2_tarski(A_39, B_40)))), inference(superposition, [status(thm), theory('equality')], [c_75, c_10])).
% 2.34/1.31  tff(c_96, plain, (![A_10]: (r2_hidden(A_10, k1_tarski(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_93])).
% 2.34/1.31  tff(c_170, plain, (![A_63, B_64]: (r1_tarski('#skF_3'(A_63, B_64), A_63) | r2_hidden('#skF_4'(A_63, B_64), B_64) | k1_zfmisc_1(A_63)=B_64)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.34/1.31  tff(c_32, plain, (![A_11, B_12]: (k1_enumset1(A_11, A_11, B_12)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.34/1.31  tff(c_113, plain, (![E_47, C_48, B_49, A_50]: (E_47=C_48 | E_47=B_49 | E_47=A_50 | ~r2_hidden(E_47, k1_enumset1(A_50, B_49, C_48)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.34/1.31  tff(c_132, plain, (![E_51, B_52, A_53]: (E_51=B_52 | E_51=A_53 | E_51=A_53 | ~r2_hidden(E_51, k2_tarski(A_53, B_52)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_113])).
% 2.34/1.31  tff(c_141, plain, (![E_51, A_10]: (E_51=A_10 | E_51=A_10 | E_51=A_10 | ~r2_hidden(E_51, k1_tarski(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_132])).
% 2.34/1.31  tff(c_193, plain, (![A_65, A_66]: ('#skF_4'(A_65, k1_tarski(A_66))=A_66 | r1_tarski('#skF_3'(A_65, k1_tarski(A_66)), A_65) | k1_zfmisc_1(A_65)=k1_tarski(A_66))), inference(resolution, [status(thm)], [c_170, c_141])).
% 2.34/1.31  tff(c_4, plain, (![A_2]: (k1_xboole_0=A_2 | ~r1_tarski(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.34/1.31  tff(c_200, plain, (![A_67]: ('#skF_3'(k1_xboole_0, k1_tarski(A_67))=k1_xboole_0 | '#skF_4'(k1_xboole_0, k1_tarski(A_67))=A_67 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_67))), inference(resolution, [status(thm)], [c_193, c_4])).
% 2.34/1.31  tff(c_44, plain, (![A_16, B_17]: (~r2_hidden('#skF_3'(A_16, B_17), B_17) | r2_hidden('#skF_4'(A_16, B_17), B_17) | k1_zfmisc_1(A_16)=B_17)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.34/1.31  tff(c_371, plain, (![A_138]: (~r2_hidden(k1_xboole_0, k1_tarski(A_138)) | r2_hidden('#skF_4'(k1_xboole_0, k1_tarski(A_138)), k1_tarski(A_138)) | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_138) | '#skF_4'(k1_xboole_0, k1_tarski(A_138))=A_138 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_138))), inference(superposition, [status(thm), theory('equality')], [c_200, c_44])).
% 2.34/1.31  tff(c_376, plain, (![A_139]: (~r2_hidden(k1_xboole_0, k1_tarski(A_139)) | '#skF_4'(k1_xboole_0, k1_tarski(A_139))=A_139 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(A_139))), inference(resolution, [status(thm)], [c_371, c_141])).
% 2.34/1.31  tff(c_380, plain, ('#skF_4'(k1_xboole_0, k1_tarski(k1_xboole_0))=k1_xboole_0 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(resolution, [status(thm)], [c_96, c_376])).
% 2.34/1.31  tff(c_383, plain, ('#skF_4'(k1_xboole_0, k1_tarski(k1_xboole_0))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_48, c_380])).
% 2.34/1.31  tff(c_152, plain, (![A_56, B_57]: (r1_tarski('#skF_3'(A_56, B_57), A_56) | ~r1_tarski('#skF_4'(A_56, B_57), A_56) | k1_zfmisc_1(A_56)=B_57)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.34/1.31  tff(c_157, plain, (![B_57]: ('#skF_3'(k1_xboole_0, B_57)=k1_xboole_0 | ~r1_tarski('#skF_4'(k1_xboole_0, B_57), k1_xboole_0) | k1_zfmisc_1(k1_xboole_0)=B_57)), inference(resolution, [status(thm)], [c_152, c_4])).
% 2.34/1.31  tff(c_390, plain, ('#skF_3'(k1_xboole_0, k1_tarski(k1_xboole_0))=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_xboole_0) | k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_383, c_157])).
% 2.34/1.31  tff(c_396, plain, ('#skF_3'(k1_xboole_0, k1_tarski(k1_xboole_0))=k1_xboole_0 | k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_390])).
% 2.34/1.31  tff(c_397, plain, ('#skF_3'(k1_xboole_0, k1_tarski(k1_xboole_0))=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_48, c_396])).
% 2.34/1.31  tff(c_40, plain, (![A_16, B_17]: (~r2_hidden('#skF_3'(A_16, B_17), B_17) | ~r1_tarski('#skF_4'(A_16, B_17), A_16) | k1_zfmisc_1(A_16)=B_17)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.34/1.31  tff(c_408, plain, (~r2_hidden(k1_xboole_0, k1_tarski(k1_xboole_0)) | ~r1_tarski('#skF_4'(k1_xboole_0, k1_tarski(k1_xboole_0)), k1_xboole_0) | k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_397, c_40])).
% 2.34/1.31  tff(c_426, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_383, c_96, c_408])).
% 2.34/1.31  tff(c_428, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_426])).
% 2.34/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.31  
% 2.34/1.31  Inference rules
% 2.34/1.31  ----------------------
% 2.34/1.31  #Ref     : 0
% 2.34/1.31  #Sup     : 74
% 2.34/1.31  #Fact    : 0
% 2.34/1.31  #Define  : 0
% 2.34/1.31  #Split   : 0
% 2.34/1.31  #Chain   : 0
% 2.34/1.31  #Close   : 0
% 2.34/1.31  
% 2.34/1.31  Ordering : KBO
% 2.34/1.31  
% 2.34/1.31  Simplification rules
% 2.34/1.31  ----------------------
% 2.34/1.31  #Subsume      : 5
% 2.34/1.31  #Demod        : 20
% 2.34/1.31  #Tautology    : 34
% 2.34/1.31  #SimpNegUnit  : 6
% 2.34/1.31  #BackRed      : 0
% 2.34/1.31  
% 2.34/1.31  #Partial instantiations: 0
% 2.34/1.31  #Strategies tried      : 1
% 2.34/1.31  
% 2.34/1.31  Timing (in seconds)
% 2.34/1.31  ----------------------
% 2.34/1.31  Preprocessing        : 0.29
% 2.34/1.31  Parsing              : 0.15
% 2.34/1.31  CNF conversion       : 0.02
% 2.34/1.31  Main loop            : 0.28
% 2.34/1.31  Inferencing          : 0.12
% 2.34/1.31  Reduction            : 0.07
% 2.34/1.31  Demodulation         : 0.05
% 2.34/1.31  BG Simplification    : 0.02
% 2.34/1.31  Subsumption          : 0.06
% 2.34/1.31  Abstraction          : 0.02
% 2.34/1.31  MUC search           : 0.00
% 2.34/1.31  Cooper               : 0.00
% 2.34/1.31  Total                : 0.60
% 2.34/1.31  Index Insertion      : 0.00
% 2.34/1.31  Index Deletion       : 0.00
% 2.34/1.31  Index Matching       : 0.00
% 2.34/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
