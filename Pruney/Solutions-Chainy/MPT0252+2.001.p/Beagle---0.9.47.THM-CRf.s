%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:01 EST 2020

% Result     : Theorem 6.59s
% Output     : CNFRefutation 6.59s
% Verified   : 
% Statistics : Number of formulae       :   57 (  73 expanded)
%              Number of leaves         :   31 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   61 ( 100 expanded)
%              Number of equality atoms :   15 (  29 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_87,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
     => ~ r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_66,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_85,plain,(
    ! [A_87,B_88] : k1_enumset1(A_87,A_87,B_88) = k2_tarski(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    ! [E_18,A_12,B_13] : r2_hidden(E_18,k1_enumset1(A_12,B_13,E_18)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_94,plain,(
    ! [B_88,A_87] : r2_hidden(B_88,k2_tarski(A_87,B_88)) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_20])).

tff(c_64,plain,(
    ! [A_68,B_69] : k3_tarski(k2_tarski(A_68,B_69)) = k2_xboole_0(A_68,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_151,plain,(
    ! [A_98,B_99] :
      ( r1_tarski(A_98,k3_tarski(B_99))
      | ~ r2_hidden(A_98,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_7201,plain,(
    ! [A_14665,A_14666,B_14667] :
      ( r1_tarski(A_14665,k2_xboole_0(A_14666,B_14667))
      | ~ r2_hidden(A_14665,k2_tarski(A_14666,B_14667)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_151])).

tff(c_7224,plain,(
    ! [B_88,A_87] : r1_tarski(B_88,k2_xboole_0(A_87,B_88)) ),
    inference(resolution,[status(thm)],[c_94,c_7201])).

tff(c_68,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( r2_xboole_0(A_8,B_9)
      | B_9 = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_159,plain,(
    ! [A_102,B_103] :
      ( r2_xboole_0(A_102,B_103)
      | B_103 = A_102
      | ~ r1_tarski(A_102,B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_xboole_0(B_2,A_1)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_180,plain,(
    ! [B_107,A_108] :
      ( ~ r2_xboole_0(B_107,A_108)
      | B_107 = A_108
      | ~ r1_tarski(A_108,B_107) ) ),
    inference(resolution,[status(thm)],[c_159,c_2])).

tff(c_185,plain,(
    ! [B_109,A_110] :
      ( ~ r1_tarski(B_109,A_110)
      | B_109 = A_110
      | ~ r1_tarski(A_110,B_109) ) ),
    inference(resolution,[status(thm)],[c_10,c_180])).

tff(c_202,plain,
    ( k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6'
    | ~ r1_tarski('#skF_6',k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_68,c_185])).

tff(c_261,plain,(
    ~ r1_tarski('#skF_6',k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_202])).

tff(c_7229,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7224,c_261])).

tff(c_7230,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_16,plain,(
    ! [A_10,B_11] : r1_tarski(A_10,k2_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_7237,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_7230,c_16])).

tff(c_22,plain,(
    ! [E_18,A_12,C_14] : r2_hidden(E_18,k1_enumset1(A_12,E_18,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_91,plain,(
    ! [A_87,B_88] : r2_hidden(A_87,k2_tarski(A_87,B_88)) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_22])).

tff(c_213,plain,(
    ! [C_114,B_115,A_116] :
      ( r2_hidden(C_114,B_115)
      | ~ r2_hidden(C_114,A_116)
      | ~ r1_tarski(A_116,B_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_7362,plain,(
    ! [A_14830,B_14831,B_14832] :
      ( r2_hidden(A_14830,B_14831)
      | ~ r1_tarski(k2_tarski(A_14830,B_14832),B_14831) ) ),
    inference(resolution,[status(thm)],[c_91,c_213])).

tff(c_7365,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_7237,c_7362])).

tff(c_7388,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_7365])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:27:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.59/2.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.59/2.39  
% 6.59/2.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.59/2.39  %$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 6.59/2.39  
% 6.59/2.39  %Foreground sorts:
% 6.59/2.39  
% 6.59/2.39  
% 6.59/2.39  %Background operators:
% 6.59/2.39  
% 6.59/2.39  
% 6.59/2.39  %Foreground operators:
% 6.59/2.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.59/2.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.59/2.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.59/2.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.59/2.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.59/2.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.59/2.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.59/2.39  tff('#skF_5', type, '#skF_5': $i).
% 6.59/2.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 6.59/2.39  tff('#skF_6', type, '#skF_6': $i).
% 6.59/2.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.59/2.39  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.59/2.39  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 6.59/2.39  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.59/2.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.59/2.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.59/2.39  tff('#skF_4', type, '#skF_4': $i).
% 6.59/2.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.59/2.39  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 6.59/2.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.59/2.39  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.59/2.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.59/2.39  
% 6.59/2.40  tff(f_92, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 6.59/2.40  tff(f_71, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 6.59/2.40  tff(f_61, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 6.59/2.40  tff(f_87, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.59/2.40  tff(f_85, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 6.59/2.40  tff(f_44, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 6.59/2.40  tff(f_30, axiom, (![A, B]: (r2_xboole_0(A, B) => ~r2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_xboole_0)).
% 6.59/2.40  tff(f_46, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.59/2.40  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.59/2.40  tff(c_66, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.59/2.40  tff(c_85, plain, (![A_87, B_88]: (k1_enumset1(A_87, A_87, B_88)=k2_tarski(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.59/2.40  tff(c_20, plain, (![E_18, A_12, B_13]: (r2_hidden(E_18, k1_enumset1(A_12, B_13, E_18)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.59/2.40  tff(c_94, plain, (![B_88, A_87]: (r2_hidden(B_88, k2_tarski(A_87, B_88)))), inference(superposition, [status(thm), theory('equality')], [c_85, c_20])).
% 6.59/2.40  tff(c_64, plain, (![A_68, B_69]: (k3_tarski(k2_tarski(A_68, B_69))=k2_xboole_0(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.59/2.40  tff(c_151, plain, (![A_98, B_99]: (r1_tarski(A_98, k3_tarski(B_99)) | ~r2_hidden(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.59/2.40  tff(c_7201, plain, (![A_14665, A_14666, B_14667]: (r1_tarski(A_14665, k2_xboole_0(A_14666, B_14667)) | ~r2_hidden(A_14665, k2_tarski(A_14666, B_14667)))), inference(superposition, [status(thm), theory('equality')], [c_64, c_151])).
% 6.59/2.40  tff(c_7224, plain, (![B_88, A_87]: (r1_tarski(B_88, k2_xboole_0(A_87, B_88)))), inference(resolution, [status(thm)], [c_94, c_7201])).
% 6.59/2.40  tff(c_68, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.59/2.40  tff(c_10, plain, (![A_8, B_9]: (r2_xboole_0(A_8, B_9) | B_9=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.59/2.40  tff(c_159, plain, (![A_102, B_103]: (r2_xboole_0(A_102, B_103) | B_103=A_102 | ~r1_tarski(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.59/2.40  tff(c_2, plain, (![B_2, A_1]: (~r2_xboole_0(B_2, A_1) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 6.59/2.40  tff(c_180, plain, (![B_107, A_108]: (~r2_xboole_0(B_107, A_108) | B_107=A_108 | ~r1_tarski(A_108, B_107))), inference(resolution, [status(thm)], [c_159, c_2])).
% 6.59/2.40  tff(c_185, plain, (![B_109, A_110]: (~r1_tarski(B_109, A_110) | B_109=A_110 | ~r1_tarski(A_110, B_109))), inference(resolution, [status(thm)], [c_10, c_180])).
% 6.59/2.40  tff(c_202, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6' | ~r1_tarski('#skF_6', k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_68, c_185])).
% 6.59/2.40  tff(c_261, plain, (~r1_tarski('#skF_6', k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(splitLeft, [status(thm)], [c_202])).
% 6.59/2.40  tff(c_7229, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7224, c_261])).
% 6.59/2.40  tff(c_7230, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_202])).
% 6.59/2.40  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(A_10, k2_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.59/2.40  tff(c_7237, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_7230, c_16])).
% 6.59/2.40  tff(c_22, plain, (![E_18, A_12, C_14]: (r2_hidden(E_18, k1_enumset1(A_12, E_18, C_14)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.59/2.40  tff(c_91, plain, (![A_87, B_88]: (r2_hidden(A_87, k2_tarski(A_87, B_88)))), inference(superposition, [status(thm), theory('equality')], [c_85, c_22])).
% 6.59/2.40  tff(c_213, plain, (![C_114, B_115, A_116]: (r2_hidden(C_114, B_115) | ~r2_hidden(C_114, A_116) | ~r1_tarski(A_116, B_115))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.59/2.40  tff(c_7362, plain, (![A_14830, B_14831, B_14832]: (r2_hidden(A_14830, B_14831) | ~r1_tarski(k2_tarski(A_14830, B_14832), B_14831))), inference(resolution, [status(thm)], [c_91, c_213])).
% 6.59/2.40  tff(c_7365, plain, (r2_hidden('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_7237, c_7362])).
% 6.59/2.40  tff(c_7388, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_7365])).
% 6.59/2.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.59/2.40  
% 6.59/2.40  Inference rules
% 6.59/2.40  ----------------------
% 6.59/2.40  #Ref     : 0
% 6.59/2.40  #Sup     : 842
% 6.59/2.40  #Fact    : 18
% 6.59/2.40  #Define  : 0
% 6.59/2.40  #Split   : 1
% 6.59/2.40  #Chain   : 0
% 6.59/2.40  #Close   : 0
% 6.59/2.40  
% 6.59/2.40  Ordering : KBO
% 6.59/2.40  
% 6.59/2.40  Simplification rules
% 6.59/2.40  ----------------------
% 6.59/2.40  #Subsume      : 90
% 6.59/2.40  #Demod        : 180
% 6.59/2.40  #Tautology    : 213
% 6.59/2.40  #SimpNegUnit  : 1
% 6.59/2.40  #BackRed      : 2
% 6.59/2.40  
% 6.59/2.40  #Partial instantiations: 4704
% 6.59/2.40  #Strategies tried      : 1
% 6.59/2.40  
% 6.59/2.40  Timing (in seconds)
% 6.59/2.40  ----------------------
% 6.59/2.41  Preprocessing        : 0.34
% 6.59/2.41  Parsing              : 0.17
% 6.59/2.41  CNF conversion       : 0.03
% 6.59/2.41  Main loop            : 1.25
% 6.59/2.41  Inferencing          : 0.63
% 6.59/2.41  Reduction            : 0.33
% 6.59/2.41  Demodulation         : 0.26
% 6.59/2.41  BG Simplification    : 0.07
% 6.59/2.41  Subsumption          : 0.16
% 6.59/2.41  Abstraction          : 0.05
% 6.59/2.41  MUC search           : 0.00
% 6.59/2.41  Cooper               : 0.00
% 6.59/2.41  Total                : 1.62
% 6.59/2.41  Index Insertion      : 0.00
% 6.59/2.41  Index Deletion       : 0.00
% 6.59/2.41  Index Matching       : 0.00
% 6.59/2.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
