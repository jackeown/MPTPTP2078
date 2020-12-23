%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:12 EST 2020

% Result     : Theorem 6.69s
% Output     : CNFRefutation 6.69s
% Verified   : 
% Statistics : Number of formulae       :   56 (  76 expanded)
%              Number of leaves         :   30 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 (  98 expanded)
%              Number of equality atoms :   13 (  31 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

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

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_85,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_64,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_82,plain,(
    ! [A_82,B_83] : k1_enumset1(A_82,A_82,B_83) = k2_tarski(A_82,B_83) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_18,plain,(
    ! [E_16,A_10,B_11] : r2_hidden(E_16,k1_enumset1(A_10,B_11,E_16)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_91,plain,(
    ! [B_83,A_82] : r2_hidden(B_83,k2_tarski(A_82,B_83)) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_18])).

tff(c_62,plain,(
    ! [A_65,B_66] : k3_tarski(k2_tarski(A_65,B_66)) = k2_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_123,plain,(
    ! [A_91,B_92] :
      ( r1_tarski(A_91,k3_tarski(B_92))
      | ~ r2_hidden(A_91,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_6856,plain,(
    ! [A_14205,A_14206,B_14207] :
      ( r1_tarski(A_14205,k2_xboole_0(A_14206,B_14207))
      | ~ r2_hidden(A_14205,k2_tarski(A_14206,B_14207)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_123])).

tff(c_6879,plain,(
    ! [B_83,A_82] : r1_tarski(B_83,k2_xboole_0(A_82,B_83)) ),
    inference(resolution,[status(thm)],[c_91,c_6856])).

tff(c_66,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_154,plain,(
    ! [A_98,B_99] :
      ( r2_xboole_0(A_98,B_99)
      | B_99 = A_98
      | ~ r1_tarski(A_98,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( ~ r2_xboole_0(B_9,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_170,plain,(
    ! [B_101,A_102] :
      ( ~ r1_tarski(B_101,A_102)
      | B_101 = A_102
      | ~ r1_tarski(A_102,B_101) ) ),
    inference(resolution,[status(thm)],[c_154,c_14])).

tff(c_182,plain,
    ( k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6'
    | ~ r1_tarski('#skF_6',k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_66,c_170])).

tff(c_336,plain,(
    ~ r1_tarski('#skF_6',k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_182])).

tff(c_6884,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6879,c_336])).

tff(c_6885,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_20,plain,(
    ! [E_16,A_10,C_12] : r2_hidden(E_16,k1_enumset1(A_10,E_16,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_88,plain,(
    ! [A_82,B_83] : r2_hidden(A_82,k2_tarski(A_82,B_83)) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_20])).

tff(c_60,plain,(
    ! [A_63,B_64] :
      ( r1_tarski(A_63,k3_tarski(B_64))
      | ~ r2_hidden(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_192,plain,(
    ! [C_106,B_107,A_108] :
      ( r2_hidden(C_106,B_107)
      | ~ r2_hidden(C_106,A_108)
      | ~ r1_tarski(A_108,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_288,plain,(
    ! [A_118,B_119,B_120] :
      ( r2_hidden(A_118,B_119)
      | ~ r1_tarski(k2_tarski(A_118,B_120),B_119) ) ),
    inference(resolution,[status(thm)],[c_88,c_192])).

tff(c_7470,plain,(
    ! [A_14448,B_14449,B_14450] :
      ( r2_hidden(A_14448,k3_tarski(B_14449))
      | ~ r2_hidden(k2_tarski(A_14448,B_14450),B_14449) ) ),
    inference(resolution,[status(thm)],[c_60,c_288])).

tff(c_7538,plain,(
    ! [A_14448,B_14450,B_83] : r2_hidden(A_14448,k3_tarski(k2_tarski(k2_tarski(A_14448,B_14450),B_83))) ),
    inference(resolution,[status(thm)],[c_88,c_7470])).

tff(c_7601,plain,(
    ! [A_14458,B_14459,B_14460] : r2_hidden(A_14458,k2_xboole_0(k2_tarski(A_14458,B_14459),B_14460)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_7538])).

tff(c_7614,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_6885,c_7601])).

tff(c_7626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_7614])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:03:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.69/2.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.69/2.41  
% 6.69/2.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.69/2.41  %$ r2_xboole_0 > r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 6.69/2.41  
% 6.69/2.41  %Foreground sorts:
% 6.69/2.41  
% 6.69/2.41  
% 6.69/2.41  %Background operators:
% 6.69/2.41  
% 6.69/2.41  
% 6.69/2.41  %Foreground operators:
% 6.69/2.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.69/2.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.69/2.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.69/2.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.69/2.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.69/2.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.69/2.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.69/2.41  tff('#skF_5', type, '#skF_5': $i).
% 6.69/2.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 6.69/2.41  tff('#skF_6', type, '#skF_6': $i).
% 6.69/2.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.69/2.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.69/2.41  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 6.69/2.41  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.69/2.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.69/2.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.69/2.41  tff('#skF_4', type, '#skF_4': $i).
% 6.69/2.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.69/2.41  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 6.69/2.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.69/2.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.69/2.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.69/2.41  
% 6.69/2.42  tff(f_90, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 6.69/2.42  tff(f_69, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.69/2.42  tff(f_59, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 6.69/2.42  tff(f_85, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.69/2.42  tff(f_83, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 6.69/2.42  tff(f_39, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 6.69/2.42  tff(f_44, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_xboole_1)).
% 6.69/2.42  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.69/2.42  tff(c_64, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.69/2.42  tff(c_82, plain, (![A_82, B_83]: (k1_enumset1(A_82, A_82, B_83)=k2_tarski(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.69/2.42  tff(c_18, plain, (![E_16, A_10, B_11]: (r2_hidden(E_16, k1_enumset1(A_10, B_11, E_16)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.69/2.42  tff(c_91, plain, (![B_83, A_82]: (r2_hidden(B_83, k2_tarski(A_82, B_83)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_18])).
% 6.69/2.42  tff(c_62, plain, (![A_65, B_66]: (k3_tarski(k2_tarski(A_65, B_66))=k2_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_85])).
% 6.69/2.42  tff(c_123, plain, (![A_91, B_92]: (r1_tarski(A_91, k3_tarski(B_92)) | ~r2_hidden(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.69/2.42  tff(c_6856, plain, (![A_14205, A_14206, B_14207]: (r1_tarski(A_14205, k2_xboole_0(A_14206, B_14207)) | ~r2_hidden(A_14205, k2_tarski(A_14206, B_14207)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_123])).
% 6.69/2.42  tff(c_6879, plain, (![B_83, A_82]: (r1_tarski(B_83, k2_xboole_0(A_82, B_83)))), inference(resolution, [status(thm)], [c_91, c_6856])).
% 6.69/2.42  tff(c_66, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.69/2.42  tff(c_154, plain, (![A_98, B_99]: (r2_xboole_0(A_98, B_99) | B_99=A_98 | ~r1_tarski(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.69/2.42  tff(c_14, plain, (![B_9, A_8]: (~r2_xboole_0(B_9, A_8) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.69/2.42  tff(c_170, plain, (![B_101, A_102]: (~r1_tarski(B_101, A_102) | B_101=A_102 | ~r1_tarski(A_102, B_101))), inference(resolution, [status(thm)], [c_154, c_14])).
% 6.69/2.42  tff(c_182, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6' | ~r1_tarski('#skF_6', k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_66, c_170])).
% 6.69/2.42  tff(c_336, plain, (~r1_tarski('#skF_6', k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(splitLeft, [status(thm)], [c_182])).
% 6.69/2.42  tff(c_6884, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6879, c_336])).
% 6.69/2.42  tff(c_6885, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_182])).
% 6.69/2.42  tff(c_20, plain, (![E_16, A_10, C_12]: (r2_hidden(E_16, k1_enumset1(A_10, E_16, C_12)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.69/2.42  tff(c_88, plain, (![A_82, B_83]: (r2_hidden(A_82, k2_tarski(A_82, B_83)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_20])).
% 6.69/2.42  tff(c_60, plain, (![A_63, B_64]: (r1_tarski(A_63, k3_tarski(B_64)) | ~r2_hidden(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.69/2.42  tff(c_192, plain, (![C_106, B_107, A_108]: (r2_hidden(C_106, B_107) | ~r2_hidden(C_106, A_108) | ~r1_tarski(A_108, B_107))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.69/2.42  tff(c_288, plain, (![A_118, B_119, B_120]: (r2_hidden(A_118, B_119) | ~r1_tarski(k2_tarski(A_118, B_120), B_119))), inference(resolution, [status(thm)], [c_88, c_192])).
% 6.69/2.42  tff(c_7470, plain, (![A_14448, B_14449, B_14450]: (r2_hidden(A_14448, k3_tarski(B_14449)) | ~r2_hidden(k2_tarski(A_14448, B_14450), B_14449))), inference(resolution, [status(thm)], [c_60, c_288])).
% 6.69/2.42  tff(c_7538, plain, (![A_14448, B_14450, B_83]: (r2_hidden(A_14448, k3_tarski(k2_tarski(k2_tarski(A_14448, B_14450), B_83))))), inference(resolution, [status(thm)], [c_88, c_7470])).
% 6.69/2.42  tff(c_7601, plain, (![A_14458, B_14459, B_14460]: (r2_hidden(A_14458, k2_xboole_0(k2_tarski(A_14458, B_14459), B_14460)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_7538])).
% 6.69/2.42  tff(c_7614, plain, (r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_6885, c_7601])).
% 6.69/2.42  tff(c_7626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_7614])).
% 6.69/2.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.69/2.42  
% 6.69/2.42  Inference rules
% 6.69/2.42  ----------------------
% 6.69/2.42  #Ref     : 0
% 6.69/2.42  #Sup     : 920
% 6.69/2.42  #Fact    : 18
% 6.69/2.42  #Define  : 0
% 6.69/2.42  #Split   : 1
% 6.69/2.42  #Chain   : 0
% 6.69/2.42  #Close   : 0
% 6.69/2.42  
% 6.69/2.42  Ordering : KBO
% 6.69/2.42  
% 6.69/2.42  Simplification rules
% 6.69/2.42  ----------------------
% 6.69/2.42  #Subsume      : 96
% 6.69/2.42  #Demod        : 231
% 6.69/2.42  #Tautology    : 263
% 6.69/2.42  #SimpNegUnit  : 1
% 6.69/2.42  #BackRed      : 2
% 6.69/2.42  
% 6.69/2.42  #Partial instantiations: 4560
% 6.69/2.42  #Strategies tried      : 1
% 6.69/2.42  
% 6.69/2.42  Timing (in seconds)
% 6.69/2.42  ----------------------
% 6.69/2.42  Preprocessing        : 0.34
% 6.69/2.42  Parsing              : 0.17
% 6.69/2.42  CNF conversion       : 0.03
% 6.69/2.42  Main loop            : 1.31
% 6.69/2.42  Inferencing          : 0.66
% 6.69/2.42  Reduction            : 0.35
% 6.69/2.42  Demodulation         : 0.28
% 6.69/2.42  BG Simplification    : 0.05
% 6.69/2.42  Subsumption          : 0.17
% 6.69/2.42  Abstraction          : 0.06
% 6.69/2.42  MUC search           : 0.00
% 6.69/2.42  Cooper               : 0.00
% 6.69/2.42  Total                : 1.69
% 6.69/2.42  Index Insertion      : 0.00
% 6.69/2.42  Index Deletion       : 0.00
% 6.69/2.42  Index Matching       : 0.00
% 6.69/2.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
