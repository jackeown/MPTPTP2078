%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:11 EST 2020

% Result     : Theorem 6.33s
% Output     : CNFRefutation 6.33s
% Verified   : 
% Statistics : Number of formulae       :   55 (  75 expanded)
%              Number of leaves         :   29 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   57 (  98 expanded)
%              Number of equality atoms :   14 (  31 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff(f_88,negated_conjecture,(
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

tff(f_83,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_81,axiom,(
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

tff(c_62,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_80,plain,(
    ! [A_74,B_75] : k1_enumset1(A_74,A_74,B_75) = k2_tarski(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_18,plain,(
    ! [E_16,A_10,B_11] : r2_hidden(E_16,k1_enumset1(A_10,B_11,E_16)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_86,plain,(
    ! [B_75,A_74] : r2_hidden(B_75,k2_tarski(A_74,B_75)) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_18])).

tff(c_110,plain,(
    ! [A_83,B_84] : k3_tarski(k2_tarski(A_83,B_84)) = k2_xboole_0(A_83,B_84) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_58,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(A_55,k3_tarski(B_56))
      | ~ r2_hidden(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6320,plain,(
    ! [A_11050,A_11051,B_11052] :
      ( r1_tarski(A_11050,k2_xboole_0(A_11051,B_11052))
      | ~ r2_hidden(A_11050,k2_tarski(A_11051,B_11052)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_58])).

tff(c_6344,plain,(
    ! [B_75,A_74] : r1_tarski(B_75,k2_xboole_0(A_74,B_75)) ),
    inference(resolution,[status(thm)],[c_86,c_6320])).

tff(c_64,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_145,plain,(
    ! [A_86,B_87] :
      ( r2_xboole_0(A_86,B_87)
      | B_87 = A_86
      | ~ r1_tarski(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( ~ r2_xboole_0(B_9,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_168,plain,(
    ! [B_93,A_94] :
      ( ~ r1_tarski(B_93,A_94)
      | B_93 = A_94
      | ~ r1_tarski(A_94,B_93) ) ),
    inference(resolution,[status(thm)],[c_145,c_14])).

tff(c_180,plain,
    ( k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6'
    | ~ r1_tarski('#skF_6',k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_64,c_168])).

tff(c_334,plain,(
    ~ r1_tarski('#skF_6',k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_180])).

tff(c_6398,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6344,c_334])).

tff(c_6399,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_60,plain,(
    ! [A_57,B_58] : k3_tarski(k2_tarski(A_57,B_58)) = k2_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_20,plain,(
    ! [E_16,A_10,C_12] : r2_hidden(E_16,k1_enumset1(A_10,E_16,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_89,plain,(
    ! [A_74,B_75] : r2_hidden(A_74,k2_tarski(A_74,B_75)) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_20])).

tff(c_190,plain,(
    ! [C_98,B_99,A_100] :
      ( r2_hidden(C_98,B_99)
      | ~ r2_hidden(C_98,A_100)
      | ~ r1_tarski(A_100,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_271,plain,(
    ! [A_107,B_108,B_109] :
      ( r2_hidden(A_107,B_108)
      | ~ r1_tarski(k2_tarski(A_107,B_109),B_108) ) ),
    inference(resolution,[status(thm)],[c_89,c_190])).

tff(c_7175,plain,(
    ! [A_11409,B_11410,B_11411] :
      ( r2_hidden(A_11409,k3_tarski(B_11410))
      | ~ r2_hidden(k2_tarski(A_11409,B_11411),B_11410) ) ),
    inference(resolution,[status(thm)],[c_58,c_271])).

tff(c_7243,plain,(
    ! [A_11409,B_11411,B_75] : r2_hidden(A_11409,k3_tarski(k2_tarski(k2_tarski(A_11409,B_11411),B_75))) ),
    inference(resolution,[status(thm)],[c_89,c_7175])).

tff(c_7292,plain,(
    ! [A_11412,B_11413,B_11414] : r2_hidden(A_11412,k2_xboole_0(k2_tarski(A_11412,B_11413),B_11414)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_7243])).

tff(c_7309,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_6399,c_7292])).

tff(c_7322,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_7309])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:53:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.33/2.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.33/2.34  
% 6.33/2.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.33/2.34  %$ r2_xboole_0 > r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 6.33/2.34  
% 6.33/2.34  %Foreground sorts:
% 6.33/2.34  
% 6.33/2.34  
% 6.33/2.34  %Background operators:
% 6.33/2.34  
% 6.33/2.34  
% 6.33/2.34  %Foreground operators:
% 6.33/2.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.33/2.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.33/2.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.33/2.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.33/2.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.33/2.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.33/2.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.33/2.34  tff('#skF_5', type, '#skF_5': $i).
% 6.33/2.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 6.33/2.34  tff('#skF_6', type, '#skF_6': $i).
% 6.33/2.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.33/2.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.33/2.34  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 6.33/2.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.33/2.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.33/2.34  tff('#skF_4', type, '#skF_4': $i).
% 6.33/2.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.33/2.34  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 6.33/2.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.33/2.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.33/2.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.33/2.34  
% 6.33/2.36  tff(f_88, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 6.33/2.36  tff(f_69, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.33/2.36  tff(f_59, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 6.33/2.36  tff(f_83, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.33/2.36  tff(f_81, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 6.33/2.36  tff(f_39, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 6.33/2.36  tff(f_44, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_xboole_1)).
% 6.33/2.36  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.33/2.36  tff(c_62, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.33/2.36  tff(c_80, plain, (![A_74, B_75]: (k1_enumset1(A_74, A_74, B_75)=k2_tarski(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.33/2.36  tff(c_18, plain, (![E_16, A_10, B_11]: (r2_hidden(E_16, k1_enumset1(A_10, B_11, E_16)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.33/2.36  tff(c_86, plain, (![B_75, A_74]: (r2_hidden(B_75, k2_tarski(A_74, B_75)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_18])).
% 6.33/2.36  tff(c_110, plain, (![A_83, B_84]: (k3_tarski(k2_tarski(A_83, B_84))=k2_xboole_0(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.33/2.36  tff(c_58, plain, (![A_55, B_56]: (r1_tarski(A_55, k3_tarski(B_56)) | ~r2_hidden(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.33/2.36  tff(c_6320, plain, (![A_11050, A_11051, B_11052]: (r1_tarski(A_11050, k2_xboole_0(A_11051, B_11052)) | ~r2_hidden(A_11050, k2_tarski(A_11051, B_11052)))), inference(superposition, [status(thm), theory('equality')], [c_110, c_58])).
% 6.33/2.36  tff(c_6344, plain, (![B_75, A_74]: (r1_tarski(B_75, k2_xboole_0(A_74, B_75)))), inference(resolution, [status(thm)], [c_86, c_6320])).
% 6.33/2.36  tff(c_64, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.33/2.36  tff(c_145, plain, (![A_86, B_87]: (r2_xboole_0(A_86, B_87) | B_87=A_86 | ~r1_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.33/2.36  tff(c_14, plain, (![B_9, A_8]: (~r2_xboole_0(B_9, A_8) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.33/2.36  tff(c_168, plain, (![B_93, A_94]: (~r1_tarski(B_93, A_94) | B_93=A_94 | ~r1_tarski(A_94, B_93))), inference(resolution, [status(thm)], [c_145, c_14])).
% 6.33/2.36  tff(c_180, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6' | ~r1_tarski('#skF_6', k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_64, c_168])).
% 6.33/2.36  tff(c_334, plain, (~r1_tarski('#skF_6', k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(splitLeft, [status(thm)], [c_180])).
% 6.33/2.36  tff(c_6398, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6344, c_334])).
% 6.33/2.36  tff(c_6399, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_180])).
% 6.33/2.36  tff(c_60, plain, (![A_57, B_58]: (k3_tarski(k2_tarski(A_57, B_58))=k2_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.33/2.36  tff(c_20, plain, (![E_16, A_10, C_12]: (r2_hidden(E_16, k1_enumset1(A_10, E_16, C_12)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.33/2.36  tff(c_89, plain, (![A_74, B_75]: (r2_hidden(A_74, k2_tarski(A_74, B_75)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_20])).
% 6.33/2.36  tff(c_190, plain, (![C_98, B_99, A_100]: (r2_hidden(C_98, B_99) | ~r2_hidden(C_98, A_100) | ~r1_tarski(A_100, B_99))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.33/2.36  tff(c_271, plain, (![A_107, B_108, B_109]: (r2_hidden(A_107, B_108) | ~r1_tarski(k2_tarski(A_107, B_109), B_108))), inference(resolution, [status(thm)], [c_89, c_190])).
% 6.33/2.36  tff(c_7175, plain, (![A_11409, B_11410, B_11411]: (r2_hidden(A_11409, k3_tarski(B_11410)) | ~r2_hidden(k2_tarski(A_11409, B_11411), B_11410))), inference(resolution, [status(thm)], [c_58, c_271])).
% 6.33/2.36  tff(c_7243, plain, (![A_11409, B_11411, B_75]: (r2_hidden(A_11409, k3_tarski(k2_tarski(k2_tarski(A_11409, B_11411), B_75))))), inference(resolution, [status(thm)], [c_89, c_7175])).
% 6.33/2.36  tff(c_7292, plain, (![A_11412, B_11413, B_11414]: (r2_hidden(A_11412, k2_xboole_0(k2_tarski(A_11412, B_11413), B_11414)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_7243])).
% 6.33/2.36  tff(c_7309, plain, (r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_6399, c_7292])).
% 6.33/2.36  tff(c_7322, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_7309])).
% 6.33/2.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.33/2.36  
% 6.33/2.36  Inference rules
% 6.33/2.36  ----------------------
% 6.33/2.36  #Ref     : 0
% 6.33/2.36  #Sup     : 928
% 6.33/2.36  #Fact    : 18
% 6.33/2.36  #Define  : 0
% 6.33/2.36  #Split   : 1
% 6.33/2.36  #Chain   : 0
% 6.33/2.36  #Close   : 0
% 6.33/2.36  
% 6.33/2.36  Ordering : KBO
% 6.33/2.36  
% 6.33/2.36  Simplification rules
% 6.33/2.36  ----------------------
% 6.33/2.36  #Subsume      : 99
% 6.33/2.36  #Demod        : 234
% 6.33/2.36  #Tautology    : 261
% 6.33/2.36  #SimpNegUnit  : 1
% 6.33/2.36  #BackRed      : 2
% 6.33/2.36  
% 6.33/2.36  #Partial instantiations: 4005
% 6.33/2.36  #Strategies tried      : 1
% 6.33/2.36  
% 6.33/2.36  Timing (in seconds)
% 6.33/2.36  ----------------------
% 6.33/2.36  Preprocessing        : 0.36
% 6.33/2.36  Parsing              : 0.19
% 6.33/2.36  CNF conversion       : 0.03
% 6.33/2.36  Main loop            : 1.18
% 6.33/2.36  Inferencing          : 0.62
% 6.33/2.36  Reduction            : 0.30
% 6.33/2.36  Demodulation         : 0.23
% 6.33/2.36  BG Simplification    : 0.05
% 6.33/2.36  Subsumption          : 0.16
% 6.33/2.36  Abstraction          : 0.06
% 6.33/2.36  MUC search           : 0.00
% 6.33/2.36  Cooper               : 0.00
% 6.33/2.36  Total                : 1.56
% 6.33/2.36  Index Insertion      : 0.00
% 6.33/2.36  Index Deletion       : 0.00
% 6.33/2.36  Index Matching       : 0.00
% 6.33/2.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
