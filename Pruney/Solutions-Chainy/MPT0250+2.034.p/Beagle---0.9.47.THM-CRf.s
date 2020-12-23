%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:36 EST 2020

% Result     : Theorem 5.96s
% Output     : CNFRefutation 6.17s
% Verified   : 
% Statistics : Number of formulae       :   53 (  61 expanded)
%              Number of leaves         :   29 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   51 (  64 expanded)
%              Number of equality atoms :   15 (  24 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_75,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_54,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_137,plain,(
    ! [A_65,B_66] : k1_enumset1(A_65,A_65,B_66) = k2_tarski(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_14,plain,(
    ! [E_17,A_11,B_12] : r2_hidden(E_17,k1_enumset1(A_11,B_12,E_17)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_143,plain,(
    ! [B_66,A_65] : r2_hidden(B_66,k2_tarski(A_65,B_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_14])).

tff(c_52,plain,(
    ! [A_48,B_49] : k3_tarski(k2_tarski(A_48,B_49)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_181,plain,(
    ! [A_72,B_73] :
      ( r1_tarski(A_72,k3_tarski(B_73))
      | ~ r2_hidden(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_5944,plain,(
    ! [A_12383,A_12384,B_12385] :
      ( r1_tarski(A_12383,k2_xboole_0(A_12384,B_12385))
      | ~ r2_hidden(A_12383,k2_tarski(A_12384,B_12385)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_181])).

tff(c_6035,plain,(
    ! [B_12682,A_12683] : r1_tarski(B_12682,k2_xboole_0(A_12683,B_12682)) ),
    inference(resolution,[status(thm)],[c_143,c_5944])).

tff(c_10,plain,(
    ! [B_10,A_9] : k2_tarski(B_10,A_9) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_102,plain,(
    ! [A_62,B_63] : k3_tarski(k2_tarski(A_62,B_63)) = k2_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_189,plain,(
    ! [A_74,B_75] : k3_tarski(k2_tarski(A_74,B_75)) = k2_xboole_0(B_75,A_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_102])).

tff(c_198,plain,(
    ! [B_75,A_74] : k2_xboole_0(B_75,A_74) = k2_xboole_0(A_74,B_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_52])).

tff(c_56,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_4'),'#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_218,plain,(
    r1_tarski(k2_xboole_0('#skF_5',k1_tarski('#skF_4')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_56])).

tff(c_325,plain,(
    ! [A_94,C_95,B_96] :
      ( r1_tarski(A_94,C_95)
      | ~ r1_tarski(B_96,C_95)
      | ~ r1_tarski(A_94,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_333,plain,(
    ! [A_94] :
      ( r1_tarski(A_94,'#skF_5')
      | ~ r1_tarski(A_94,k2_xboole_0('#skF_5',k1_tarski('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_218,c_325])).

tff(c_6084,plain,(
    r1_tarski(k1_tarski('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_6035,c_333])).

tff(c_36,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_155,plain,(
    ! [B_67,A_68] : r2_hidden(B_67,k2_tarski(A_68,B_67)) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_14])).

tff(c_164,plain,(
    ! [A_18] : r2_hidden(A_18,k1_tarski(A_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_155])).

tff(c_270,plain,(
    ! [C_86,B_87,A_88] :
      ( r2_hidden(C_86,B_87)
      | ~ r2_hidden(C_86,A_88)
      | ~ r1_tarski(A_88,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_287,plain,(
    ! [A_18,B_87] :
      ( r2_hidden(A_18,B_87)
      | ~ r1_tarski(k1_tarski(A_18),B_87) ) ),
    inference(resolution,[status(thm)],[c_164,c_270])).

tff(c_6101,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_6084,c_287])).

tff(c_6107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_6101])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:24:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.96/2.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.96/2.35  
% 5.96/2.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.17/2.35  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 6.17/2.35  
% 6.17/2.35  %Foreground sorts:
% 6.17/2.35  
% 6.17/2.35  
% 6.17/2.35  %Background operators:
% 6.17/2.35  
% 6.17/2.35  
% 6.17/2.35  %Foreground operators:
% 6.17/2.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.17/2.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.17/2.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.17/2.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.17/2.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.17/2.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.17/2.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.17/2.35  tff('#skF_5', type, '#skF_5': $i).
% 6.17/2.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 6.17/2.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.17/2.35  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.17/2.35  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.17/2.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.17/2.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.17/2.35  tff('#skF_4', type, '#skF_4': $i).
% 6.17/2.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.17/2.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 6.17/2.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.17/2.35  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.17/2.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.17/2.35  
% 6.17/2.36  tff(f_80, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 6.17/2.36  tff(f_59, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.17/2.36  tff(f_55, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 6.17/2.36  tff(f_75, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.17/2.36  tff(f_73, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 6.17/2.36  tff(f_40, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.17/2.36  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 6.17/2.36  tff(f_57, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.17/2.36  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.17/2.36  tff(c_54, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.17/2.36  tff(c_137, plain, (![A_65, B_66]: (k1_enumset1(A_65, A_65, B_66)=k2_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.17/2.36  tff(c_14, plain, (![E_17, A_11, B_12]: (r2_hidden(E_17, k1_enumset1(A_11, B_12, E_17)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.17/2.36  tff(c_143, plain, (![B_66, A_65]: (r2_hidden(B_66, k2_tarski(A_65, B_66)))), inference(superposition, [status(thm), theory('equality')], [c_137, c_14])).
% 6.17/2.36  tff(c_52, plain, (![A_48, B_49]: (k3_tarski(k2_tarski(A_48, B_49))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.17/2.36  tff(c_181, plain, (![A_72, B_73]: (r1_tarski(A_72, k3_tarski(B_73)) | ~r2_hidden(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.17/2.36  tff(c_5944, plain, (![A_12383, A_12384, B_12385]: (r1_tarski(A_12383, k2_xboole_0(A_12384, B_12385)) | ~r2_hidden(A_12383, k2_tarski(A_12384, B_12385)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_181])).
% 6.17/2.36  tff(c_6035, plain, (![B_12682, A_12683]: (r1_tarski(B_12682, k2_xboole_0(A_12683, B_12682)))), inference(resolution, [status(thm)], [c_143, c_5944])).
% 6.17/2.36  tff(c_10, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.17/2.36  tff(c_102, plain, (![A_62, B_63]: (k3_tarski(k2_tarski(A_62, B_63))=k2_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.17/2.36  tff(c_189, plain, (![A_74, B_75]: (k3_tarski(k2_tarski(A_74, B_75))=k2_xboole_0(B_75, A_74))), inference(superposition, [status(thm), theory('equality')], [c_10, c_102])).
% 6.17/2.36  tff(c_198, plain, (![B_75, A_74]: (k2_xboole_0(B_75, A_74)=k2_xboole_0(A_74, B_75))), inference(superposition, [status(thm), theory('equality')], [c_189, c_52])).
% 6.17/2.36  tff(c_56, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_4'), '#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.17/2.36  tff(c_218, plain, (r1_tarski(k2_xboole_0('#skF_5', k1_tarski('#skF_4')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_198, c_56])).
% 6.17/2.36  tff(c_325, plain, (![A_94, C_95, B_96]: (r1_tarski(A_94, C_95) | ~r1_tarski(B_96, C_95) | ~r1_tarski(A_94, B_96))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.17/2.36  tff(c_333, plain, (![A_94]: (r1_tarski(A_94, '#skF_5') | ~r1_tarski(A_94, k2_xboole_0('#skF_5', k1_tarski('#skF_4'))))), inference(resolution, [status(thm)], [c_218, c_325])).
% 6.17/2.36  tff(c_6084, plain, (r1_tarski(k1_tarski('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_6035, c_333])).
% 6.17/2.36  tff(c_36, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.17/2.36  tff(c_155, plain, (![B_67, A_68]: (r2_hidden(B_67, k2_tarski(A_68, B_67)))), inference(superposition, [status(thm), theory('equality')], [c_137, c_14])).
% 6.17/2.36  tff(c_164, plain, (![A_18]: (r2_hidden(A_18, k1_tarski(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_155])).
% 6.17/2.36  tff(c_270, plain, (![C_86, B_87, A_88]: (r2_hidden(C_86, B_87) | ~r2_hidden(C_86, A_88) | ~r1_tarski(A_88, B_87))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.17/2.36  tff(c_287, plain, (![A_18, B_87]: (r2_hidden(A_18, B_87) | ~r1_tarski(k1_tarski(A_18), B_87))), inference(resolution, [status(thm)], [c_164, c_270])).
% 6.17/2.36  tff(c_6101, plain, (r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_6084, c_287])).
% 6.17/2.36  tff(c_6107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_6101])).
% 6.17/2.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.17/2.36  
% 6.17/2.36  Inference rules
% 6.17/2.36  ----------------------
% 6.17/2.37  #Ref     : 0
% 6.17/2.37  #Sup     : 723
% 6.17/2.37  #Fact    : 18
% 6.17/2.37  #Define  : 0
% 6.17/2.37  #Split   : 0
% 6.17/2.37  #Chain   : 0
% 6.17/2.37  #Close   : 0
% 6.17/2.37  
% 6.17/2.37  Ordering : KBO
% 6.17/2.37  
% 6.17/2.37  Simplification rules
% 6.17/2.37  ----------------------
% 6.17/2.37  #Subsume      : 93
% 6.17/2.37  #Demod        : 177
% 6.17/2.37  #Tautology    : 189
% 6.17/2.37  #SimpNegUnit  : 1
% 6.17/2.37  #BackRed      : 1
% 6.17/2.37  
% 6.17/2.37  #Partial instantiations: 3870
% 6.17/2.37  #Strategies tried      : 1
% 6.17/2.37  
% 6.17/2.37  Timing (in seconds)
% 6.17/2.37  ----------------------
% 6.24/2.37  Preprocessing        : 0.46
% 6.24/2.37  Parsing              : 0.24
% 6.24/2.37  CNF conversion       : 0.04
% 6.24/2.37  Main loop            : 1.14
% 6.24/2.37  Inferencing          : 0.59
% 6.24/2.37  Reduction            : 0.31
% 6.24/2.37  Demodulation         : 0.25
% 6.24/2.37  BG Simplification    : 0.05
% 6.24/2.37  Subsumption          : 0.14
% 6.24/2.37  Abstraction          : 0.05
% 6.24/2.37  MUC search           : 0.00
% 6.24/2.37  Cooper               : 0.00
% 6.24/2.37  Total                : 1.63
% 6.24/2.37  Index Insertion      : 0.00
% 6.24/2.37  Index Deletion       : 0.00
% 6.24/2.37  Index Matching       : 0.00
% 6.24/2.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
