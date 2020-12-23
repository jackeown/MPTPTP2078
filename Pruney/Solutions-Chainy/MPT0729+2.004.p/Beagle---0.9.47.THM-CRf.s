%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:58 EST 2020

% Result     : Theorem 6.62s
% Output     : CNFRefutation 6.62s
% Verified   : 
% Statistics : Number of formulae       :   55 (  89 expanded)
%              Number of leaves         :   25 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :   61 ( 112 expanded)
%              Number of equality atoms :   21 (  49 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( k1_ordinal1(A) = k1_ordinal1(B)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_ordinal1)).

tff(f_66,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_40,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_53,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,C) )
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_32,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_34,plain,(
    k1_ordinal1('#skF_2') = k1_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_28,plain,(
    ! [A_25] : k2_xboole_0(A_25,k1_tarski(A_25)) = k1_ordinal1(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_111,plain,(
    ! [A_45,B_46] : k3_tarski(k2_tarski(A_45,B_46)) = k2_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_433,plain,(
    ! [B_95,A_96] : k3_tarski(k2_tarski(B_95,A_96)) = k2_xboole_0(A_96,B_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_111])).

tff(c_18,plain,(
    ! [A_18,B_19] : k3_tarski(k2_tarski(A_18,B_19)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_459,plain,(
    ! [B_97,A_98] : k2_xboole_0(B_97,A_98) = k2_xboole_0(A_98,B_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_433,c_18])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_536,plain,(
    ! [A_99,B_100] : r1_tarski(A_99,k2_xboole_0(B_100,A_99)) ),
    inference(superposition,[status(thm),theory(equality)],[c_459,c_6])).

tff(c_572,plain,(
    ! [A_101] : r1_tarski(k1_tarski(A_101),k1_ordinal1(A_101)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_536])).

tff(c_578,plain,(
    r1_tarski(k1_tarski('#skF_2'),k1_ordinal1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_572])).

tff(c_20,plain,(
    ! [A_20,B_21] :
      ( r1_xboole_0(k1_tarski(A_20),k1_tarski(B_21))
      | B_21 = A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_292,plain,(
    ! [A_71,B_72,C_73] :
      ( r1_tarski(A_71,B_72)
      | ~ r1_xboole_0(A_71,C_73)
      | ~ r1_tarski(A_71,k2_xboole_0(B_72,C_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_11356,plain,(
    ! [A_4320,A_4321] :
      ( r1_tarski(A_4320,A_4321)
      | ~ r1_xboole_0(A_4320,k1_tarski(A_4321))
      | ~ r1_tarski(A_4320,k1_ordinal1(A_4321)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_292])).

tff(c_13076,plain,(
    ! [A_5198,B_5199] :
      ( r1_tarski(k1_tarski(A_5198),B_5199)
      | ~ r1_tarski(k1_tarski(A_5198),k1_ordinal1(B_5199))
      | B_5199 = A_5198 ) ),
    inference(resolution,[status(thm)],[c_20,c_11356])).

tff(c_13111,plain,
    ( r1_tarski(k1_tarski('#skF_2'),'#skF_1')
    | '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_578,c_13076])).

tff(c_13125,plain,(
    r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_13111])).

tff(c_10,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_149,plain,(
    ! [B_48,C_49,A_50] :
      ( r2_hidden(B_48,C_49)
      | ~ r1_tarski(k2_tarski(A_50,B_48),C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_166,plain,(
    ! [A_10,C_49] :
      ( r2_hidden(A_10,C_49)
      | ~ r1_tarski(k1_tarski(A_10),C_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_149])).

tff(c_13204,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_13125,c_166])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_13249,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_13204,c_2])).

tff(c_563,plain,(
    ! [A_25] : r1_tarski(k1_tarski(A_25),k1_ordinal1(A_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_536])).

tff(c_13259,plain,(
    ! [A_5312] :
      ( r1_tarski(k1_tarski(A_5312),'#skF_2')
      | ~ r1_tarski(k1_tarski(A_5312),k1_ordinal1('#skF_1'))
      | A_5312 = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_13076])).

tff(c_13337,plain,
    ( r1_tarski(k1_tarski('#skF_1'),'#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_563,c_13259])).

tff(c_13345,plain,(
    r1_tarski(k1_tarski('#skF_1'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_13337])).

tff(c_13358,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_13345,c_166])).

tff(c_13432,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13249,c_13358])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:38:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.62/2.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.62/2.51  
% 6.62/2.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.62/2.51  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1
% 6.62/2.51  
% 6.62/2.51  %Foreground sorts:
% 6.62/2.51  
% 6.62/2.51  
% 6.62/2.51  %Background operators:
% 6.62/2.51  
% 6.62/2.51  
% 6.62/2.51  %Foreground operators:
% 6.62/2.51  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 6.62/2.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.62/2.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.62/2.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.62/2.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.62/2.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.62/2.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.62/2.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.62/2.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.62/2.51  tff('#skF_2', type, '#skF_2': $i).
% 6.62/2.51  tff('#skF_1', type, '#skF_1': $i).
% 6.62/2.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.62/2.51  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.62/2.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.62/2.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.62/2.51  
% 6.62/2.52  tff(f_76, negated_conjecture, ~(![A, B]: ((k1_ordinal1(A) = k1_ordinal1(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_ordinal1)).
% 6.62/2.52  tff(f_66, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 6.62/2.52  tff(f_40, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.62/2.52  tff(f_53, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.62/2.52  tff(f_38, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 6.62/2.52  tff(f_58, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 6.62/2.52  tff(f_36, axiom, (![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 6.62/2.52  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.62/2.52  tff(f_64, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 6.62/2.52  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 6.62/2.52  tff(c_32, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.62/2.52  tff(c_34, plain, (k1_ordinal1('#skF_2')=k1_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.62/2.52  tff(c_28, plain, (![A_25]: (k2_xboole_0(A_25, k1_tarski(A_25))=k1_ordinal1(A_25))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.62/2.52  tff(c_8, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.62/2.52  tff(c_111, plain, (![A_45, B_46]: (k3_tarski(k2_tarski(A_45, B_46))=k2_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.62/2.52  tff(c_433, plain, (![B_95, A_96]: (k3_tarski(k2_tarski(B_95, A_96))=k2_xboole_0(A_96, B_95))), inference(superposition, [status(thm), theory('equality')], [c_8, c_111])).
% 6.62/2.52  tff(c_18, plain, (![A_18, B_19]: (k3_tarski(k2_tarski(A_18, B_19))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.62/2.52  tff(c_459, plain, (![B_97, A_98]: (k2_xboole_0(B_97, A_98)=k2_xboole_0(A_98, B_97))), inference(superposition, [status(thm), theory('equality')], [c_433, c_18])).
% 6.62/2.52  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.62/2.52  tff(c_536, plain, (![A_99, B_100]: (r1_tarski(A_99, k2_xboole_0(B_100, A_99)))), inference(superposition, [status(thm), theory('equality')], [c_459, c_6])).
% 6.62/2.52  tff(c_572, plain, (![A_101]: (r1_tarski(k1_tarski(A_101), k1_ordinal1(A_101)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_536])).
% 6.62/2.52  tff(c_578, plain, (r1_tarski(k1_tarski('#skF_2'), k1_ordinal1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_572])).
% 6.62/2.52  tff(c_20, plain, (![A_20, B_21]: (r1_xboole_0(k1_tarski(A_20), k1_tarski(B_21)) | B_21=A_20)), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.62/2.52  tff(c_292, plain, (![A_71, B_72, C_73]: (r1_tarski(A_71, B_72) | ~r1_xboole_0(A_71, C_73) | ~r1_tarski(A_71, k2_xboole_0(B_72, C_73)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.62/2.52  tff(c_11356, plain, (![A_4320, A_4321]: (r1_tarski(A_4320, A_4321) | ~r1_xboole_0(A_4320, k1_tarski(A_4321)) | ~r1_tarski(A_4320, k1_ordinal1(A_4321)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_292])).
% 6.62/2.52  tff(c_13076, plain, (![A_5198, B_5199]: (r1_tarski(k1_tarski(A_5198), B_5199) | ~r1_tarski(k1_tarski(A_5198), k1_ordinal1(B_5199)) | B_5199=A_5198)), inference(resolution, [status(thm)], [c_20, c_11356])).
% 6.62/2.52  tff(c_13111, plain, (r1_tarski(k1_tarski('#skF_2'), '#skF_1') | '#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_578, c_13076])).
% 6.62/2.52  tff(c_13125, plain, (r1_tarski(k1_tarski('#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_32, c_13111])).
% 6.62/2.52  tff(c_10, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.62/2.52  tff(c_149, plain, (![B_48, C_49, A_50]: (r2_hidden(B_48, C_49) | ~r1_tarski(k2_tarski(A_50, B_48), C_49))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.62/2.52  tff(c_166, plain, (![A_10, C_49]: (r2_hidden(A_10, C_49) | ~r1_tarski(k1_tarski(A_10), C_49))), inference(superposition, [status(thm), theory('equality')], [c_10, c_149])).
% 6.62/2.52  tff(c_13204, plain, (r2_hidden('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_13125, c_166])).
% 6.62/2.52  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 6.62/2.52  tff(c_13249, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_13204, c_2])).
% 6.62/2.52  tff(c_563, plain, (![A_25]: (r1_tarski(k1_tarski(A_25), k1_ordinal1(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_536])).
% 6.62/2.52  tff(c_13259, plain, (![A_5312]: (r1_tarski(k1_tarski(A_5312), '#skF_2') | ~r1_tarski(k1_tarski(A_5312), k1_ordinal1('#skF_1')) | A_5312='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_34, c_13076])).
% 6.62/2.52  tff(c_13337, plain, (r1_tarski(k1_tarski('#skF_1'), '#skF_2') | '#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_563, c_13259])).
% 6.62/2.52  tff(c_13345, plain, (r1_tarski(k1_tarski('#skF_1'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_32, c_13337])).
% 6.62/2.52  tff(c_13358, plain, (r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_13345, c_166])).
% 6.62/2.52  tff(c_13432, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13249, c_13358])).
% 6.62/2.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.62/2.52  
% 6.62/2.52  Inference rules
% 6.62/2.52  ----------------------
% 6.62/2.52  #Ref     : 2
% 6.62/2.52  #Sup     : 2691
% 6.62/2.52  #Fact    : 2
% 6.62/2.52  #Define  : 0
% 6.62/2.52  #Split   : 4
% 6.62/2.52  #Chain   : 0
% 6.62/2.52  #Close   : 0
% 6.62/2.52  
% 6.62/2.52  Ordering : KBO
% 6.62/2.52  
% 6.62/2.52  Simplification rules
% 6.62/2.52  ----------------------
% 6.62/2.52  #Subsume      : 397
% 6.62/2.52  #Demod        : 313
% 6.62/2.52  #Tautology    : 134
% 6.62/2.52  #SimpNegUnit  : 5
% 6.62/2.52  #BackRed      : 0
% 6.62/2.52  
% 6.62/2.52  #Partial instantiations: 3330
% 6.62/2.52  #Strategies tried      : 1
% 6.62/2.52  
% 6.62/2.52  Timing (in seconds)
% 6.62/2.52  ----------------------
% 6.62/2.53  Preprocessing        : 0.29
% 6.62/2.53  Parsing              : 0.16
% 6.62/2.53  CNF conversion       : 0.02
% 6.62/2.53  Main loop            : 1.48
% 6.62/2.53  Inferencing          : 0.46
% 6.62/2.53  Reduction            : 0.61
% 6.62/2.53  Demodulation         : 0.44
% 6.62/2.53  BG Simplification    : 0.06
% 6.62/2.53  Subsumption          : 0.24
% 6.62/2.53  Abstraction          : 0.05
% 6.62/2.53  MUC search           : 0.00
% 6.62/2.53  Cooper               : 0.00
% 6.62/2.53  Total                : 1.81
% 6.62/2.53  Index Insertion      : 0.00
% 6.62/2.53  Index Deletion       : 0.00
% 6.62/2.53  Index Matching       : 0.00
% 6.62/2.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
