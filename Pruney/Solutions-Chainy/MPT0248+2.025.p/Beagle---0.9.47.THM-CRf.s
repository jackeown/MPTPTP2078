%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:07 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 106 expanded)
%              Number of leaves         :   17 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :   83 ( 240 expanded)
%              Number of equality atoms :   54 ( 196 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_24,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_47,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_22,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_46,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_28,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_109,plain,(
    ! [A_20,C_21,B_22] :
      ( r1_tarski(A_20,C_21)
      | ~ r1_tarski(k2_xboole_0(A_20,B_22),C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_139,plain,(
    ! [A_24,B_25] : r1_tarski(A_24,k2_xboole_0(A_24,B_25)) ),
    inference(resolution,[status(thm)],[c_8,c_109])).

tff(c_161,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_139])).

tff(c_402,plain,(
    ! [B_37,A_38] :
      ( k1_tarski(B_37) = A_38
      | k1_xboole_0 = A_38
      | ~ r1_tarski(A_38,k1_tarski(B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_405,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_161,c_402])).

tff(c_419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_46,c_405])).

tff(c_420,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_480,plain,(
    ! [A_42,B_43] :
      ( k2_xboole_0(A_42,B_43) = B_43
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_488,plain,(
    ! [B_4] : k2_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_480])).

tff(c_428,plain,(
    ! [B_40,A_41] : k2_xboole_0(B_40,A_41) = k2_xboole_0(A_41,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_443,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_428,c_28])).

tff(c_517,plain,(
    ! [A_48,C_49,B_50] :
      ( r1_tarski(A_48,C_49)
      | ~ r1_tarski(k2_xboole_0(A_48,B_50),C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_541,plain,(
    ! [A_51,B_52] : r1_tarski(A_51,k2_xboole_0(A_51,B_52)) ),
    inference(resolution,[status(thm)],[c_8,c_517])).

tff(c_559,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_443,c_541])).

tff(c_421,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( k1_tarski(B_12) = A_11
      | k1_xboole_0 = A_11
      | ~ r1_tarski(A_11,k1_tarski(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_623,plain,(
    ! [B_55,A_56] :
      ( k1_tarski(B_55) = A_56
      | A_56 = '#skF_2'
      | ~ r1_tarski(A_56,k1_tarski(B_55)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_16])).

tff(c_626,plain,
    ( k1_tarski('#skF_1') = '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_559,c_623])).

tff(c_636,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_420,c_626])).

tff(c_643,plain,(
    k2_xboole_0('#skF_3','#skF_3') = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_636,c_443])).

tff(c_648,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_488,c_643])).

tff(c_650,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_420,c_648])).

tff(c_651,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_652,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_26,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_667,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_652,c_26])).

tff(c_668,plain,(
    ! [B_57,A_58] : k2_xboole_0(B_57,A_58) = k2_xboole_0(A_58,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_653,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_28])).

tff(c_683,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_668,c_653])).

tff(c_793,plain,(
    ! [A_65,C_66,B_67] :
      ( r1_tarski(A_65,C_66)
      | ~ r1_tarski(k2_xboole_0(A_65,B_67),C_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_823,plain,(
    ! [A_68,B_69] : r1_tarski(A_68,k2_xboole_0(A_68,B_69)) ),
    inference(resolution,[status(thm)],[c_8,c_793])).

tff(c_847,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_683,c_823])).

tff(c_921,plain,(
    ! [B_72,A_73] :
      ( k1_tarski(B_72) = A_73
      | k1_xboole_0 = A_73
      | ~ r1_tarski(A_73,k1_tarski(B_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_924,plain,(
    ! [A_73] :
      ( k1_tarski('#skF_1') = A_73
      | k1_xboole_0 = A_73
      | ~ r1_tarski(A_73,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_652,c_921])).

tff(c_1010,plain,(
    ! [A_77] :
      ( A_77 = '#skF_2'
      | k1_xboole_0 = A_77
      | ~ r1_tarski(A_77,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_924])).

tff(c_1013,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_847,c_1010])).

tff(c_1024,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_651,c_667,c_1013])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:08:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.38  
% 2.44/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.39  %$ r1_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.44/1.39  
% 2.44/1.39  %Foreground sorts:
% 2.44/1.39  
% 2.44/1.39  
% 2.44/1.39  %Background operators:
% 2.44/1.39  
% 2.44/1.39  
% 2.44/1.39  %Foreground operators:
% 2.44/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.44/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.44/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.44/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.44/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.44/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.44/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.44/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.44/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.44/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.44/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.44/1.39  
% 2.74/1.40  tff(f_68, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.74/1.40  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.74/1.40  tff(f_37, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.74/1.40  tff(f_49, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.74/1.40  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.74/1.40  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.74/1.40  tff(c_24, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.74/1.40  tff(c_47, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_24])).
% 2.74/1.40  tff(c_22, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.74/1.40  tff(c_46, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_22])).
% 2.74/1.40  tff(c_28, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.74/1.40  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.74/1.40  tff(c_109, plain, (![A_20, C_21, B_22]: (r1_tarski(A_20, C_21) | ~r1_tarski(k2_xboole_0(A_20, B_22), C_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.74/1.40  tff(c_139, plain, (![A_24, B_25]: (r1_tarski(A_24, k2_xboole_0(A_24, B_25)))), inference(resolution, [status(thm)], [c_8, c_109])).
% 2.74/1.40  tff(c_161, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_139])).
% 2.74/1.40  tff(c_402, plain, (![B_37, A_38]: (k1_tarski(B_37)=A_38 | k1_xboole_0=A_38 | ~r1_tarski(A_38, k1_tarski(B_37)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.74/1.40  tff(c_405, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_161, c_402])).
% 2.74/1.40  tff(c_419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_46, c_405])).
% 2.74/1.40  tff(c_420, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_24])).
% 2.74/1.40  tff(c_480, plain, (![A_42, B_43]: (k2_xboole_0(A_42, B_43)=B_43 | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.74/1.40  tff(c_488, plain, (![B_4]: (k2_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_480])).
% 2.74/1.40  tff(c_428, plain, (![B_40, A_41]: (k2_xboole_0(B_40, A_41)=k2_xboole_0(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.74/1.40  tff(c_443, plain, (k2_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_428, c_28])).
% 2.74/1.40  tff(c_517, plain, (![A_48, C_49, B_50]: (r1_tarski(A_48, C_49) | ~r1_tarski(k2_xboole_0(A_48, B_50), C_49))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.74/1.40  tff(c_541, plain, (![A_51, B_52]: (r1_tarski(A_51, k2_xboole_0(A_51, B_52)))), inference(resolution, [status(thm)], [c_8, c_517])).
% 2.74/1.40  tff(c_559, plain, (r1_tarski('#skF_3', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_443, c_541])).
% 2.74/1.40  tff(c_421, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_24])).
% 2.74/1.40  tff(c_16, plain, (![B_12, A_11]: (k1_tarski(B_12)=A_11 | k1_xboole_0=A_11 | ~r1_tarski(A_11, k1_tarski(B_12)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.74/1.40  tff(c_623, plain, (![B_55, A_56]: (k1_tarski(B_55)=A_56 | A_56='#skF_2' | ~r1_tarski(A_56, k1_tarski(B_55)))), inference(demodulation, [status(thm), theory('equality')], [c_421, c_16])).
% 2.74/1.40  tff(c_626, plain, (k1_tarski('#skF_1')='#skF_3' | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_559, c_623])).
% 2.74/1.40  tff(c_636, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_420, c_626])).
% 2.74/1.40  tff(c_643, plain, (k2_xboole_0('#skF_3', '#skF_3')=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_636, c_443])).
% 2.74/1.40  tff(c_648, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_488, c_643])).
% 2.74/1.40  tff(c_650, plain, $false, inference(negUnitSimplification, [status(thm)], [c_420, c_648])).
% 2.74/1.40  tff(c_651, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_22])).
% 2.74/1.40  tff(c_652, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_22])).
% 2.74/1.40  tff(c_26, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.74/1.40  tff(c_667, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_652, c_652, c_26])).
% 2.74/1.40  tff(c_668, plain, (![B_57, A_58]: (k2_xboole_0(B_57, A_58)=k2_xboole_0(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.74/1.40  tff(c_653, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_652, c_28])).
% 2.74/1.40  tff(c_683, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_668, c_653])).
% 2.74/1.40  tff(c_793, plain, (![A_65, C_66, B_67]: (r1_tarski(A_65, C_66) | ~r1_tarski(k2_xboole_0(A_65, B_67), C_66))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.74/1.40  tff(c_823, plain, (![A_68, B_69]: (r1_tarski(A_68, k2_xboole_0(A_68, B_69)))), inference(resolution, [status(thm)], [c_8, c_793])).
% 2.74/1.40  tff(c_847, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_683, c_823])).
% 2.74/1.40  tff(c_921, plain, (![B_72, A_73]: (k1_tarski(B_72)=A_73 | k1_xboole_0=A_73 | ~r1_tarski(A_73, k1_tarski(B_72)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.74/1.40  tff(c_924, plain, (![A_73]: (k1_tarski('#skF_1')=A_73 | k1_xboole_0=A_73 | ~r1_tarski(A_73, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_652, c_921])).
% 2.74/1.40  tff(c_1010, plain, (![A_77]: (A_77='#skF_2' | k1_xboole_0=A_77 | ~r1_tarski(A_77, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_652, c_924])).
% 2.74/1.40  tff(c_1013, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_847, c_1010])).
% 2.74/1.40  tff(c_1024, plain, $false, inference(negUnitSimplification, [status(thm)], [c_651, c_667, c_1013])).
% 2.74/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.40  
% 2.74/1.40  Inference rules
% 2.74/1.40  ----------------------
% 2.74/1.40  #Ref     : 0
% 2.74/1.40  #Sup     : 244
% 2.74/1.40  #Fact    : 0
% 2.74/1.40  #Define  : 0
% 2.74/1.40  #Split   : 3
% 2.74/1.40  #Chain   : 0
% 2.74/1.40  #Close   : 0
% 2.74/1.40  
% 2.74/1.40  Ordering : KBO
% 2.74/1.40  
% 2.74/1.40  Simplification rules
% 2.74/1.40  ----------------------
% 2.74/1.40  #Subsume      : 2
% 2.74/1.40  #Demod        : 96
% 2.74/1.40  #Tautology    : 149
% 2.74/1.40  #SimpNegUnit  : 8
% 2.74/1.40  #BackRed      : 9
% 2.74/1.40  
% 2.74/1.40  #Partial instantiations: 0
% 2.74/1.40  #Strategies tried      : 1
% 2.74/1.40  
% 2.74/1.40  Timing (in seconds)
% 2.74/1.40  ----------------------
% 2.74/1.40  Preprocessing        : 0.29
% 2.74/1.40  Parsing              : 0.15
% 2.74/1.40  CNF conversion       : 0.02
% 2.74/1.40  Main loop            : 0.34
% 2.74/1.40  Inferencing          : 0.12
% 2.74/1.40  Reduction            : 0.13
% 2.74/1.40  Demodulation         : 0.10
% 2.74/1.40  BG Simplification    : 0.02
% 2.74/1.40  Subsumption          : 0.06
% 2.74/1.40  Abstraction          : 0.02
% 2.74/1.40  MUC search           : 0.00
% 2.74/1.40  Cooper               : 0.00
% 2.74/1.40  Total                : 0.66
% 2.74/1.40  Index Insertion      : 0.00
% 2.74/1.40  Index Deletion       : 0.00
% 2.74/1.40  Index Matching       : 0.00
% 2.74/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
