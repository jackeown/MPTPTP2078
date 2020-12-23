%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:19 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 101 expanded)
%              Number of leaves         :   21 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   86 ( 237 expanded)
%              Number of equality atoms :   53 ( 191 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_32,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_55,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_30,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_41,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_36,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_182,plain,(
    ! [A_45,C_46,B_47] :
      ( r1_tarski(A_45,C_46)
      | ~ r1_tarski(k2_xboole_0(A_45,B_47),C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_210,plain,(
    ! [A_48,B_49] : r1_tarski(A_48,k2_xboole_0(A_48,B_49)) ),
    inference(resolution,[status(thm)],[c_6,c_182])).

tff(c_231,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_210])).

tff(c_552,plain,(
    ! [B_69,A_70] :
      ( k1_tarski(B_69) = A_70
      | k1_xboole_0 = A_70
      | ~ r1_tarski(A_70,k1_tarski(B_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_555,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_231,c_552])).

tff(c_569,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_41,c_555])).

tff(c_570,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_616,plain,(
    ! [A_77,B_78] :
      ( k2_xboole_0(A_77,B_78) = B_78
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_624,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_616])).

tff(c_791,plain,(
    ! [A_98,C_99,B_100] :
      ( r1_tarski(A_98,k2_xboole_0(C_99,B_100))
      | ~ r1_tarski(A_98,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_813,plain,(
    ! [A_98] :
      ( r1_tarski(A_98,k1_tarski('#skF_1'))
      | ~ r1_tarski(A_98,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_791])).

tff(c_571,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_22,plain,(
    ! [B_22,A_21] :
      ( k1_tarski(B_22) = A_21
      | k1_xboole_0 = A_21
      | ~ r1_tarski(A_21,k1_tarski(B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_958,plain,(
    ! [B_113,A_114] :
      ( k1_tarski(B_113) = A_114
      | A_114 = '#skF_2'
      | ~ r1_tarski(A_114,k1_tarski(B_113)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_571,c_22])).

tff(c_974,plain,(
    ! [A_115] :
      ( k1_tarski('#skF_1') = A_115
      | A_115 = '#skF_2'
      | ~ r1_tarski(A_115,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_813,c_958])).

tff(c_978,plain,
    ( k1_tarski('#skF_1') = '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6,c_974])).

tff(c_981,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_570,c_978])).

tff(c_991,plain,(
    k2_xboole_0('#skF_3','#skF_3') = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_981,c_36])).

tff(c_993,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_624,c_991])).

tff(c_995,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_570,c_993])).

tff(c_996,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_997,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_34,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1021,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_997,c_997,c_34])).

tff(c_1006,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_997,c_36])).

tff(c_1302,plain,(
    ! [A_145,C_146,B_147] :
      ( r1_tarski(A_145,k2_xboole_0(C_146,B_147))
      | ~ r1_tarski(A_145,B_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1331,plain,(
    ! [A_145] :
      ( r1_tarski(A_145,'#skF_2')
      | ~ r1_tarski(A_145,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1006,c_1302])).

tff(c_1337,plain,(
    ! [B_148,A_149] :
      ( k1_tarski(B_148) = A_149
      | k1_xboole_0 = A_149
      | ~ r1_tarski(A_149,k1_tarski(B_148)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1344,plain,(
    ! [A_149] :
      ( k1_tarski('#skF_1') = A_149
      | k1_xboole_0 = A_149
      | ~ r1_tarski(A_149,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_997,c_1337])).

tff(c_1384,plain,(
    ! [A_151] :
      ( A_151 = '#skF_2'
      | k1_xboole_0 = A_151
      | ~ r1_tarski(A_151,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_997,c_1344])).

tff(c_1425,plain,(
    ! [A_153] :
      ( A_153 = '#skF_2'
      | k1_xboole_0 = A_153
      | ~ r1_tarski(A_153,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1331,c_1384])).

tff(c_1433,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6,c_1425])).

tff(c_1441,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_996,c_1021,c_1433])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:23:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.42  
% 2.74/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.43  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.74/1.43  
% 2.74/1.43  %Foreground sorts:
% 2.74/1.43  
% 2.74/1.43  
% 2.74/1.43  %Background operators:
% 2.74/1.43  
% 2.74/1.43  
% 2.74/1.43  %Foreground operators:
% 2.74/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.74/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.74/1.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.74/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.74/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.74/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.74/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.74/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.74/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.74/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.74/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.43  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.74/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.74/1.43  
% 2.95/1.44  tff(f_78, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.95/1.44  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.95/1.44  tff(f_39, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.95/1.44  tff(f_57, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.95/1.44  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.95/1.44  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.95/1.44  tff(c_32, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.95/1.44  tff(c_55, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_32])).
% 2.95/1.44  tff(c_30, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.95/1.44  tff(c_41, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_30])).
% 2.95/1.44  tff(c_36, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.95/1.44  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.95/1.44  tff(c_182, plain, (![A_45, C_46, B_47]: (r1_tarski(A_45, C_46) | ~r1_tarski(k2_xboole_0(A_45, B_47), C_46))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.95/1.44  tff(c_210, plain, (![A_48, B_49]: (r1_tarski(A_48, k2_xboole_0(A_48, B_49)))), inference(resolution, [status(thm)], [c_6, c_182])).
% 2.95/1.44  tff(c_231, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_210])).
% 2.95/1.44  tff(c_552, plain, (![B_69, A_70]: (k1_tarski(B_69)=A_70 | k1_xboole_0=A_70 | ~r1_tarski(A_70, k1_tarski(B_69)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.95/1.44  tff(c_555, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_231, c_552])).
% 2.95/1.44  tff(c_569, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_41, c_555])).
% 2.95/1.44  tff(c_570, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_32])).
% 2.95/1.44  tff(c_616, plain, (![A_77, B_78]: (k2_xboole_0(A_77, B_78)=B_78 | ~r1_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.95/1.44  tff(c_624, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_616])).
% 2.95/1.44  tff(c_791, plain, (![A_98, C_99, B_100]: (r1_tarski(A_98, k2_xboole_0(C_99, B_100)) | ~r1_tarski(A_98, B_100))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.95/1.44  tff(c_813, plain, (![A_98]: (r1_tarski(A_98, k1_tarski('#skF_1')) | ~r1_tarski(A_98, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_791])).
% 2.95/1.44  tff(c_571, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_32])).
% 2.95/1.44  tff(c_22, plain, (![B_22, A_21]: (k1_tarski(B_22)=A_21 | k1_xboole_0=A_21 | ~r1_tarski(A_21, k1_tarski(B_22)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.95/1.44  tff(c_958, plain, (![B_113, A_114]: (k1_tarski(B_113)=A_114 | A_114='#skF_2' | ~r1_tarski(A_114, k1_tarski(B_113)))), inference(demodulation, [status(thm), theory('equality')], [c_571, c_22])).
% 2.95/1.44  tff(c_974, plain, (![A_115]: (k1_tarski('#skF_1')=A_115 | A_115='#skF_2' | ~r1_tarski(A_115, '#skF_3'))), inference(resolution, [status(thm)], [c_813, c_958])).
% 2.95/1.44  tff(c_978, plain, (k1_tarski('#skF_1')='#skF_3' | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_6, c_974])).
% 2.95/1.44  tff(c_981, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_570, c_978])).
% 2.95/1.44  tff(c_991, plain, (k2_xboole_0('#skF_3', '#skF_3')=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_981, c_36])).
% 2.95/1.44  tff(c_993, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_624, c_991])).
% 2.95/1.44  tff(c_995, plain, $false, inference(negUnitSimplification, [status(thm)], [c_570, c_993])).
% 2.95/1.44  tff(c_996, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_30])).
% 2.95/1.44  tff(c_997, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_30])).
% 2.95/1.44  tff(c_34, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.95/1.44  tff(c_1021, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_997, c_997, c_34])).
% 2.95/1.44  tff(c_1006, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_997, c_36])).
% 2.95/1.44  tff(c_1302, plain, (![A_145, C_146, B_147]: (r1_tarski(A_145, k2_xboole_0(C_146, B_147)) | ~r1_tarski(A_145, B_147))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.95/1.44  tff(c_1331, plain, (![A_145]: (r1_tarski(A_145, '#skF_2') | ~r1_tarski(A_145, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1006, c_1302])).
% 2.95/1.44  tff(c_1337, plain, (![B_148, A_149]: (k1_tarski(B_148)=A_149 | k1_xboole_0=A_149 | ~r1_tarski(A_149, k1_tarski(B_148)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.95/1.44  tff(c_1344, plain, (![A_149]: (k1_tarski('#skF_1')=A_149 | k1_xboole_0=A_149 | ~r1_tarski(A_149, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_997, c_1337])).
% 2.95/1.44  tff(c_1384, plain, (![A_151]: (A_151='#skF_2' | k1_xboole_0=A_151 | ~r1_tarski(A_151, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_997, c_1344])).
% 2.95/1.44  tff(c_1425, plain, (![A_153]: (A_153='#skF_2' | k1_xboole_0=A_153 | ~r1_tarski(A_153, '#skF_3'))), inference(resolution, [status(thm)], [c_1331, c_1384])).
% 2.95/1.44  tff(c_1433, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_6, c_1425])).
% 2.95/1.44  tff(c_1441, plain, $false, inference(negUnitSimplification, [status(thm)], [c_996, c_1021, c_1433])).
% 2.95/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.44  
% 2.95/1.44  Inference rules
% 2.95/1.44  ----------------------
% 2.95/1.44  #Ref     : 0
% 2.95/1.44  #Sup     : 314
% 2.95/1.44  #Fact    : 0
% 2.95/1.44  #Define  : 0
% 2.95/1.44  #Split   : 3
% 2.95/1.44  #Chain   : 0
% 2.95/1.44  #Close   : 0
% 2.95/1.44  
% 2.95/1.44  Ordering : KBO
% 2.95/1.44  
% 2.95/1.44  Simplification rules
% 2.95/1.44  ----------------------
% 2.95/1.44  #Subsume      : 9
% 2.95/1.44  #Demod        : 132
% 2.95/1.44  #Tautology    : 193
% 2.95/1.44  #SimpNegUnit  : 11
% 2.95/1.44  #BackRed      : 15
% 2.95/1.44  
% 2.95/1.44  #Partial instantiations: 0
% 2.95/1.44  #Strategies tried      : 1
% 2.95/1.44  
% 2.95/1.44  Timing (in seconds)
% 2.95/1.44  ----------------------
% 2.95/1.44  Preprocessing        : 0.30
% 2.95/1.44  Parsing              : 0.16
% 2.95/1.44  CNF conversion       : 0.02
% 2.95/1.44  Main loop            : 0.38
% 2.95/1.44  Inferencing          : 0.14
% 2.95/1.44  Reduction            : 0.12
% 2.95/1.44  Demodulation         : 0.09
% 2.95/1.44  BG Simplification    : 0.02
% 2.95/1.44  Subsumption          : 0.07
% 2.95/1.44  Abstraction          : 0.02
% 2.95/1.44  MUC search           : 0.00
% 2.95/1.44  Cooper               : 0.00
% 2.95/1.44  Total                : 0.71
% 2.95/1.44  Index Insertion      : 0.00
% 2.95/1.44  Index Deletion       : 0.00
% 2.95/1.44  Index Matching       : 0.00
% 2.95/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
