%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:06 EST 2020

% Result     : Theorem 3.42s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 121 expanded)
%              Number of leaves         :   24 (  49 expanded)
%              Depth                    :    9
%              Number of atoms          :   86 ( 252 expanded)
%              Number of equality atoms :   59 ( 212 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(c_42,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_69,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_40,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_51,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_46,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_65,plain,(
    ! [A_35,B_36] : r1_tarski(A_35,k2_xboole_0(A_35,B_36)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_68,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_65])).

tff(c_606,plain,(
    ! [B_68,A_69] :
      ( k1_tarski(B_68) = A_69
      | k1_xboole_0 = A_69
      | ~ r1_tarski(A_69,k1_tarski(B_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_616,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_68,c_606])).

tff(c_629,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_51,c_616])).

tff(c_631,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_888,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_631,c_10])).

tff(c_630,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_654,plain,(
    ! [B_73,A_74] : k2_xboole_0(B_73,A_74) = k2_xboole_0(A_74,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_16,B_17] : r1_tarski(A_16,k2_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_711,plain,(
    ! [A_75,B_76] : r1_tarski(A_75,k2_xboole_0(B_76,A_75)) ),
    inference(superposition,[status(thm),theory(equality)],[c_654,c_22])).

tff(c_720,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_711])).

tff(c_1158,plain,(
    ! [B_99,A_100] :
      ( B_99 = A_100
      | ~ r1_tarski(B_99,A_100)
      | ~ r1_tarski(A_100,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1164,plain,
    ( k1_tarski('#skF_1') = '#skF_3'
    | ~ r1_tarski(k1_tarski('#skF_1'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_720,c_1158])).

tff(c_1177,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_630,c_1164])).

tff(c_1188,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_3') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_888,c_1177])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_724,plain,(
    ! [A_77,B_78] :
      ( k4_xboole_0(A_77,B_78) = '#skF_2'
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_631,c_12])).

tff(c_745,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_724])).

tff(c_895,plain,(
    ! [A_92,B_93] : k2_xboole_0(A_92,k4_xboole_0(B_93,A_92)) = k2_xboole_0(A_92,B_93) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_941,plain,(
    ! [B_94] : k2_xboole_0(B_94,B_94) = k2_xboole_0(B_94,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_745,c_895])).

tff(c_699,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_654])).

tff(c_959,plain,(
    k2_xboole_0('#skF_3','#skF_3') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_941,c_699])).

tff(c_1268,plain,(
    ! [A_103,B_104] : k4_xboole_0(k2_xboole_0(A_103,B_104),B_104) = k4_xboole_0(A_103,B_104) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1289,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_3') = k4_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_959,c_1268])).

tff(c_1319,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_745,c_1289])).

tff(c_1321,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1188,c_1319])).

tff(c_1322,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1323,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_44,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1352,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1323,c_1323,c_44])).

tff(c_1367,plain,(
    ! [B_110,A_111] : k2_xboole_0(B_110,A_111) = k2_xboole_0(A_111,B_110) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1330,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1323,c_46])).

tff(c_1394,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1367,c_1330])).

tff(c_1430,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1394,c_22])).

tff(c_2394,plain,(
    ! [B_149,A_150] :
      ( k1_tarski(B_149) = A_150
      | k1_xboole_0 = A_150
      | ~ r1_tarski(A_150,k1_tarski(B_149)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2401,plain,(
    ! [A_150] :
      ( k1_tarski('#skF_1') = A_150
      | k1_xboole_0 = A_150
      | ~ r1_tarski(A_150,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1323,c_2394])).

tff(c_2479,plain,(
    ! [A_152] :
      ( A_152 = '#skF_2'
      | k1_xboole_0 = A_152
      | ~ r1_tarski(A_152,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1323,c_2401])).

tff(c_2486,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1430,c_2479])).

tff(c_2498,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1322,c_1352,c_2486])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:09:27 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.42/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.56  
% 3.42/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.56  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.42/1.56  
% 3.42/1.56  %Foreground sorts:
% 3.42/1.56  
% 3.42/1.56  
% 3.42/1.56  %Background operators:
% 3.42/1.56  
% 3.42/1.56  
% 3.42/1.56  %Foreground operators:
% 3.42/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.42/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.42/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.42/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.42/1.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.42/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.42/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.42/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.42/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.42/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.42/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.42/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.42/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.42/1.56  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.42/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.42/1.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.42/1.56  
% 3.42/1.58  tff(f_82, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.42/1.58  tff(f_47, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.42/1.58  tff(f_61, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.42/1.58  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.42/1.58  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.42/1.58  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.42/1.58  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.42/1.58  tff(f_41, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 3.42/1.58  tff(c_42, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.42/1.58  tff(c_69, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_42])).
% 3.42/1.58  tff(c_40, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.42/1.58  tff(c_51, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_40])).
% 3.42/1.58  tff(c_46, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.42/1.58  tff(c_65, plain, (![A_35, B_36]: (r1_tarski(A_35, k2_xboole_0(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.42/1.58  tff(c_68, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_65])).
% 3.42/1.58  tff(c_606, plain, (![B_68, A_69]: (k1_tarski(B_68)=A_69 | k1_xboole_0=A_69 | ~r1_tarski(A_69, k1_tarski(B_68)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.42/1.58  tff(c_616, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_68, c_606])).
% 3.42/1.58  tff(c_629, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_51, c_616])).
% 3.42/1.58  tff(c_631, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_42])).
% 3.42/1.58  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.42/1.58  tff(c_888, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_631, c_10])).
% 3.42/1.58  tff(c_630, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_42])).
% 3.42/1.58  tff(c_654, plain, (![B_73, A_74]: (k2_xboole_0(B_73, A_74)=k2_xboole_0(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.42/1.58  tff(c_22, plain, (![A_16, B_17]: (r1_tarski(A_16, k2_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.42/1.58  tff(c_711, plain, (![A_75, B_76]: (r1_tarski(A_75, k2_xboole_0(B_76, A_75)))), inference(superposition, [status(thm), theory('equality')], [c_654, c_22])).
% 3.42/1.58  tff(c_720, plain, (r1_tarski('#skF_3', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_711])).
% 3.42/1.58  tff(c_1158, plain, (![B_99, A_100]: (B_99=A_100 | ~r1_tarski(B_99, A_100) | ~r1_tarski(A_100, B_99))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.42/1.58  tff(c_1164, plain, (k1_tarski('#skF_1')='#skF_3' | ~r1_tarski(k1_tarski('#skF_1'), '#skF_3')), inference(resolution, [status(thm)], [c_720, c_1158])).
% 3.42/1.58  tff(c_1177, plain, (~r1_tarski(k1_tarski('#skF_1'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_630, c_1164])).
% 3.42/1.58  tff(c_1188, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_3')!='#skF_2'), inference(resolution, [status(thm)], [c_888, c_1177])).
% 3.42/1.58  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.42/1.58  tff(c_12, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.42/1.58  tff(c_724, plain, (![A_77, B_78]: (k4_xboole_0(A_77, B_78)='#skF_2' | ~r1_tarski(A_77, B_78))), inference(demodulation, [status(thm), theory('equality')], [c_631, c_12])).
% 3.42/1.58  tff(c_745, plain, (![B_4]: (k4_xboole_0(B_4, B_4)='#skF_2')), inference(resolution, [status(thm)], [c_8, c_724])).
% 3.42/1.58  tff(c_895, plain, (![A_92, B_93]: (k2_xboole_0(A_92, k4_xboole_0(B_93, A_92))=k2_xboole_0(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.42/1.58  tff(c_941, plain, (![B_94]: (k2_xboole_0(B_94, B_94)=k2_xboole_0(B_94, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_745, c_895])).
% 3.42/1.58  tff(c_699, plain, (k2_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_46, c_654])).
% 3.42/1.58  tff(c_959, plain, (k2_xboole_0('#skF_3', '#skF_3')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_941, c_699])).
% 3.42/1.58  tff(c_1268, plain, (![A_103, B_104]: (k4_xboole_0(k2_xboole_0(A_103, B_104), B_104)=k4_xboole_0(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.42/1.58  tff(c_1289, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_3')=k4_xboole_0('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_959, c_1268])).
% 3.42/1.58  tff(c_1319, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_745, c_1289])).
% 3.42/1.58  tff(c_1321, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1188, c_1319])).
% 3.42/1.58  tff(c_1322, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_40])).
% 3.42/1.58  tff(c_1323, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_40])).
% 3.42/1.58  tff(c_44, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.42/1.58  tff(c_1352, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1323, c_1323, c_44])).
% 3.42/1.58  tff(c_1367, plain, (![B_110, A_111]: (k2_xboole_0(B_110, A_111)=k2_xboole_0(A_111, B_110))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.42/1.58  tff(c_1330, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1323, c_46])).
% 3.42/1.58  tff(c_1394, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1367, c_1330])).
% 3.42/1.58  tff(c_1430, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1394, c_22])).
% 3.42/1.58  tff(c_2394, plain, (![B_149, A_150]: (k1_tarski(B_149)=A_150 | k1_xboole_0=A_150 | ~r1_tarski(A_150, k1_tarski(B_149)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.42/1.58  tff(c_2401, plain, (![A_150]: (k1_tarski('#skF_1')=A_150 | k1_xboole_0=A_150 | ~r1_tarski(A_150, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1323, c_2394])).
% 3.42/1.58  tff(c_2479, plain, (![A_152]: (A_152='#skF_2' | k1_xboole_0=A_152 | ~r1_tarski(A_152, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1323, c_2401])).
% 3.42/1.58  tff(c_2486, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1430, c_2479])).
% 3.42/1.58  tff(c_2498, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1322, c_1352, c_2486])).
% 3.42/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.58  
% 3.42/1.58  Inference rules
% 3.42/1.58  ----------------------
% 3.42/1.58  #Ref     : 0
% 3.42/1.58  #Sup     : 659
% 3.42/1.58  #Fact    : 0
% 3.42/1.58  #Define  : 0
% 3.42/1.58  #Split   : 6
% 3.42/1.58  #Chain   : 0
% 3.42/1.58  #Close   : 0
% 3.42/1.58  
% 3.42/1.58  Ordering : KBO
% 3.42/1.58  
% 3.42/1.58  Simplification rules
% 3.42/1.58  ----------------------
% 3.42/1.58  #Subsume      : 36
% 3.42/1.58  #Demod        : 301
% 3.42/1.58  #Tautology    : 422
% 3.42/1.58  #SimpNegUnit  : 9
% 3.42/1.58  #BackRed      : 13
% 3.42/1.58  
% 3.42/1.58  #Partial instantiations: 0
% 3.42/1.58  #Strategies tried      : 1
% 3.42/1.58  
% 3.42/1.58  Timing (in seconds)
% 3.42/1.58  ----------------------
% 3.63/1.58  Preprocessing        : 0.30
% 3.63/1.58  Parsing              : 0.16
% 3.63/1.58  CNF conversion       : 0.02
% 3.63/1.58  Main loop            : 0.54
% 3.63/1.58  Inferencing          : 0.18
% 3.63/1.58  Reduction            : 0.21
% 3.63/1.58  Demodulation         : 0.16
% 3.63/1.58  BG Simplification    : 0.02
% 3.63/1.58  Subsumption          : 0.08
% 3.63/1.58  Abstraction          : 0.02
% 3.63/1.58  MUC search           : 0.00
% 3.63/1.58  Cooper               : 0.00
% 3.63/1.58  Total                : 0.86
% 3.63/1.58  Index Insertion      : 0.00
% 3.63/1.58  Index Deletion       : 0.00
% 3.63/1.58  Index Matching       : 0.00
% 3.63/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
