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
% DateTime   : Thu Dec  3 09:50:29 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :   55 (  77 expanded)
%              Number of leaves         :   29 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :   60 ( 113 expanded)
%              Number of equality atoms :   31 (  77 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_62,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_22,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_64,plain,(
    k2_xboole_0('#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_321,plain,(
    ! [D_65,B_66,A_67] :
      ( ~ r2_hidden(D_65,B_66)
      | r2_hidden(D_65,k2_xboole_0(A_67,B_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_343,plain,(
    ! [D_70] :
      ( ~ r2_hidden(D_70,'#skF_8')
      | r2_hidden(D_70,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_321])).

tff(c_28,plain,(
    ! [C_17,A_13] :
      ( C_17 = A_13
      | ~ r2_hidden(C_17,k1_tarski(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_348,plain,(
    ! [D_71] :
      ( D_71 = '#skF_6'
      | ~ r2_hidden(D_71,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_343,c_28])).

tff(c_352,plain,
    ( '#skF_3'('#skF_8') = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_22,c_348])).

tff(c_355,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_352])).

tff(c_359,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_355,c_22])).

tff(c_362,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_359])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_26,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_85,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_26])).

tff(c_491,plain,(
    ! [B_78,A_79] :
      ( k1_tarski(B_78) = A_79
      | k1_xboole_0 = A_79
      | ~ r1_tarski(A_79,k1_tarski(B_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_498,plain,
    ( k1_tarski('#skF_6') = '#skF_7'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_85,c_491])).

tff(c_508,plain,(
    k1_tarski('#skF_6') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_498])).

tff(c_48,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(k1_tarski(A_24),B_25)
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_804,plain,(
    ! [B_89] :
      ( r1_tarski('#skF_7',B_89)
      | ~ r2_hidden('#skF_6',B_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_508,c_48])).

tff(c_852,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_362,c_804])).

tff(c_24,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_865,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_852,c_24])).

tff(c_517,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_508,c_64])).

tff(c_866,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_865,c_517])).

tff(c_868,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_866])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:43:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.64/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.41  
% 2.64/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.41  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 2.64/1.41  
% 2.64/1.41  %Foreground sorts:
% 2.64/1.41  
% 2.64/1.41  
% 2.64/1.41  %Background operators:
% 2.64/1.41  
% 2.64/1.41  
% 2.64/1.41  %Foreground operators:
% 2.64/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.64/1.41  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 2.64/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.64/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.64/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.64/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.64/1.41  tff('#skF_7', type, '#skF_7': $i).
% 2.64/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.64/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.64/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.64/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.64/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.64/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.64/1.41  tff('#skF_8', type, '#skF_8': $i).
% 2.64/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.64/1.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.64/1.41  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.64/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.64/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.64/1.41  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.64/1.41  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.64/1.41  
% 2.91/1.42  tff(f_87, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 2.91/1.42  tff(f_43, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.91/1.42  tff(f_35, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.91/1.42  tff(f_56, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.91/1.42  tff(f_49, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.91/1.42  tff(f_72, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.91/1.42  tff(f_66, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.91/1.42  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.91/1.42  tff(c_62, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.91/1.42  tff(c_58, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.91/1.42  tff(c_22, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.91/1.42  tff(c_64, plain, (k2_xboole_0('#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.91/1.42  tff(c_321, plain, (![D_65, B_66, A_67]: (~r2_hidden(D_65, B_66) | r2_hidden(D_65, k2_xboole_0(A_67, B_66)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.91/1.42  tff(c_343, plain, (![D_70]: (~r2_hidden(D_70, '#skF_8') | r2_hidden(D_70, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_64, c_321])).
% 2.91/1.42  tff(c_28, plain, (![C_17, A_13]: (C_17=A_13 | ~r2_hidden(C_17, k1_tarski(A_13)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.91/1.42  tff(c_348, plain, (![D_71]: (D_71='#skF_6' | ~r2_hidden(D_71, '#skF_8'))), inference(resolution, [status(thm)], [c_343, c_28])).
% 2.91/1.42  tff(c_352, plain, ('#skF_3'('#skF_8')='#skF_6' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_22, c_348])).
% 2.91/1.42  tff(c_355, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_58, c_352])).
% 2.91/1.42  tff(c_359, plain, (r2_hidden('#skF_6', '#skF_8') | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_355, c_22])).
% 2.91/1.42  tff(c_362, plain, (r2_hidden('#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_58, c_359])).
% 2.91/1.42  tff(c_60, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.91/1.42  tff(c_26, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.91/1.42  tff(c_85, plain, (r1_tarski('#skF_7', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_64, c_26])).
% 2.91/1.42  tff(c_491, plain, (![B_78, A_79]: (k1_tarski(B_78)=A_79 | k1_xboole_0=A_79 | ~r1_tarski(A_79, k1_tarski(B_78)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.91/1.42  tff(c_498, plain, (k1_tarski('#skF_6')='#skF_7' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_85, c_491])).
% 2.91/1.42  tff(c_508, plain, (k1_tarski('#skF_6')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_60, c_498])).
% 2.91/1.42  tff(c_48, plain, (![A_24, B_25]: (r1_tarski(k1_tarski(A_24), B_25) | ~r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.91/1.42  tff(c_804, plain, (![B_89]: (r1_tarski('#skF_7', B_89) | ~r2_hidden('#skF_6', B_89))), inference(superposition, [status(thm), theory('equality')], [c_508, c_48])).
% 2.91/1.42  tff(c_852, plain, (r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_362, c_804])).
% 2.91/1.42  tff(c_24, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.91/1.42  tff(c_865, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_852, c_24])).
% 2.91/1.42  tff(c_517, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_508, c_64])).
% 2.91/1.42  tff(c_866, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_865, c_517])).
% 2.91/1.42  tff(c_868, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_866])).
% 2.91/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.42  
% 2.91/1.42  Inference rules
% 2.91/1.42  ----------------------
% 2.91/1.42  #Ref     : 0
% 2.91/1.42  #Sup     : 196
% 2.91/1.42  #Fact    : 0
% 2.91/1.42  #Define  : 0
% 2.91/1.42  #Split   : 1
% 2.91/1.42  #Chain   : 0
% 2.91/1.42  #Close   : 0
% 2.91/1.42  
% 2.91/1.42  Ordering : KBO
% 2.91/1.42  
% 2.91/1.42  Simplification rules
% 2.91/1.42  ----------------------
% 2.91/1.42  #Subsume      : 6
% 2.91/1.42  #Demod        : 87
% 2.91/1.42  #Tautology    : 133
% 2.91/1.42  #SimpNegUnit  : 7
% 2.91/1.42  #BackRed      : 6
% 2.91/1.42  
% 2.91/1.42  #Partial instantiations: 0
% 2.91/1.42  #Strategies tried      : 1
% 2.91/1.42  
% 2.91/1.42  Timing (in seconds)
% 2.91/1.42  ----------------------
% 2.91/1.43  Preprocessing        : 0.33
% 2.91/1.43  Parsing              : 0.16
% 2.91/1.43  CNF conversion       : 0.02
% 2.91/1.43  Main loop            : 0.33
% 2.91/1.43  Inferencing          : 0.12
% 2.91/1.43  Reduction            : 0.11
% 2.91/1.43  Demodulation         : 0.08
% 2.91/1.43  BG Simplification    : 0.02
% 2.91/1.43  Subsumption          : 0.06
% 2.91/1.43  Abstraction          : 0.02
% 2.91/1.43  MUC search           : 0.00
% 2.91/1.43  Cooper               : 0.00
% 2.91/1.43  Total                : 0.69
% 2.91/1.43  Index Insertion      : 0.00
% 2.91/1.43  Index Deletion       : 0.00
% 2.91/1.43  Index Matching       : 0.00
% 2.91/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
