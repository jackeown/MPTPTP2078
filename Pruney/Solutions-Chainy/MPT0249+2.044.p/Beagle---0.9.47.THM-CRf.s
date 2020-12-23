%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:29 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 102 expanded)
%              Number of leaves         :   31 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :   70 ( 167 expanded)
%              Number of equality atoms :   33 ( 107 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_58,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_66,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_22,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_68,plain,(
    k2_xboole_0('#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_350,plain,(
    ! [D_77,B_78,A_79] :
      ( ~ r2_hidden(D_77,B_78)
      | r2_hidden(D_77,k2_xboole_0(A_79,B_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_371,plain,(
    ! [D_80] :
      ( ~ r2_hidden(D_80,'#skF_8')
      | r2_hidden(D_80,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_350])).

tff(c_28,plain,(
    ! [C_17,A_13] :
      ( C_17 = A_13
      | ~ r2_hidden(C_17,k1_tarski(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_376,plain,(
    ! [D_81] :
      ( D_81 = '#skF_6'
      | ~ r2_hidden(D_81,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_371,c_28])).

tff(c_380,plain,
    ( '#skF_3'('#skF_8') = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_22,c_376])).

tff(c_383,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_380])).

tff(c_387,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_22])).

tff(c_390,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_387])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_26,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_89,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_26])).

tff(c_418,plain,(
    ! [B_90,A_91] :
      ( k1_tarski(B_90) = A_91
      | k1_xboole_0 = A_91
      | ~ r1_tarski(A_91,k1_tarski(B_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_421,plain,
    ( k1_tarski('#skF_6') = '#skF_7'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_89,c_418])).

tff(c_430,plain,(
    k1_tarski('#skF_6') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_421])).

tff(c_40,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_849,plain,(
    ! [A_113,B_114,C_115] :
      ( r1_tarski(k2_tarski(A_113,B_114),C_115)
      | ~ r2_hidden(B_114,C_115)
      | ~ r2_hidden(A_113,C_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1005,plain,(
    ! [A_118,C_119] :
      ( r1_tarski(k1_tarski(A_118),C_119)
      | ~ r2_hidden(A_118,C_119)
      | ~ r2_hidden(A_118,C_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_849])).

tff(c_1027,plain,(
    ! [C_120] :
      ( r1_tarski('#skF_7',C_120)
      | ~ r2_hidden('#skF_6',C_120)
      | ~ r2_hidden('#skF_6',C_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_430,c_1005])).

tff(c_1051,plain,
    ( r1_tarski('#skF_7','#skF_8')
    | ~ r2_hidden('#skF_6','#skF_8') ),
    inference(resolution,[status(thm)],[c_390,c_1027])).

tff(c_1090,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_1051])).

tff(c_24,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1111,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1090,c_24])).

tff(c_439,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_68])).

tff(c_1112,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1111,c_439])).

tff(c_1114,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1112])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:27:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.70/2.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/2.06  
% 3.70/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/2.07  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 3.70/2.07  
% 3.70/2.07  %Foreground sorts:
% 3.70/2.07  
% 3.70/2.07  
% 3.70/2.07  %Background operators:
% 3.70/2.07  
% 3.70/2.07  
% 3.70/2.07  %Foreground operators:
% 3.70/2.07  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.70/2.07  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 3.70/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.70/2.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.70/2.07  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.70/2.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.70/2.07  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.70/2.07  tff('#skF_7', type, '#skF_7': $i).
% 3.70/2.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.70/2.07  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.70/2.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.70/2.07  tff('#skF_6', type, '#skF_6': $i).
% 3.70/2.07  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.70/2.07  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.70/2.07  tff('#skF_8', type, '#skF_8': $i).
% 3.70/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.70/2.07  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.70/2.07  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.70/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.70/2.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.70/2.07  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.70/2.07  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.70/2.07  
% 3.96/2.09  tff(f_91, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 3.96/2.09  tff(f_43, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.96/2.09  tff(f_35, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.96/2.09  tff(f_56, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.96/2.09  tff(f_49, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.96/2.09  tff(f_70, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.96/2.09  tff(f_58, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.96/2.09  tff(f_78, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.96/2.09  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.96/2.09  tff(c_66, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.96/2.09  tff(c_62, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.96/2.09  tff(c_22, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.96/2.09  tff(c_68, plain, (k2_xboole_0('#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.96/2.09  tff(c_350, plain, (![D_77, B_78, A_79]: (~r2_hidden(D_77, B_78) | r2_hidden(D_77, k2_xboole_0(A_79, B_78)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.96/2.09  tff(c_371, plain, (![D_80]: (~r2_hidden(D_80, '#skF_8') | r2_hidden(D_80, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_68, c_350])).
% 3.96/2.09  tff(c_28, plain, (![C_17, A_13]: (C_17=A_13 | ~r2_hidden(C_17, k1_tarski(A_13)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.96/2.09  tff(c_376, plain, (![D_81]: (D_81='#skF_6' | ~r2_hidden(D_81, '#skF_8'))), inference(resolution, [status(thm)], [c_371, c_28])).
% 3.96/2.09  tff(c_380, plain, ('#skF_3'('#skF_8')='#skF_6' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_22, c_376])).
% 3.96/2.09  tff(c_383, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_62, c_380])).
% 3.96/2.09  tff(c_387, plain, (r2_hidden('#skF_6', '#skF_8') | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_383, c_22])).
% 3.96/2.09  tff(c_390, plain, (r2_hidden('#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_62, c_387])).
% 3.96/2.09  tff(c_64, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.96/2.09  tff(c_26, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.96/2.09  tff(c_89, plain, (r1_tarski('#skF_7', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_26])).
% 3.96/2.09  tff(c_418, plain, (![B_90, A_91]: (k1_tarski(B_90)=A_91 | k1_xboole_0=A_91 | ~r1_tarski(A_91, k1_tarski(B_90)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.96/2.09  tff(c_421, plain, (k1_tarski('#skF_6')='#skF_7' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_89, c_418])).
% 3.96/2.09  tff(c_430, plain, (k1_tarski('#skF_6')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_64, c_421])).
% 3.96/2.09  tff(c_40, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.96/2.09  tff(c_849, plain, (![A_113, B_114, C_115]: (r1_tarski(k2_tarski(A_113, B_114), C_115) | ~r2_hidden(B_114, C_115) | ~r2_hidden(A_113, C_115))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.96/2.09  tff(c_1005, plain, (![A_118, C_119]: (r1_tarski(k1_tarski(A_118), C_119) | ~r2_hidden(A_118, C_119) | ~r2_hidden(A_118, C_119))), inference(superposition, [status(thm), theory('equality')], [c_40, c_849])).
% 3.96/2.09  tff(c_1027, plain, (![C_120]: (r1_tarski('#skF_7', C_120) | ~r2_hidden('#skF_6', C_120) | ~r2_hidden('#skF_6', C_120))), inference(superposition, [status(thm), theory('equality')], [c_430, c_1005])).
% 3.96/2.09  tff(c_1051, plain, (r1_tarski('#skF_7', '#skF_8') | ~r2_hidden('#skF_6', '#skF_8')), inference(resolution, [status(thm)], [c_390, c_1027])).
% 3.96/2.09  tff(c_1090, plain, (r1_tarski('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_390, c_1051])).
% 3.96/2.09  tff(c_24, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.96/2.09  tff(c_1111, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_1090, c_24])).
% 3.96/2.09  tff(c_439, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_430, c_68])).
% 3.96/2.09  tff(c_1112, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1111, c_439])).
% 3.96/2.09  tff(c_1114, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_1112])).
% 3.96/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/2.09  
% 3.96/2.09  Inference rules
% 3.96/2.09  ----------------------
% 3.96/2.09  #Ref     : 0
% 3.96/2.09  #Sup     : 250
% 3.96/2.09  #Fact    : 0
% 3.96/2.09  #Define  : 0
% 3.96/2.09  #Split   : 1
% 3.96/2.09  #Chain   : 0
% 3.96/2.09  #Close   : 0
% 3.96/2.09  
% 3.96/2.09  Ordering : KBO
% 3.96/2.09  
% 3.96/2.09  Simplification rules
% 3.96/2.09  ----------------------
% 3.96/2.09  #Subsume      : 19
% 3.96/2.09  #Demod        : 151
% 3.96/2.09  #Tautology    : 168
% 3.96/2.09  #SimpNegUnit  : 9
% 3.96/2.09  #BackRed      : 5
% 3.96/2.09  
% 3.96/2.09  #Partial instantiations: 0
% 3.96/2.09  #Strategies tried      : 1
% 3.96/2.09  
% 3.96/2.09  Timing (in seconds)
% 3.96/2.09  ----------------------
% 4.01/2.09  Preprocessing        : 0.52
% 4.01/2.09  Parsing              : 0.25
% 4.01/2.09  CNF conversion       : 0.04
% 4.01/2.09  Main loop            : 0.64
% 4.01/2.09  Inferencing          : 0.23
% 4.01/2.09  Reduction            : 0.23
% 4.01/2.09  Demodulation         : 0.17
% 4.01/2.09  BG Simplification    : 0.03
% 4.01/2.09  Subsumption          : 0.11
% 4.01/2.09  Abstraction          : 0.03
% 4.01/2.09  MUC search           : 0.00
% 4.01/2.09  Cooper               : 0.00
% 4.01/2.09  Total                : 1.21
% 4.01/2.09  Index Insertion      : 0.00
% 4.01/2.09  Index Deletion       : 0.00
% 4.01/2.10  Index Matching       : 0.00
% 4.01/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
