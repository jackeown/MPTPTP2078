%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:30 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   58 (  80 expanded)
%              Number of leaves         :   32 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :   60 ( 113 expanded)
%              Number of equality atoms :   31 (  77 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_42,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_48,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_68,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_20,plain,(
    ! [A_7] :
      ( r2_hidden('#skF_3'(A_7),A_7)
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_70,plain,(
    k2_xboole_0('#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_329,plain,(
    ! [D_89,B_90,A_91] :
      ( ~ r2_hidden(D_89,B_90)
      | r2_hidden(D_89,k2_xboole_0(A_91,B_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_345,plain,(
    ! [D_92] :
      ( ~ r2_hidden(D_92,'#skF_8')
      | r2_hidden(D_92,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_329])).

tff(c_26,plain,(
    ! [C_17,A_13] :
      ( C_17 = A_13
      | ~ r2_hidden(C_17,k1_tarski(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_350,plain,(
    ! [D_93] :
      ( D_93 = '#skF_6'
      | ~ r2_hidden(D_93,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_345,c_26])).

tff(c_354,plain,
    ( '#skF_3'('#skF_8') = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_20,c_350])).

tff(c_357,plain,(
    '#skF_3'('#skF_8') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_354])).

tff(c_361,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_20])).

tff(c_364,plain,(
    r2_hidden('#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_361])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_78,plain,(
    ! [A_55,B_56] : r1_tarski(A_55,k2_xboole_0(A_55,B_56)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_81,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_78])).

tff(c_493,plain,(
    ! [B_100,A_101] :
      ( k1_tarski(B_100) = A_101
      | k1_xboole_0 = A_101
      | ~ r1_tarski(A_101,k1_tarski(B_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_500,plain,
    ( k1_tarski('#skF_6') = '#skF_7'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_81,c_493])).

tff(c_510,plain,(
    k1_tarski('#skF_6') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_500])).

tff(c_54,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(k1_tarski(A_46),B_47)
      | ~ r2_hidden(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_751,plain,(
    ! [B_110] :
      ( r1_tarski('#skF_7',B_110)
      | ~ r2_hidden('#skF_6',B_110) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_510,c_54])).

tff(c_799,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_364,c_751])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = B_10
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_812,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_799,c_22])).

tff(c_519,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_70])).

tff(c_813,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_812,c_519])).

tff(c_815,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_813])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:34:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.43  
% 2.68/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.43  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_5 > #skF_4
% 2.68/1.43  
% 2.68/1.43  %Foreground sorts:
% 2.68/1.43  
% 2.68/1.43  
% 2.68/1.43  %Background operators:
% 2.68/1.43  
% 2.68/1.43  
% 2.68/1.43  %Foreground operators:
% 2.68/1.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.68/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.68/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.68/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.68/1.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.68/1.43  tff('#skF_7', type, '#skF_7': $i).
% 2.68/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.68/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.68/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.68/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.68/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.68/1.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.68/1.43  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.68/1.43  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.68/1.43  tff('#skF_8', type, '#skF_8': $i).
% 2.68/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.43  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.68/1.43  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.68/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.68/1.43  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.68/1.43  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.68/1.43  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.68/1.43  
% 2.68/1.44  tff(f_94, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 2.68/1.44  tff(f_42, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.68/1.44  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.68/1.44  tff(f_55, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.68/1.44  tff(f_48, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.68/1.44  tff(f_79, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.68/1.44  tff(f_73, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.68/1.44  tff(f_46, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.68/1.44  tff(c_68, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.68/1.44  tff(c_64, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.68/1.44  tff(c_20, plain, (![A_7]: (r2_hidden('#skF_3'(A_7), A_7) | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.68/1.44  tff(c_70, plain, (k2_xboole_0('#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.68/1.44  tff(c_329, plain, (![D_89, B_90, A_91]: (~r2_hidden(D_89, B_90) | r2_hidden(D_89, k2_xboole_0(A_91, B_90)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.68/1.44  tff(c_345, plain, (![D_92]: (~r2_hidden(D_92, '#skF_8') | r2_hidden(D_92, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_70, c_329])).
% 2.68/1.44  tff(c_26, plain, (![C_17, A_13]: (C_17=A_13 | ~r2_hidden(C_17, k1_tarski(A_13)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.68/1.44  tff(c_350, plain, (![D_93]: (D_93='#skF_6' | ~r2_hidden(D_93, '#skF_8'))), inference(resolution, [status(thm)], [c_345, c_26])).
% 2.68/1.44  tff(c_354, plain, ('#skF_3'('#skF_8')='#skF_6' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_20, c_350])).
% 2.68/1.44  tff(c_357, plain, ('#skF_3'('#skF_8')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_64, c_354])).
% 2.68/1.44  tff(c_361, plain, (r2_hidden('#skF_6', '#skF_8') | k1_xboole_0='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_357, c_20])).
% 2.68/1.44  tff(c_364, plain, (r2_hidden('#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_64, c_361])).
% 2.68/1.44  tff(c_66, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.68/1.44  tff(c_78, plain, (![A_55, B_56]: (r1_tarski(A_55, k2_xboole_0(A_55, B_56)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.68/1.44  tff(c_81, plain, (r1_tarski('#skF_7', k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_78])).
% 2.68/1.44  tff(c_493, plain, (![B_100, A_101]: (k1_tarski(B_100)=A_101 | k1_xboole_0=A_101 | ~r1_tarski(A_101, k1_tarski(B_100)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.68/1.44  tff(c_500, plain, (k1_tarski('#skF_6')='#skF_7' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_81, c_493])).
% 2.68/1.44  tff(c_510, plain, (k1_tarski('#skF_6')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_66, c_500])).
% 2.68/1.44  tff(c_54, plain, (![A_46, B_47]: (r1_tarski(k1_tarski(A_46), B_47) | ~r2_hidden(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.68/1.44  tff(c_751, plain, (![B_110]: (r1_tarski('#skF_7', B_110) | ~r2_hidden('#skF_6', B_110))), inference(superposition, [status(thm), theory('equality')], [c_510, c_54])).
% 2.68/1.44  tff(c_799, plain, (r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_364, c_751])).
% 2.68/1.44  tff(c_22, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=B_10 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.68/1.44  tff(c_812, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_799, c_22])).
% 2.68/1.44  tff(c_519, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_510, c_70])).
% 2.68/1.44  tff(c_813, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_812, c_519])).
% 2.68/1.44  tff(c_815, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_813])).
% 2.68/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.44  
% 2.68/1.44  Inference rules
% 2.68/1.44  ----------------------
% 2.68/1.44  #Ref     : 0
% 2.68/1.44  #Sup     : 179
% 2.68/1.44  #Fact    : 0
% 2.68/1.44  #Define  : 0
% 2.68/1.44  #Split   : 1
% 2.68/1.44  #Chain   : 0
% 2.68/1.44  #Close   : 0
% 2.68/1.44  
% 2.68/1.44  Ordering : KBO
% 2.68/1.44  
% 2.68/1.44  Simplification rules
% 2.68/1.44  ----------------------
% 2.68/1.44  #Subsume      : 8
% 2.68/1.44  #Demod        : 85
% 2.68/1.44  #Tautology    : 120
% 2.68/1.44  #SimpNegUnit  : 7
% 2.68/1.44  #BackRed      : 6
% 2.68/1.44  
% 2.68/1.44  #Partial instantiations: 0
% 2.68/1.44  #Strategies tried      : 1
% 2.68/1.44  
% 2.68/1.44  Timing (in seconds)
% 2.68/1.44  ----------------------
% 2.68/1.45  Preprocessing        : 0.34
% 2.68/1.45  Parsing              : 0.17
% 2.68/1.45  CNF conversion       : 0.03
% 2.68/1.45  Main loop            : 0.32
% 2.68/1.45  Inferencing          : 0.12
% 2.68/1.45  Reduction            : 0.11
% 2.68/1.45  Demodulation         : 0.08
% 2.68/1.45  BG Simplification    : 0.02
% 2.68/1.45  Subsumption          : 0.06
% 2.68/1.45  Abstraction          : 0.02
% 2.68/1.45  MUC search           : 0.00
% 2.68/1.45  Cooper               : 0.00
% 2.68/1.45  Total                : 0.70
% 2.68/1.45  Index Insertion      : 0.00
% 2.68/1.45  Index Deletion       : 0.00
% 2.68/1.45  Index Matching       : 0.00
% 2.68/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
