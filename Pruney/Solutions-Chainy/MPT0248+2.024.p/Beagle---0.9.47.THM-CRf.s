%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:07 EST 2020

% Result     : Theorem 3.51s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 100 expanded)
%              Number of leaves         :   20 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :   75 ( 219 expanded)
%              Number of equality atoms :   54 ( 192 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_30,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_28,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_39,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_34,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_54,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_12])).

tff(c_716,plain,(
    ! [B_53,A_54] :
      ( k1_tarski(B_53) = A_54
      | k1_xboole_0 = A_54
      | ~ r1_tarski(A_54,k1_tarski(B_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_722,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_54,c_716])).

tff(c_734,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_39,c_722])).

tff(c_735,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_840,plain,(
    ! [A_63,B_64] :
      ( k2_xboole_0(A_63,B_64) = B_64
      | ~ r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_860,plain,(
    ! [B_4] : k2_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_840])).

tff(c_761,plain,(
    ! [B_59,A_60] : k2_xboole_0(B_59,A_60) = k2_xboole_0(A_60,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_812,plain,(
    ! [A_61,B_62] : r1_tarski(A_61,k2_xboole_0(B_62,A_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_761,c_12])).

tff(c_821,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_812])).

tff(c_736,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_20,plain,(
    ! [B_16,A_15] :
      ( k1_tarski(B_16) = A_15
      | k1_xboole_0 = A_15
      | ~ r1_tarski(A_15,k1_tarski(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_961,plain,(
    ! [B_75,A_76] :
      ( k1_tarski(B_75) = A_76
      | A_76 = '#skF_2'
      | ~ r1_tarski(A_76,k1_tarski(B_75)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_736,c_20])).

tff(c_964,plain,
    ( k1_tarski('#skF_1') = '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_821,c_961])).

tff(c_974,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_735,c_964])).

tff(c_803,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_761])).

tff(c_982,plain,(
    k2_xboole_0('#skF_3','#skF_3') = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_974,c_803])).

tff(c_987,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_860,c_982])).

tff(c_989,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_735,c_987])).

tff(c_990,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_991,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_32,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1079,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_991,c_991,c_32])).

tff(c_1019,plain,(
    ! [B_80,A_81] : k2_xboole_0(B_80,A_81) = k2_xboole_0(A_81,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1000,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_991,c_34])).

tff(c_1040,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1019,c_1000])).

tff(c_1073,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1040,c_12])).

tff(c_1470,plain,(
    ! [B_105,A_106] :
      ( k1_tarski(B_105) = A_106
      | k1_xboole_0 = A_106
      | ~ r1_tarski(A_106,k1_tarski(B_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1473,plain,(
    ! [A_106] :
      ( k1_tarski('#skF_1') = A_106
      | k1_xboole_0 = A_106
      | ~ r1_tarski(A_106,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_991,c_1470])).

tff(c_1486,plain,(
    ! [A_107] :
      ( A_107 = '#skF_2'
      | k1_xboole_0 = A_107
      | ~ r1_tarski(A_107,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_991,c_1473])).

tff(c_1489,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1073,c_1486])).

tff(c_1500,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_990,c_1079,c_1489])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:22:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.51/2.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/2.23  
% 3.82/2.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/2.23  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.82/2.23  
% 3.82/2.23  %Foreground sorts:
% 3.82/2.23  
% 3.82/2.23  
% 3.82/2.23  %Background operators:
% 3.82/2.23  
% 3.82/2.23  
% 3.82/2.23  %Foreground operators:
% 3.82/2.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.82/2.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.82/2.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.82/2.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.82/2.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.82/2.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.82/2.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.82/2.23  tff('#skF_2', type, '#skF_2': $i).
% 3.82/2.23  tff('#skF_3', type, '#skF_3': $i).
% 3.82/2.23  tff('#skF_1', type, '#skF_1': $i).
% 3.82/2.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.82/2.23  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.82/2.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.82/2.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.82/2.23  
% 3.82/2.25  tff(f_72, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.82/2.25  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.82/2.25  tff(f_51, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.82/2.25  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.82/2.25  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.82/2.25  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.82/2.25  tff(c_30, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.82/2.25  tff(c_40, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_30])).
% 3.82/2.25  tff(c_28, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.82/2.25  tff(c_39, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_28])).
% 3.82/2.25  tff(c_34, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.82/2.25  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.82/2.25  tff(c_54, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_12])).
% 3.82/2.25  tff(c_716, plain, (![B_53, A_54]: (k1_tarski(B_53)=A_54 | k1_xboole_0=A_54 | ~r1_tarski(A_54, k1_tarski(B_53)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.82/2.25  tff(c_722, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_54, c_716])).
% 3.82/2.25  tff(c_734, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_39, c_722])).
% 3.82/2.25  tff(c_735, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_30])).
% 3.82/2.25  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.82/2.25  tff(c_840, plain, (![A_63, B_64]: (k2_xboole_0(A_63, B_64)=B_64 | ~r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.82/2.25  tff(c_860, plain, (![B_4]: (k2_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_840])).
% 3.82/2.25  tff(c_761, plain, (![B_59, A_60]: (k2_xboole_0(B_59, A_60)=k2_xboole_0(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.82/2.25  tff(c_812, plain, (![A_61, B_62]: (r1_tarski(A_61, k2_xboole_0(B_62, A_61)))), inference(superposition, [status(thm), theory('equality')], [c_761, c_12])).
% 3.82/2.25  tff(c_821, plain, (r1_tarski('#skF_3', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_812])).
% 3.82/2.25  tff(c_736, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_30])).
% 3.82/2.25  tff(c_20, plain, (![B_16, A_15]: (k1_tarski(B_16)=A_15 | k1_xboole_0=A_15 | ~r1_tarski(A_15, k1_tarski(B_16)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.82/2.25  tff(c_961, plain, (![B_75, A_76]: (k1_tarski(B_75)=A_76 | A_76='#skF_2' | ~r1_tarski(A_76, k1_tarski(B_75)))), inference(demodulation, [status(thm), theory('equality')], [c_736, c_20])).
% 3.82/2.25  tff(c_964, plain, (k1_tarski('#skF_1')='#skF_3' | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_821, c_961])).
% 3.82/2.25  tff(c_974, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_735, c_964])).
% 3.82/2.25  tff(c_803, plain, (k2_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_34, c_761])).
% 3.82/2.25  tff(c_982, plain, (k2_xboole_0('#skF_3', '#skF_3')=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_974, c_803])).
% 3.82/2.25  tff(c_987, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_860, c_982])).
% 3.82/2.25  tff(c_989, plain, $false, inference(negUnitSimplification, [status(thm)], [c_735, c_987])).
% 3.82/2.25  tff(c_990, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_28])).
% 3.82/2.25  tff(c_991, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_28])).
% 3.82/2.25  tff(c_32, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.82/2.25  tff(c_1079, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_991, c_991, c_32])).
% 3.82/2.25  tff(c_1019, plain, (![B_80, A_81]: (k2_xboole_0(B_80, A_81)=k2_xboole_0(A_81, B_80))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.82/2.25  tff(c_1000, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_991, c_34])).
% 3.82/2.25  tff(c_1040, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1019, c_1000])).
% 3.82/2.25  tff(c_1073, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1040, c_12])).
% 3.82/2.25  tff(c_1470, plain, (![B_105, A_106]: (k1_tarski(B_105)=A_106 | k1_xboole_0=A_106 | ~r1_tarski(A_106, k1_tarski(B_105)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.82/2.25  tff(c_1473, plain, (![A_106]: (k1_tarski('#skF_1')=A_106 | k1_xboole_0=A_106 | ~r1_tarski(A_106, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_991, c_1470])).
% 3.82/2.25  tff(c_1486, plain, (![A_107]: (A_107='#skF_2' | k1_xboole_0=A_107 | ~r1_tarski(A_107, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_991, c_1473])).
% 3.82/2.25  tff(c_1489, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1073, c_1486])).
% 3.82/2.25  tff(c_1500, plain, $false, inference(negUnitSimplification, [status(thm)], [c_990, c_1079, c_1489])).
% 3.82/2.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/2.25  
% 3.82/2.25  Inference rules
% 3.82/2.25  ----------------------
% 3.82/2.25  #Ref     : 0
% 3.82/2.25  #Sup     : 361
% 3.82/2.25  #Fact    : 0
% 3.82/2.25  #Define  : 0
% 3.82/2.25  #Split   : 4
% 3.82/2.25  #Chain   : 0
% 3.82/2.25  #Close   : 0
% 3.82/2.25  
% 3.82/2.25  Ordering : KBO
% 3.82/2.25  
% 3.82/2.25  Simplification rules
% 3.82/2.25  ----------------------
% 3.82/2.25  #Subsume      : 12
% 3.82/2.25  #Demod        : 295
% 3.82/2.25  #Tautology    : 280
% 3.82/2.25  #SimpNegUnit  : 9
% 3.82/2.25  #BackRed      : 13
% 3.82/2.25  
% 3.82/2.25  #Partial instantiations: 0
% 3.82/2.25  #Strategies tried      : 1
% 3.82/2.25  
% 3.82/2.25  Timing (in seconds)
% 3.82/2.25  ----------------------
% 3.82/2.26  Preprocessing        : 0.51
% 3.82/2.26  Parsing              : 0.29
% 3.82/2.26  CNF conversion       : 0.03
% 3.82/2.26  Main loop            : 0.80
% 3.82/2.26  Inferencing          : 0.28
% 3.82/2.26  Reduction            : 0.33
% 3.82/2.26  Demodulation         : 0.28
% 3.82/2.26  BG Simplification    : 0.03
% 3.82/2.26  Subsumption          : 0.11
% 3.82/2.26  Abstraction          : 0.04
% 3.82/2.26  MUC search           : 0.00
% 3.82/2.26  Cooper               : 0.00
% 3.82/2.26  Total                : 1.36
% 3.82/2.26  Index Insertion      : 0.00
% 3.82/2.26  Index Deletion       : 0.00
% 3.82/2.26  Index Matching       : 0.00
% 3.82/2.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
