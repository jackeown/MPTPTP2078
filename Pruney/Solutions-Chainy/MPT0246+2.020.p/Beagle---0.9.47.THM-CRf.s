%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:02 EST 2020

% Result     : Theorem 6.95s
% Output     : CNFRefutation 6.95s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 123 expanded)
%              Number of leaves         :   22 (  53 expanded)
%              Depth                    :   14
%              Number of atoms          :   81 ( 252 expanded)
%              Number of equality atoms :   62 ( 192 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_tarski(B)
          & A != k1_xboole_0
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & C != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_40,plain,(
    k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_61,plain,(
    ! [A_46] :
      ( r2_hidden('#skF_1'(A_46),A_46)
      | k1_xboole_0 = A_46 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_36,plain,(
    ! [C_38] :
      ( C_38 = '#skF_5'
      | ~ r2_hidden(C_38,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_65,plain,
    ( '#skF_1'('#skF_4') = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_61,c_36])).

tff(c_68,plain,(
    '#skF_1'('#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_65])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_72,plain,
    ( r2_hidden('#skF_5','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_2])).

tff(c_75,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_72])).

tff(c_22,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12,plain,(
    ! [A_3,B_4,C_5] :
      ( '#skF_2'(A_3,B_4,C_5) = B_4
      | '#skF_2'(A_3,B_4,C_5) = A_3
      | '#skF_3'(A_3,B_4,C_5) != B_4
      | k2_tarski(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_253,plain,(
    ! [B_4,C_5] :
      ( '#skF_3'(B_4,B_4,C_5) != B_4
      | k2_tarski(B_4,B_4) = C_5
      | '#skF_2'(B_4,B_4,C_5) = B_4 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_12])).

tff(c_1242,plain,(
    ! [B_2387,C_2388] :
      ( '#skF_3'(B_2387,B_2387,C_2388) != B_2387
      | k1_tarski(B_2387) = C_2388
      | '#skF_2'(B_2387,B_2387,C_2388) = B_2387 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_253])).

tff(c_1508,plain,(
    ! [C_3636] :
      ( C_3636 != '#skF_4'
      | '#skF_3'('#skF_5','#skF_5',C_3636) != '#skF_5'
      | '#skF_2'('#skF_5','#skF_5',C_3636) = '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1242,c_40])).

tff(c_14,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | '#skF_3'(A_3,B_4,C_5) != A_3
      | k2_tarski(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1532,plain,(
    ! [C_3636] :
      ( ~ r2_hidden('#skF_5',C_3636)
      | '#skF_3'('#skF_5','#skF_5',C_3636) != '#skF_5'
      | k2_tarski('#skF_5','#skF_5') = C_3636
      | C_3636 != '#skF_4'
      | '#skF_3'('#skF_5','#skF_5',C_3636) != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1508,c_14])).

tff(c_1566,plain,(
    ! [C_3766] :
      ( ~ r2_hidden('#skF_5',C_3766)
      | '#skF_3'('#skF_5','#skF_5',C_3766) != '#skF_5'
      | k1_tarski('#skF_5') = C_3766
      | C_3766 != '#skF_4'
      | '#skF_3'('#skF_5','#skF_5',C_3766) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1532])).

tff(c_1583,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | '#skF_3'('#skF_5','#skF_5','#skF_4') != '#skF_5' ),
    inference(resolution,[status(thm)],[c_75,c_1566])).

tff(c_1598,plain,(
    '#skF_3'('#skF_5','#skF_5','#skF_4') != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1583])).

tff(c_1725,plain,(
    ! [A_4285,B_4286,C_4287] :
      ( '#skF_2'(A_4285,B_4286,C_4287) = B_4286
      | '#skF_2'(A_4285,B_4286,C_4287) = A_4285
      | r2_hidden('#skF_3'(A_4285,B_4286,C_4287),C_4287)
      | k2_tarski(A_4285,B_4286) = C_4287 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1897,plain,(
    ! [A_4677,B_4678] :
      ( '#skF_3'(A_4677,B_4678,'#skF_4') = '#skF_5'
      | '#skF_2'(A_4677,B_4678,'#skF_4') = B_4678
      | '#skF_2'(A_4677,B_4678,'#skF_4') = A_4677
      | k2_tarski(A_4677,B_4678) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_1725,c_36])).

tff(c_9320,plain,(
    ! [A_15711] :
      ( '#skF_3'(A_15711,A_15711,'#skF_4') = '#skF_5'
      | '#skF_2'(A_15711,A_15711,'#skF_4') = A_15711
      | '#skF_2'(A_15711,A_15711,'#skF_4') = A_15711
      | k1_tarski(A_15711) = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1897])).

tff(c_9418,plain,
    ( '#skF_3'('#skF_5','#skF_5','#skF_4') = '#skF_5'
    | '#skF_2'('#skF_5','#skF_5','#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_9320,c_40])).

tff(c_9624,plain,(
    '#skF_2'('#skF_5','#skF_5','#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1598,c_9418])).

tff(c_18,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | r2_hidden('#skF_3'(A_3,B_4,C_5),C_5)
      | k2_tarski(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_9695,plain,
    ( ~ r2_hidden('#skF_5','#skF_4')
    | r2_hidden('#skF_3'('#skF_5','#skF_5','#skF_4'),'#skF_4')
    | k2_tarski('#skF_5','#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_9624,c_18])).

tff(c_9761,plain,
    ( r2_hidden('#skF_3'('#skF_5','#skF_5','#skF_4'),'#skF_4')
    | k1_tarski('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_75,c_9695])).

tff(c_9762,plain,(
    r2_hidden('#skF_3'('#skF_5','#skF_5','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_9761])).

tff(c_9779,plain,(
    '#skF_3'('#skF_5','#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_9762,c_36])).

tff(c_9785,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1598,c_9779])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:29:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.95/2.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.95/2.46  
% 6.95/2.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.95/2.46  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 6.95/2.46  
% 6.95/2.46  %Foreground sorts:
% 6.95/2.46  
% 6.95/2.46  
% 6.95/2.46  %Background operators:
% 6.95/2.46  
% 6.95/2.46  
% 6.95/2.46  %Foreground operators:
% 6.95/2.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.95/2.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.95/2.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.95/2.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.95/2.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.95/2.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.95/2.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.95/2.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.95/2.46  tff('#skF_5', type, '#skF_5': $i).
% 6.95/2.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.95/2.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.95/2.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.95/2.46  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.95/2.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.95/2.46  tff('#skF_4', type, '#skF_4': $i).
% 6.95/2.46  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.95/2.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.95/2.46  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.95/2.46  
% 6.95/2.47  tff(f_71, negated_conjecture, ~(![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 6.95/2.47  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 6.95/2.47  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.95/2.47  tff(f_42, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 6.95/2.47  tff(c_40, plain, (k1_tarski('#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.95/2.47  tff(c_38, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.95/2.47  tff(c_61, plain, (![A_46]: (r2_hidden('#skF_1'(A_46), A_46) | k1_xboole_0=A_46)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.95/2.47  tff(c_36, plain, (![C_38]: (C_38='#skF_5' | ~r2_hidden(C_38, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.95/2.47  tff(c_65, plain, ('#skF_1'('#skF_4')='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_61, c_36])).
% 6.95/2.47  tff(c_68, plain, ('#skF_1'('#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_38, c_65])).
% 6.95/2.47  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.95/2.47  tff(c_72, plain, (r2_hidden('#skF_5', '#skF_4') | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_68, c_2])).
% 6.95/2.47  tff(c_75, plain, (r2_hidden('#skF_5', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_38, c_72])).
% 6.95/2.47  tff(c_22, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.95/2.47  tff(c_12, plain, (![A_3, B_4, C_5]: ('#skF_2'(A_3, B_4, C_5)=B_4 | '#skF_2'(A_3, B_4, C_5)=A_3 | '#skF_3'(A_3, B_4, C_5)!=B_4 | k2_tarski(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.95/2.47  tff(c_253, plain, (![B_4, C_5]: ('#skF_3'(B_4, B_4, C_5)!=B_4 | k2_tarski(B_4, B_4)=C_5 | '#skF_2'(B_4, B_4, C_5)=B_4)), inference(factorization, [status(thm), theory('equality')], [c_12])).
% 6.95/2.47  tff(c_1242, plain, (![B_2387, C_2388]: ('#skF_3'(B_2387, B_2387, C_2388)!=B_2387 | k1_tarski(B_2387)=C_2388 | '#skF_2'(B_2387, B_2387, C_2388)=B_2387)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_253])).
% 6.95/2.47  tff(c_1508, plain, (![C_3636]: (C_3636!='#skF_4' | '#skF_3'('#skF_5', '#skF_5', C_3636)!='#skF_5' | '#skF_2'('#skF_5', '#skF_5', C_3636)='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1242, c_40])).
% 6.95/2.47  tff(c_14, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | '#skF_3'(A_3, B_4, C_5)!=A_3 | k2_tarski(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.95/2.47  tff(c_1532, plain, (![C_3636]: (~r2_hidden('#skF_5', C_3636) | '#skF_3'('#skF_5', '#skF_5', C_3636)!='#skF_5' | k2_tarski('#skF_5', '#skF_5')=C_3636 | C_3636!='#skF_4' | '#skF_3'('#skF_5', '#skF_5', C_3636)!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1508, c_14])).
% 6.95/2.47  tff(c_1566, plain, (![C_3766]: (~r2_hidden('#skF_5', C_3766) | '#skF_3'('#skF_5', '#skF_5', C_3766)!='#skF_5' | k1_tarski('#skF_5')=C_3766 | C_3766!='#skF_4' | '#skF_3'('#skF_5', '#skF_5', C_3766)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1532])).
% 6.95/2.47  tff(c_1583, plain, (k1_tarski('#skF_5')='#skF_4' | '#skF_3'('#skF_5', '#skF_5', '#skF_4')!='#skF_5'), inference(resolution, [status(thm)], [c_75, c_1566])).
% 6.95/2.47  tff(c_1598, plain, ('#skF_3'('#skF_5', '#skF_5', '#skF_4')!='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_40, c_1583])).
% 6.95/2.47  tff(c_1725, plain, (![A_4285, B_4286, C_4287]: ('#skF_2'(A_4285, B_4286, C_4287)=B_4286 | '#skF_2'(A_4285, B_4286, C_4287)=A_4285 | r2_hidden('#skF_3'(A_4285, B_4286, C_4287), C_4287) | k2_tarski(A_4285, B_4286)=C_4287)), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.95/2.47  tff(c_1897, plain, (![A_4677, B_4678]: ('#skF_3'(A_4677, B_4678, '#skF_4')='#skF_5' | '#skF_2'(A_4677, B_4678, '#skF_4')=B_4678 | '#skF_2'(A_4677, B_4678, '#skF_4')=A_4677 | k2_tarski(A_4677, B_4678)='#skF_4')), inference(resolution, [status(thm)], [c_1725, c_36])).
% 6.95/2.47  tff(c_9320, plain, (![A_15711]: ('#skF_3'(A_15711, A_15711, '#skF_4')='#skF_5' | '#skF_2'(A_15711, A_15711, '#skF_4')=A_15711 | '#skF_2'(A_15711, A_15711, '#skF_4')=A_15711 | k1_tarski(A_15711)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_22, c_1897])).
% 6.95/2.47  tff(c_9418, plain, ('#skF_3'('#skF_5', '#skF_5', '#skF_4')='#skF_5' | '#skF_2'('#skF_5', '#skF_5', '#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_9320, c_40])).
% 6.95/2.47  tff(c_9624, plain, ('#skF_2'('#skF_5', '#skF_5', '#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1598, c_9418])).
% 6.95/2.47  tff(c_18, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | r2_hidden('#skF_3'(A_3, B_4, C_5), C_5) | k2_tarski(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.95/2.47  tff(c_9695, plain, (~r2_hidden('#skF_5', '#skF_4') | r2_hidden('#skF_3'('#skF_5', '#skF_5', '#skF_4'), '#skF_4') | k2_tarski('#skF_5', '#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_9624, c_18])).
% 6.95/2.47  tff(c_9761, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_5', '#skF_4'), '#skF_4') | k1_tarski('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_75, c_9695])).
% 6.95/2.47  tff(c_9762, plain, (r2_hidden('#skF_3'('#skF_5', '#skF_5', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_40, c_9761])).
% 6.95/2.47  tff(c_9779, plain, ('#skF_3'('#skF_5', '#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_9762, c_36])).
% 6.95/2.47  tff(c_9785, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1598, c_9779])).
% 6.95/2.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.95/2.47  
% 6.95/2.47  Inference rules
% 6.95/2.47  ----------------------
% 6.95/2.47  #Ref     : 0
% 6.95/2.47  #Sup     : 1636
% 6.95/2.47  #Fact    : 48
% 6.95/2.47  #Define  : 0
% 6.95/2.47  #Split   : 0
% 6.95/2.47  #Chain   : 0
% 6.95/2.47  #Close   : 0
% 6.95/2.47  
% 6.95/2.47  Ordering : KBO
% 6.95/2.47  
% 6.95/2.47  Simplification rules
% 6.95/2.47  ----------------------
% 6.95/2.47  #Subsume      : 762
% 6.95/2.47  #Demod        : 145
% 6.95/2.47  #Tautology    : 567
% 6.95/2.47  #SimpNegUnit  : 70
% 6.95/2.47  #BackRed      : 0
% 6.95/2.47  
% 6.95/2.47  #Partial instantiations: 4650
% 6.95/2.47  #Strategies tried      : 1
% 6.95/2.47  
% 6.95/2.47  Timing (in seconds)
% 6.95/2.47  ----------------------
% 6.95/2.48  Preprocessing        : 0.30
% 6.95/2.48  Parsing              : 0.15
% 6.95/2.48  CNF conversion       : 0.02
% 6.95/2.48  Main loop            : 1.40
% 6.95/2.48  Inferencing          : 0.66
% 6.95/2.48  Reduction            : 0.28
% 6.95/2.48  Demodulation         : 0.19
% 6.95/2.48  BG Simplification    : 0.06
% 6.95/2.48  Subsumption          : 0.33
% 6.95/2.48  Abstraction          : 0.07
% 6.95/2.48  MUC search           : 0.00
% 6.95/2.48  Cooper               : 0.00
% 6.95/2.48  Total                : 1.73
% 6.95/2.48  Index Insertion      : 0.00
% 6.95/2.48  Index Deletion       : 0.00
% 6.95/2.48  Index Matching       : 0.00
% 6.95/2.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
