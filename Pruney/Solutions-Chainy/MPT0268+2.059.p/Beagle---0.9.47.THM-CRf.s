%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:42 EST 2020

% Result     : Theorem 17.78s
% Output     : CNFRefutation 17.78s
% Verified   : 
% Statistics : Number of formulae       :   62 (  89 expanded)
%              Number of leaves         :   29 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :   67 ( 137 expanded)
%              Number of equality atoms :   24 (  50 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_60,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_141,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_62,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_102,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_2622,plain,(
    ! [A_3583,B_3584,C_3585] :
      ( r2_hidden('#skF_1'(A_3583,B_3584,C_3585),A_3583)
      | r2_hidden('#skF_2'(A_3583,B_3584,C_3585),C_3585)
      | k4_xboole_0(A_3583,B_3584) = C_3585 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2670,plain,(
    ! [A_3583,B_3584] :
      ( r2_hidden('#skF_2'(A_3583,B_3584,A_3583),A_3583)
      | k4_xboole_0(A_3583,B_3584) = A_3583 ) ),
    inference(resolution,[status(thm)],[c_2622,c_14])).

tff(c_12,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3027,plain,(
    ! [A_4100,B_4101,C_4102] :
      ( ~ r2_hidden('#skF_1'(A_4100,B_4101,C_4102),C_4102)
      | r2_hidden('#skF_2'(A_4100,B_4101,C_4102),B_4101)
      | ~ r2_hidden('#skF_2'(A_4100,B_4101,C_4102),A_4100)
      | k4_xboole_0(A_4100,B_4101) = C_4102 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_34758,plain,(
    ! [A_36611,B_36612] :
      ( r2_hidden('#skF_2'(A_36611,B_36612,A_36611),B_36612)
      | ~ r2_hidden('#skF_2'(A_36611,B_36612,A_36611),A_36611)
      | k4_xboole_0(A_36611,B_36612) = A_36611 ) ),
    inference(resolution,[status(thm)],[c_12,c_3027])).

tff(c_34809,plain,(
    ! [A_36888,B_36889] :
      ( r2_hidden('#skF_2'(A_36888,B_36889,A_36888),B_36889)
      | k4_xboole_0(A_36888,B_36889) = A_36888 ) ),
    inference(resolution,[status(thm)],[c_2670,c_34758])).

tff(c_30,plain,(
    ! [C_21,A_17] :
      ( C_21 = A_17
      | ~ r2_hidden(C_21,k1_tarski(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_43095,plain,(
    ! [A_41875,A_41876] :
      ( '#skF_2'(A_41875,k1_tarski(A_41876),A_41875) = A_41876
      | k4_xboole_0(A_41875,k1_tarski(A_41876)) = A_41875 ) ),
    inference(resolution,[status(thm)],[c_34809,c_30])).

tff(c_43341,plain,(
    '#skF_2'('#skF_5',k1_tarski('#skF_6'),'#skF_5') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_43095,c_141])).

tff(c_43356,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_43341,c_2670])).

tff(c_43420,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_102,c_43356])).

tff(c_43421,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_32,plain,(
    ! [C_21] : r2_hidden(C_21,k1_tarski(C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_43422,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_64,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_43470,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43422,c_64])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_43487,plain,(
    ! [D_42439] :
      ( ~ r2_hidden(D_42439,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_42439,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43470,c_4])).

tff(c_43491,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_43487])).

tff(c_43495,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_43421,c_43491])).

tff(c_43496,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_43497,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_66,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_43537,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_43497,c_66])).

tff(c_43542,plain,(
    ! [D_42447,B_42448,A_42449] :
      ( ~ r2_hidden(D_42447,B_42448)
      | ~ r2_hidden(D_42447,k4_xboole_0(A_42449,B_42448)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_43546,plain,(
    ! [D_42450] :
      ( ~ r2_hidden(D_42450,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_42450,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_43537,c_43542])).

tff(c_43550,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_43546])).

tff(c_43554,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_43496,c_43550])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:32:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.78/9.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.78/9.63  
% 17.78/9.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.78/9.63  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4
% 17.78/9.63  
% 17.78/9.63  %Foreground sorts:
% 17.78/9.63  
% 17.78/9.63  
% 17.78/9.63  %Background operators:
% 17.78/9.63  
% 17.78/9.63  
% 17.78/9.63  %Foreground operators:
% 17.78/9.63  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 17.78/9.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.78/9.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.78/9.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 17.78/9.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 17.78/9.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.78/9.63  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 17.78/9.63  tff('#skF_7', type, '#skF_7': $i).
% 17.78/9.63  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 17.78/9.63  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 17.78/9.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 17.78/9.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 17.78/9.63  tff('#skF_5', type, '#skF_5': $i).
% 17.78/9.63  tff('#skF_6', type, '#skF_6': $i).
% 17.78/9.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 17.78/9.63  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 17.78/9.63  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 17.78/9.63  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 17.78/9.63  tff('#skF_8', type, '#skF_8': $i).
% 17.78/9.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.78/9.63  tff(k3_tarski, type, k3_tarski: $i > $i).
% 17.78/9.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.78/9.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 17.78/9.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 17.78/9.63  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 17.78/9.63  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 17.78/9.63  
% 17.78/9.64  tff(f_76, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 17.78/9.64  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 17.78/9.64  tff(f_52, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 17.78/9.64  tff(c_60, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_76])).
% 17.78/9.64  tff(c_141, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_60])).
% 17.78/9.64  tff(c_62, plain, (~r2_hidden('#skF_6', '#skF_5') | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_76])).
% 17.78/9.64  tff(c_102, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_62])).
% 17.78/9.64  tff(c_2622, plain, (![A_3583, B_3584, C_3585]: (r2_hidden('#skF_1'(A_3583, B_3584, C_3585), A_3583) | r2_hidden('#skF_2'(A_3583, B_3584, C_3585), C_3585) | k4_xboole_0(A_3583, B_3584)=C_3585)), inference(cnfTransformation, [status(thm)], [f_35])).
% 17.78/9.64  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 17.78/9.64  tff(c_2670, plain, (![A_3583, B_3584]: (r2_hidden('#skF_2'(A_3583, B_3584, A_3583), A_3583) | k4_xboole_0(A_3583, B_3584)=A_3583)), inference(resolution, [status(thm)], [c_2622, c_14])).
% 17.78/9.64  tff(c_12, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 17.78/9.64  tff(c_3027, plain, (![A_4100, B_4101, C_4102]: (~r2_hidden('#skF_1'(A_4100, B_4101, C_4102), C_4102) | r2_hidden('#skF_2'(A_4100, B_4101, C_4102), B_4101) | ~r2_hidden('#skF_2'(A_4100, B_4101, C_4102), A_4100) | k4_xboole_0(A_4100, B_4101)=C_4102)), inference(cnfTransformation, [status(thm)], [f_35])).
% 17.78/9.64  tff(c_34758, plain, (![A_36611, B_36612]: (r2_hidden('#skF_2'(A_36611, B_36612, A_36611), B_36612) | ~r2_hidden('#skF_2'(A_36611, B_36612, A_36611), A_36611) | k4_xboole_0(A_36611, B_36612)=A_36611)), inference(resolution, [status(thm)], [c_12, c_3027])).
% 17.78/9.64  tff(c_34809, plain, (![A_36888, B_36889]: (r2_hidden('#skF_2'(A_36888, B_36889, A_36888), B_36889) | k4_xboole_0(A_36888, B_36889)=A_36888)), inference(resolution, [status(thm)], [c_2670, c_34758])).
% 17.78/9.64  tff(c_30, plain, (![C_21, A_17]: (C_21=A_17 | ~r2_hidden(C_21, k1_tarski(A_17)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 17.78/9.64  tff(c_43095, plain, (![A_41875, A_41876]: ('#skF_2'(A_41875, k1_tarski(A_41876), A_41875)=A_41876 | k4_xboole_0(A_41875, k1_tarski(A_41876))=A_41875)), inference(resolution, [status(thm)], [c_34809, c_30])).
% 17.78/9.64  tff(c_43341, plain, ('#skF_2'('#skF_5', k1_tarski('#skF_6'), '#skF_5')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_43095, c_141])).
% 17.78/9.64  tff(c_43356, plain, (r2_hidden('#skF_6', '#skF_5') | k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_43341, c_2670])).
% 17.78/9.64  tff(c_43420, plain, $false, inference(negUnitSimplification, [status(thm)], [c_141, c_102, c_43356])).
% 17.78/9.64  tff(c_43421, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_60])).
% 17.78/9.64  tff(c_32, plain, (![C_21]: (r2_hidden(C_21, k1_tarski(C_21)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 17.78/9.64  tff(c_43422, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_60])).
% 17.78/9.64  tff(c_64, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_76])).
% 17.78/9.64  tff(c_43470, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_43422, c_64])).
% 17.78/9.64  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 17.78/9.64  tff(c_43487, plain, (![D_42439]: (~r2_hidden(D_42439, k1_tarski('#skF_8')) | ~r2_hidden(D_42439, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_43470, c_4])).
% 17.78/9.64  tff(c_43491, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_32, c_43487])).
% 17.78/9.64  tff(c_43495, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_43421, c_43491])).
% 17.78/9.64  tff(c_43496, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_62])).
% 17.78/9.64  tff(c_43497, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_62])).
% 17.78/9.64  tff(c_66, plain, (~r2_hidden('#skF_6', '#skF_5') | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_76])).
% 17.78/9.64  tff(c_43537, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_43497, c_66])).
% 17.78/9.64  tff(c_43542, plain, (![D_42447, B_42448, A_42449]: (~r2_hidden(D_42447, B_42448) | ~r2_hidden(D_42447, k4_xboole_0(A_42449, B_42448)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 17.78/9.64  tff(c_43546, plain, (![D_42450]: (~r2_hidden(D_42450, k1_tarski('#skF_8')) | ~r2_hidden(D_42450, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_43537, c_43542])).
% 17.78/9.64  tff(c_43550, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_32, c_43546])).
% 17.78/9.64  tff(c_43554, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_43496, c_43550])).
% 17.78/9.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.78/9.64  
% 17.78/9.64  Inference rules
% 17.78/9.64  ----------------------
% 17.78/9.64  #Ref     : 0
% 17.78/9.64  #Sup     : 10666
% 17.78/9.64  #Fact    : 6
% 17.78/9.64  #Define  : 0
% 17.78/9.64  #Split   : 3
% 17.78/9.64  #Chain   : 0
% 17.78/9.64  #Close   : 0
% 17.78/9.64  
% 17.78/9.64  Ordering : KBO
% 17.78/9.64  
% 17.78/9.64  Simplification rules
% 17.78/9.64  ----------------------
% 17.78/9.64  #Subsume      : 668
% 17.78/9.64  #Demod        : 15664
% 17.78/9.64  #Tautology    : 4104
% 17.78/9.64  #SimpNegUnit  : 19
% 17.78/9.64  #BackRed      : 19
% 17.78/9.64  
% 17.78/9.64  #Partial instantiations: 10186
% 17.78/9.64  #Strategies tried      : 1
% 17.78/9.64  
% 17.78/9.64  Timing (in seconds)
% 17.78/9.64  ----------------------
% 17.78/9.65  Preprocessing        : 0.34
% 17.78/9.65  Parsing              : 0.17
% 17.78/9.65  CNF conversion       : 0.03
% 17.78/9.65  Main loop            : 8.53
% 17.78/9.65  Inferencing          : 1.43
% 17.78/9.65  Reduction            : 5.63
% 17.78/9.65  Demodulation         : 5.31
% 17.78/9.65  BG Simplification    : 0.21
% 17.78/9.65  Subsumption          : 1.00
% 17.78/9.65  Abstraction          : 0.31
% 17.78/9.65  MUC search           : 0.00
% 17.78/9.65  Cooper               : 0.00
% 17.78/9.65  Total                : 8.90
% 17.78/9.65  Index Insertion      : 0.00
% 17.78/9.65  Index Deletion       : 0.00
% 17.78/9.65  Index Matching       : 0.00
% 17.78/9.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
