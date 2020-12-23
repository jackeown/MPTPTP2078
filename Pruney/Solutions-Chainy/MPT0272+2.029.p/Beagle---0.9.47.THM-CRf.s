%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:09 EST 2020

% Result     : Theorem 4.68s
% Output     : CNFRefutation 4.68s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 140 expanded)
%              Number of leaves         :   28 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :   88 ( 304 expanded)
%              Number of equality atoms :   44 ( 116 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
        | k4_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).

tff(c_20,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),A_3)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1348,plain,(
    ! [A_2745,B_2746,C_2747] :
      ( ~ r2_hidden('#skF_1'(A_2745,B_2746,C_2747),B_2746)
      | r2_hidden('#skF_2'(A_2745,B_2746,C_2747),C_2747)
      | k4_xboole_0(A_2745,B_2746) = C_2747 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1365,plain,(
    ! [A_3,C_5] :
      ( r2_hidden('#skF_2'(A_3,A_3,C_5),C_5)
      | k4_xboole_0(A_3,A_3) = C_5 ) ),
    inference(resolution,[status(thm)],[c_20,c_1348])).

tff(c_1370,plain,(
    ! [A_2800,C_2801] :
      ( r2_hidden('#skF_2'(A_2800,A_2800,C_2801),C_2801)
      | k4_xboole_0(A_2800,A_2800) = C_2801 ) ),
    inference(resolution,[status(thm)],[c_20,c_1348])).

tff(c_26,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_185,plain,(
    ! [A_57,B_58] : k5_xboole_0(A_57,k3_xboole_0(A_57,B_58)) = k4_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_202,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = k4_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_185])).

tff(c_205,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_202])).

tff(c_242,plain,(
    ! [D_64,B_65,A_66] :
      ( ~ r2_hidden(D_64,B_65)
      | ~ r2_hidden(D_64,k4_xboole_0(A_66,B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_248,plain,(
    ! [D_64,A_11] :
      ( ~ r2_hidden(D_64,k1_xboole_0)
      | ~ r2_hidden(D_64,A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_242])).

tff(c_1477,plain,(
    ! [A_2963,A_2964] :
      ( ~ r2_hidden('#skF_2'(A_2963,A_2963,k1_xboole_0),A_2964)
      | k4_xboole_0(A_2963,A_2963) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1370,c_248])).

tff(c_1510,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1365,c_1477])).

tff(c_1592,plain,(
    ! [A_3183,C_3184] :
      ( r2_hidden('#skF_2'(A_3183,A_3183,C_3184),C_3184)
      | k1_xboole_0 = C_3184 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1510,c_1365])).

tff(c_8,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,A_3)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2011,plain,(
    ! [A_3777,A_3778,B_3779] :
      ( r2_hidden('#skF_2'(A_3777,A_3777,k4_xboole_0(A_3778,B_3779)),A_3778)
      | k4_xboole_0(A_3778,B_3779) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1592,c_8])).

tff(c_28,plain,(
    ! [C_17,A_13] :
      ( C_17 = A_13
      | ~ r2_hidden(C_17,k1_tarski(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2244,plain,(
    ! [A_3886,A_3887,B_3888] :
      ( '#skF_2'(A_3886,A_3886,k4_xboole_0(k1_tarski(A_3887),B_3888)) = A_3887
      | k4_xboole_0(k1_tarski(A_3887),B_3888) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2011,c_28])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1635,plain,(
    ! [A_3183,A_3,B_4] :
      ( ~ r2_hidden('#skF_2'(A_3183,A_3183,k4_xboole_0(A_3,B_4)),B_4)
      | k4_xboole_0(A_3,B_4) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1592,c_6])).

tff(c_2256,plain,(
    ! [A_3887,B_3888] :
      ( ~ r2_hidden(A_3887,B_3888)
      | k4_xboole_0(k1_tarski(A_3887),B_3888) = k1_xboole_0
      | k4_xboole_0(k1_tarski(A_3887),B_3888) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2244,c_1635])).

tff(c_3790,plain,(
    ! [A_4696,B_4697] :
      ( ~ r2_hidden(A_4696,B_4697)
      | k4_xboole_0(k1_tarski(A_4696),B_4697) = k1_xboole_0 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_2256])).

tff(c_56,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_3914,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3790,c_56])).

tff(c_1409,plain,(
    ! [A_2854,B_2855,C_2856] :
      ( ~ r2_hidden('#skF_1'(A_2854,B_2855,C_2856),C_2856)
      | r2_hidden('#skF_2'(A_2854,B_2855,C_2856),C_2856)
      | k4_xboole_0(A_2854,B_2855) = C_2856 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1431,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_2'(A_3,B_4,A_3),A_3)
      | k4_xboole_0(A_3,B_4) = A_3 ) ),
    inference(resolution,[status(thm)],[c_20,c_1409])).

tff(c_1856,plain,(
    ! [A_3558,B_3559,C_3560] :
      ( r2_hidden('#skF_1'(A_3558,B_3559,C_3560),A_3558)
      | r2_hidden('#skF_2'(A_3558,B_3559,C_3560),B_3559)
      | ~ r2_hidden('#skF_2'(A_3558,B_3559,C_3560),A_3558)
      | k4_xboole_0(A_3558,B_3559) = C_3560 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),B_4)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),A_3)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2627,plain,(
    ! [A_4101,B_4102] :
      ( r2_hidden('#skF_2'(A_4101,B_4102,A_4101),B_4102)
      | ~ r2_hidden('#skF_2'(A_4101,B_4102,A_4101),A_4101)
      | k4_xboole_0(A_4101,B_4102) = A_4101 ) ),
    inference(resolution,[status(thm)],[c_1856,c_10])).

tff(c_2664,plain,(
    ! [A_4155,B_4156] :
      ( r2_hidden('#skF_2'(A_4155,B_4156,A_4155),B_4156)
      | k4_xboole_0(A_4155,B_4156) = A_4155 ) ),
    inference(resolution,[status(thm)],[c_1431,c_2627])).

tff(c_2722,plain,(
    ! [A_4209,A_4210] :
      ( '#skF_2'(A_4209,k1_tarski(A_4210),A_4209) = A_4210
      | k4_xboole_0(A_4209,k1_tarski(A_4210)) = A_4209 ) ),
    inference(resolution,[status(thm)],[c_2664,c_28])).

tff(c_2750,plain,(
    ! [A_4210,A_4209] :
      ( r2_hidden(A_4210,A_4209)
      | k4_xboole_0(A_4209,k1_tarski(A_4210)) = A_4209
      | k4_xboole_0(A_4209,k1_tarski(A_4210)) = A_4209 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2722,c_1431])).

tff(c_2918,plain,(
    ! [A_4210,A_4209] :
      ( r2_hidden(A_4210,A_4209)
      | k4_xboole_0(A_4209,k1_tarski(A_4210)) = A_4209 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_2750])).

tff(c_5177,plain,(
    ! [A_5402,A_5403,B_5404] :
      ( ~ r2_hidden('#skF_2'(A_5402,k4_xboole_0(A_5403,B_5404),A_5402),B_5404)
      | k4_xboole_0(A_5402,k4_xboole_0(A_5403,B_5404)) = A_5402 ) ),
    inference(resolution,[status(thm)],[c_2664,c_6])).

tff(c_5247,plain,(
    ! [A_5457,A_5458] : k4_xboole_0(A_5457,k4_xboole_0(A_5458,A_5457)) = A_5457 ),
    inference(resolution,[status(thm)],[c_1431,c_5177])).

tff(c_5546,plain,(
    ! [A_5620,A_5621] :
      ( k4_xboole_0(k1_tarski(A_5620),A_5621) = k1_tarski(A_5620)
      | r2_hidden(A_5620,A_5621) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2918,c_5247])).

tff(c_54,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_5613,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_5546,c_54])).

tff(c_5718,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3914,c_5613])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:18:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.68/1.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.90  
% 4.68/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.90  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 4.68/1.90  
% 4.68/1.90  %Foreground sorts:
% 4.68/1.90  
% 4.68/1.90  
% 4.68/1.90  %Background operators:
% 4.68/1.90  
% 4.68/1.90  
% 4.68/1.90  %Foreground operators:
% 4.68/1.90  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.68/1.90  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.68/1.90  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.68/1.90  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.68/1.90  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.68/1.90  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.68/1.90  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.68/1.90  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.68/1.90  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.68/1.90  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.68/1.90  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.68/1.90  tff('#skF_5', type, '#skF_5': $i).
% 4.68/1.90  tff('#skF_6', type, '#skF_6': $i).
% 4.68/1.90  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.68/1.90  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.68/1.90  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.68/1.90  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.68/1.90  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.68/1.90  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.68/1.90  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.68/1.90  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.68/1.90  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.68/1.90  
% 4.68/1.91  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.68/1.91  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.68/1.91  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 4.68/1.91  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.68/1.91  tff(f_50, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 4.68/1.91  tff(f_69, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) | (k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 4.68/1.91  tff(c_20, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), A_3) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.68/1.91  tff(c_1348, plain, (![A_2745, B_2746, C_2747]: (~r2_hidden('#skF_1'(A_2745, B_2746, C_2747), B_2746) | r2_hidden('#skF_2'(A_2745, B_2746, C_2747), C_2747) | k4_xboole_0(A_2745, B_2746)=C_2747)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.68/1.91  tff(c_1365, plain, (![A_3, C_5]: (r2_hidden('#skF_2'(A_3, A_3, C_5), C_5) | k4_xboole_0(A_3, A_3)=C_5)), inference(resolution, [status(thm)], [c_20, c_1348])).
% 4.68/1.91  tff(c_1370, plain, (![A_2800, C_2801]: (r2_hidden('#skF_2'(A_2800, A_2800, C_2801), C_2801) | k4_xboole_0(A_2800, A_2800)=C_2801)), inference(resolution, [status(thm)], [c_20, c_1348])).
% 4.68/1.91  tff(c_26, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.68/1.91  tff(c_24, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.68/1.91  tff(c_185, plain, (![A_57, B_58]: (k5_xboole_0(A_57, k3_xboole_0(A_57, B_58))=k4_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.68/1.91  tff(c_202, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=k4_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_185])).
% 4.68/1.91  tff(c_205, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_202])).
% 4.68/1.91  tff(c_242, plain, (![D_64, B_65, A_66]: (~r2_hidden(D_64, B_65) | ~r2_hidden(D_64, k4_xboole_0(A_66, B_65)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.68/1.91  tff(c_248, plain, (![D_64, A_11]: (~r2_hidden(D_64, k1_xboole_0) | ~r2_hidden(D_64, A_11))), inference(superposition, [status(thm), theory('equality')], [c_205, c_242])).
% 4.68/1.91  tff(c_1477, plain, (![A_2963, A_2964]: (~r2_hidden('#skF_2'(A_2963, A_2963, k1_xboole_0), A_2964) | k4_xboole_0(A_2963, A_2963)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1370, c_248])).
% 4.68/1.91  tff(c_1510, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1365, c_1477])).
% 4.68/1.91  tff(c_1592, plain, (![A_3183, C_3184]: (r2_hidden('#skF_2'(A_3183, A_3183, C_3184), C_3184) | k1_xboole_0=C_3184)), inference(demodulation, [status(thm), theory('equality')], [c_1510, c_1365])).
% 4.68/1.91  tff(c_8, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, A_3) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.68/1.91  tff(c_2011, plain, (![A_3777, A_3778, B_3779]: (r2_hidden('#skF_2'(A_3777, A_3777, k4_xboole_0(A_3778, B_3779)), A_3778) | k4_xboole_0(A_3778, B_3779)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1592, c_8])).
% 4.68/1.91  tff(c_28, plain, (![C_17, A_13]: (C_17=A_13 | ~r2_hidden(C_17, k1_tarski(A_13)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.68/1.91  tff(c_2244, plain, (![A_3886, A_3887, B_3888]: ('#skF_2'(A_3886, A_3886, k4_xboole_0(k1_tarski(A_3887), B_3888))=A_3887 | k4_xboole_0(k1_tarski(A_3887), B_3888)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2011, c_28])).
% 4.68/1.91  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.68/1.91  tff(c_1635, plain, (![A_3183, A_3, B_4]: (~r2_hidden('#skF_2'(A_3183, A_3183, k4_xboole_0(A_3, B_4)), B_4) | k4_xboole_0(A_3, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1592, c_6])).
% 4.68/1.91  tff(c_2256, plain, (![A_3887, B_3888]: (~r2_hidden(A_3887, B_3888) | k4_xboole_0(k1_tarski(A_3887), B_3888)=k1_xboole_0 | k4_xboole_0(k1_tarski(A_3887), B_3888)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2244, c_1635])).
% 4.68/1.91  tff(c_3790, plain, (![A_4696, B_4697]: (~r2_hidden(A_4696, B_4697) | k4_xboole_0(k1_tarski(A_4696), B_4697)=k1_xboole_0)), inference(factorization, [status(thm), theory('equality')], [c_2256])).
% 4.68/1.91  tff(c_56, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.68/1.91  tff(c_3914, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3790, c_56])).
% 4.68/1.91  tff(c_1409, plain, (![A_2854, B_2855, C_2856]: (~r2_hidden('#skF_1'(A_2854, B_2855, C_2856), C_2856) | r2_hidden('#skF_2'(A_2854, B_2855, C_2856), C_2856) | k4_xboole_0(A_2854, B_2855)=C_2856)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.68/1.91  tff(c_1431, plain, (![A_3, B_4]: (r2_hidden('#skF_2'(A_3, B_4, A_3), A_3) | k4_xboole_0(A_3, B_4)=A_3)), inference(resolution, [status(thm)], [c_20, c_1409])).
% 4.68/1.91  tff(c_1856, plain, (![A_3558, B_3559, C_3560]: (r2_hidden('#skF_1'(A_3558, B_3559, C_3560), A_3558) | r2_hidden('#skF_2'(A_3558, B_3559, C_3560), B_3559) | ~r2_hidden('#skF_2'(A_3558, B_3559, C_3560), A_3558) | k4_xboole_0(A_3558, B_3559)=C_3560)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.68/1.91  tff(c_10, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | r2_hidden('#skF_2'(A_3, B_4, C_5), B_4) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), A_3) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.68/1.91  tff(c_2627, plain, (![A_4101, B_4102]: (r2_hidden('#skF_2'(A_4101, B_4102, A_4101), B_4102) | ~r2_hidden('#skF_2'(A_4101, B_4102, A_4101), A_4101) | k4_xboole_0(A_4101, B_4102)=A_4101)), inference(resolution, [status(thm)], [c_1856, c_10])).
% 4.68/1.91  tff(c_2664, plain, (![A_4155, B_4156]: (r2_hidden('#skF_2'(A_4155, B_4156, A_4155), B_4156) | k4_xboole_0(A_4155, B_4156)=A_4155)), inference(resolution, [status(thm)], [c_1431, c_2627])).
% 4.68/1.91  tff(c_2722, plain, (![A_4209, A_4210]: ('#skF_2'(A_4209, k1_tarski(A_4210), A_4209)=A_4210 | k4_xboole_0(A_4209, k1_tarski(A_4210))=A_4209)), inference(resolution, [status(thm)], [c_2664, c_28])).
% 4.68/1.91  tff(c_2750, plain, (![A_4210, A_4209]: (r2_hidden(A_4210, A_4209) | k4_xboole_0(A_4209, k1_tarski(A_4210))=A_4209 | k4_xboole_0(A_4209, k1_tarski(A_4210))=A_4209)), inference(superposition, [status(thm), theory('equality')], [c_2722, c_1431])).
% 4.68/1.91  tff(c_2918, plain, (![A_4210, A_4209]: (r2_hidden(A_4210, A_4209) | k4_xboole_0(A_4209, k1_tarski(A_4210))=A_4209)), inference(factorization, [status(thm), theory('equality')], [c_2750])).
% 4.68/1.92  tff(c_5177, plain, (![A_5402, A_5403, B_5404]: (~r2_hidden('#skF_2'(A_5402, k4_xboole_0(A_5403, B_5404), A_5402), B_5404) | k4_xboole_0(A_5402, k4_xboole_0(A_5403, B_5404))=A_5402)), inference(resolution, [status(thm)], [c_2664, c_6])).
% 4.68/1.92  tff(c_5247, plain, (![A_5457, A_5458]: (k4_xboole_0(A_5457, k4_xboole_0(A_5458, A_5457))=A_5457)), inference(resolution, [status(thm)], [c_1431, c_5177])).
% 4.68/1.92  tff(c_5546, plain, (![A_5620, A_5621]: (k4_xboole_0(k1_tarski(A_5620), A_5621)=k1_tarski(A_5620) | r2_hidden(A_5620, A_5621))), inference(superposition, [status(thm), theory('equality')], [c_2918, c_5247])).
% 4.68/1.92  tff(c_54, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.68/1.92  tff(c_5613, plain, (r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_5546, c_54])).
% 4.68/1.92  tff(c_5718, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3914, c_5613])).
% 4.68/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.92  
% 4.68/1.92  Inference rules
% 4.68/1.92  ----------------------
% 4.68/1.92  #Ref     : 0
% 4.68/1.92  #Sup     : 877
% 4.68/1.92  #Fact    : 8
% 4.68/1.92  #Define  : 0
% 4.68/1.92  #Split   : 1
% 4.68/1.92  #Chain   : 0
% 4.68/1.92  #Close   : 0
% 4.68/1.92  
% 4.68/1.92  Ordering : KBO
% 4.68/1.92  
% 4.68/1.92  Simplification rules
% 4.68/1.92  ----------------------
% 4.68/1.92  #Subsume      : 192
% 4.68/1.92  #Demod        : 302
% 4.68/1.92  #Tautology    : 333
% 4.68/1.92  #SimpNegUnit  : 1
% 4.68/1.92  #BackRed      : 3
% 4.68/1.92  
% 4.68/1.92  #Partial instantiations: 1854
% 4.68/1.92  #Strategies tried      : 1
% 4.68/1.92  
% 4.68/1.92  Timing (in seconds)
% 4.68/1.92  ----------------------
% 4.68/1.92  Preprocessing        : 0.32
% 4.68/1.92  Parsing              : 0.16
% 4.68/1.92  CNF conversion       : 0.02
% 4.68/1.92  Main loop            : 0.85
% 4.68/1.92  Inferencing          : 0.39
% 4.68/1.92  Reduction            : 0.20
% 4.68/1.92  Demodulation         : 0.14
% 4.68/1.92  BG Simplification    : 0.04
% 4.68/1.92  Subsumption          : 0.17
% 4.68/1.92  Abstraction          : 0.05
% 4.68/1.92  MUC search           : 0.00
% 4.68/1.92  Cooper               : 0.00
% 4.68/1.92  Total                : 1.19
% 4.68/1.92  Index Insertion      : 0.00
% 4.68/1.92  Index Deletion       : 0.00
% 4.68/1.92  Index Matching       : 0.00
% 4.68/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
