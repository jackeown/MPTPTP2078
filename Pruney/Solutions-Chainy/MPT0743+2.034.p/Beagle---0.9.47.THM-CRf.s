%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:12 EST 2020

% Result     : Theorem 11.79s
% Output     : CNFRefutation 11.84s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 295 expanded)
%              Number of leaves         :   33 ( 109 expanded)
%              Depth                    :   15
%              Number of atoms          :  224 ( 686 expanded)
%              Number of equality atoms :   22 (  57 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,B)
            <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_103,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_99,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_108,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_73,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_84,axiom,(
    ! [A] : A != k1_ordinal1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(c_50,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_52,plain,(
    v3_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_8494,plain,(
    ! [A_488,B_489] :
      ( r1_tarski(A_488,B_489)
      | ~ r1_ordinal1(A_488,B_489)
      | ~ v3_ordinal1(B_489)
      | ~ v3_ordinal1(A_488) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_46,plain,(
    ! [A_52] :
      ( v3_ordinal1(k1_ordinal1(A_52))
      | ~ v3_ordinal1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_825,plain,(
    ! [B_138,A_139] :
      ( r2_hidden(B_138,A_139)
      | B_138 = A_139
      | r2_hidden(A_139,B_138)
      | ~ v3_ordinal1(B_138)
      | ~ v3_ordinal1(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_48,plain,(
    ! [B_54,A_53] :
      ( ~ r1_tarski(B_54,A_53)
      | ~ r2_hidden(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2618,plain,(
    ! [B_232,A_233] :
      ( ~ r1_tarski(B_232,A_233)
      | r2_hidden(B_232,A_233)
      | B_232 = A_233
      | ~ v3_ordinal1(B_232)
      | ~ v3_ordinal1(A_233) ) ),
    inference(resolution,[status(thm)],[c_825,c_48])).

tff(c_54,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_88,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_2628,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | '#skF_2' = '#skF_1'
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2618,c_88])).

tff(c_2636,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_2628])).

tff(c_2637,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2636])).

tff(c_60,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_99,plain,(
    r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_60])).

tff(c_40,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ r1_ordinal1(A_46,B_47)
      | ~ v3_ordinal1(B_47)
      | ~ v3_ordinal1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_36,plain,(
    ! [A_45] : k2_xboole_0(A_45,k1_tarski(A_45)) = k1_ordinal1(A_45) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_202,plain,(
    ! [A_83,C_84,B_85] :
      ( r1_tarski(A_83,C_84)
      | ~ r1_tarski(k2_xboole_0(A_83,B_85),C_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_503,plain,(
    ! [A_115,C_116] :
      ( r1_tarski(A_115,C_116)
      | ~ r1_tarski(k1_ordinal1(A_115),C_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_202])).

tff(c_7765,plain,(
    ! [A_425,B_426] :
      ( r1_tarski(A_425,B_426)
      | ~ r1_ordinal1(k1_ordinal1(A_425),B_426)
      | ~ v3_ordinal1(B_426)
      | ~ v3_ordinal1(k1_ordinal1(A_425)) ) ),
    inference(resolution,[status(thm)],[c_40,c_503])).

tff(c_7799,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_99,c_7765])).

tff(c_7812,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_7799])).

tff(c_7813,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_2637,c_7812])).

tff(c_7816,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_7813])).

tff(c_7820,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_7816])).

tff(c_7821,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2636])).

tff(c_7823,plain,(
    r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7821,c_99])).

tff(c_455,plain,(
    ! [A_113,B_114] :
      ( r1_tarski(A_113,B_114)
      | ~ r1_ordinal1(A_113,B_114)
      | ~ v3_ordinal1(B_114)
      | ~ v3_ordinal1(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_42,plain,(
    ! [A_48] : k1_ordinal1(A_48) != A_48 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_75,plain,(
    ! [A_62] : k2_xboole_0(A_62,k1_tarski(A_62)) = k1_ordinal1(A_62) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_81,plain,(
    ! [A_62] : r1_tarski(A_62,k1_ordinal1(A_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_10])).

tff(c_163,plain,(
    ! [B_76,A_77] :
      ( B_76 = A_77
      | ~ r1_tarski(B_76,A_77)
      | ~ r1_tarski(A_77,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_169,plain,(
    ! [A_62] :
      ( k1_ordinal1(A_62) = A_62
      | ~ r1_tarski(k1_ordinal1(A_62),A_62) ) ),
    inference(resolution,[status(thm)],[c_81,c_163])).

tff(c_178,plain,(
    ! [A_62] : ~ r1_tarski(k1_ordinal1(A_62),A_62) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_169])).

tff(c_7995,plain,(
    ! [B_435] :
      ( ~ r1_ordinal1(k1_ordinal1(B_435),B_435)
      | ~ v3_ordinal1(B_435)
      | ~ v3_ordinal1(k1_ordinal1(B_435)) ) ),
    inference(resolution,[status(thm)],[c_455,c_178])).

tff(c_7998,plain,
    ( ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_7823,c_7995])).

tff(c_8009,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_7998])).

tff(c_8014,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_8009])).

tff(c_8018,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_8014])).

tff(c_8020,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_8021,plain,(
    ! [B_436,A_437] :
      ( ~ r1_tarski(B_436,A_437)
      | ~ r2_hidden(A_437,B_436) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_8025,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_8020,c_8021])).

tff(c_8538,plain,
    ( ~ r1_ordinal1('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8494,c_8025])).

tff(c_8552,plain,(
    ~ r1_ordinal1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_8538])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_8,C_10,B_9] :
      ( r1_tarski(k2_xboole_0(A_8,C_10),B_9)
      | ~ r1_tarski(C_10,B_9)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8141,plain,(
    ! [B_457,A_458] :
      ( B_457 = A_458
      | ~ r1_tarski(B_457,A_458)
      | ~ r1_tarski(A_458,B_457) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_9183,plain,(
    ! [A_551,B_552] :
      ( k2_xboole_0(A_551,B_552) = A_551
      | ~ r1_tarski(k2_xboole_0(A_551,B_552),A_551) ) ),
    inference(resolution,[status(thm)],[c_10,c_8141])).

tff(c_9187,plain,(
    ! [B_9,C_10] :
      ( k2_xboole_0(B_9,C_10) = B_9
      | ~ r1_tarski(C_10,B_9)
      | ~ r1_tarski(B_9,B_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_9183])).

tff(c_9204,plain,(
    ! [B_553,C_554] :
      ( k2_xboole_0(B_553,C_554) = B_553
      | ~ r1_tarski(C_554,B_553) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_9187])).

tff(c_9300,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_9204])).

tff(c_34,plain,(
    ! [B_44,A_43] :
      ( r1_ordinal1(B_44,A_43)
      | r1_ordinal1(A_43,B_44)
      | ~ v3_ordinal1(B_44)
      | ~ v3_ordinal1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_11618,plain,(
    ! [A_656,B_657,B_658] :
      ( r1_tarski(A_656,B_657)
      | ~ r1_ordinal1(k2_xboole_0(A_656,B_658),B_657)
      | ~ v3_ordinal1(B_657)
      | ~ v3_ordinal1(k2_xboole_0(A_656,B_658)) ) ),
    inference(resolution,[status(thm)],[c_8494,c_8])).

tff(c_21703,plain,(
    ! [A_935,A_936,B_937] :
      ( r1_tarski(A_935,A_936)
      | r1_ordinal1(A_936,k2_xboole_0(A_935,B_937))
      | ~ v3_ordinal1(k2_xboole_0(A_935,B_937))
      | ~ v3_ordinal1(A_936) ) ),
    inference(resolution,[status(thm)],[c_34,c_11618])).

tff(c_21783,plain,(
    ! [B_2,A_936] :
      ( r1_tarski(B_2,A_936)
      | r1_ordinal1(A_936,B_2)
      | ~ v3_ordinal1(k2_xboole_0(B_2,B_2))
      | ~ v3_ordinal1(A_936) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9300,c_21703])).

tff(c_21818,plain,(
    ! [B_2,A_936] :
      ( r1_tarski(B_2,A_936)
      | r1_ordinal1(A_936,B_2)
      | ~ v3_ordinal1(B_2)
      | ~ v3_ordinal1(A_936) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9300,c_21783])).

tff(c_30,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(k1_tarski(A_39),B_40)
      | ~ r2_hidden(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8566,plain,(
    ! [A_490,C_491,B_492] :
      ( r1_tarski(k2_xboole_0(A_490,C_491),B_492)
      | ~ r1_tarski(C_491,B_492)
      | ~ r1_tarski(A_490,B_492) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_9982,plain,(
    ! [A_576,B_577] :
      ( r1_tarski(k1_ordinal1(A_576),B_577)
      | ~ r1_tarski(k1_tarski(A_576),B_577)
      | ~ r1_tarski(A_576,B_577) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_8566])).

tff(c_10063,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(k1_ordinal1(A_39),B_40)
      | ~ r1_tarski(A_39,B_40)
      | ~ r2_hidden(A_39,B_40) ) ),
    inference(resolution,[status(thm)],[c_30,c_9982])).

tff(c_8469,plain,(
    ! [B_486,A_487] :
      ( r1_ordinal1(B_486,A_487)
      | r1_ordinal1(A_487,B_486)
      | ~ v3_ordinal1(B_486)
      | ~ v3_ordinal1(A_487) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8019,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_8472,plain,
    ( r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8469,c_8019])).

tff(c_8478,plain,
    ( r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_8472])).

tff(c_8482,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_8478])).

tff(c_8485,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_8482])).

tff(c_8489,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_8485])).

tff(c_8491,plain,(
    v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_8478])).

tff(c_8490,plain,(
    r1_ordinal1('#skF_2',k1_ordinal1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_8478])).

tff(c_18154,plain,(
    ! [B_859,A_860] :
      ( k2_xboole_0(B_859,A_860) = B_859
      | ~ r1_ordinal1(A_860,B_859)
      | ~ v3_ordinal1(B_859)
      | ~ v3_ordinal1(A_860) ) ),
    inference(resolution,[status(thm)],[c_40,c_9204])).

tff(c_18178,plain,
    ( k2_xboole_0(k1_ordinal1('#skF_1'),'#skF_2') = k1_ordinal1('#skF_1')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8490,c_18154])).

tff(c_18201,plain,(
    k2_xboole_0(k1_ordinal1('#skF_1'),'#skF_2') = k1_ordinal1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_8491,c_18178])).

tff(c_38,plain,(
    ! [A_46,B_47] :
      ( r1_ordinal1(A_46,B_47)
      | ~ r1_tarski(A_46,B_47)
      | ~ v3_ordinal1(B_47)
      | ~ v3_ordinal1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_8585,plain,(
    ! [A_490,C_491,B_492] :
      ( r1_ordinal1(k2_xboole_0(A_490,C_491),B_492)
      | ~ v3_ordinal1(B_492)
      | ~ v3_ordinal1(k2_xboole_0(A_490,C_491))
      | ~ r1_tarski(C_491,B_492)
      | ~ r1_tarski(A_490,B_492) ) ),
    inference(resolution,[status(thm)],[c_8566,c_38])).

tff(c_18406,plain,(
    ! [B_492] :
      ( r1_ordinal1(k1_ordinal1('#skF_1'),B_492)
      | ~ v3_ordinal1(B_492)
      | ~ v3_ordinal1(k2_xboole_0(k1_ordinal1('#skF_1'),'#skF_2'))
      | ~ r1_tarski('#skF_2',B_492)
      | ~ r1_tarski(k1_ordinal1('#skF_1'),B_492) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18201,c_8585])).

tff(c_18890,plain,(
    ! [B_868] :
      ( r1_ordinal1(k1_ordinal1('#skF_1'),B_868)
      | ~ v3_ordinal1(B_868)
      | ~ r1_tarski('#skF_2',B_868)
      | ~ r1_tarski(k1_ordinal1('#skF_1'),B_868) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8491,c_18201,c_18406])).

tff(c_26091,plain,(
    ! [B_1043] :
      ( r1_ordinal1(k1_ordinal1('#skF_1'),B_1043)
      | ~ v3_ordinal1(B_1043)
      | ~ r1_tarski('#skF_2',B_1043)
      | ~ r1_tarski('#skF_1',B_1043)
      | ~ r2_hidden('#skF_1',B_1043) ) ),
    inference(resolution,[status(thm)],[c_10063,c_18890])).

tff(c_26125,plain,
    ( ~ v3_ordinal1('#skF_2')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ r1_tarski('#skF_1','#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_26091,c_8019])).

tff(c_26154,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8020,c_6,c_50,c_26125])).

tff(c_26157,plain,
    ( r1_ordinal1('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_21818,c_26154])).

tff(c_26163,plain,(
    r1_ordinal1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_26157])).

tff(c_26165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8552,c_26163])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:20:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.79/4.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.79/4.58  
% 11.79/4.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.84/4.59  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1
% 11.84/4.59  
% 11.84/4.59  %Foreground sorts:
% 11.84/4.59  
% 11.84/4.59  
% 11.84/4.59  %Background operators:
% 11.84/4.59  
% 11.84/4.59  
% 11.84/4.59  %Foreground operators:
% 11.84/4.59  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 11.84/4.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.84/4.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.84/4.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.84/4.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 11.84/4.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.84/4.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.84/4.59  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 11.84/4.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.84/4.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.84/4.59  tff('#skF_2', type, '#skF_2': $i).
% 11.84/4.59  tff('#skF_1', type, '#skF_1': $i).
% 11.84/4.59  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 11.84/4.59  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 11.84/4.59  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 11.84/4.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.84/4.59  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.84/4.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.84/4.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.84/4.59  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 11.84/4.59  
% 11.84/4.61  tff(f_118, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_ordinal1)).
% 11.84/4.61  tff(f_81, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 11.84/4.61  tff(f_103, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 11.84/4.61  tff(f_99, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 11.84/4.61  tff(f_108, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 11.84/4.61  tff(f_73, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 11.84/4.61  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 11.84/4.61  tff(f_84, axiom, (![A]: ~(A = k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_ordinal1)).
% 11.84/4.61  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 11.84/4.61  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.84/4.61  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 11.84/4.61  tff(f_71, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 11.84/4.61  tff(f_61, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 11.84/4.61  tff(c_50, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.84/4.61  tff(c_52, plain, (v3_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.84/4.61  tff(c_8494, plain, (![A_488, B_489]: (r1_tarski(A_488, B_489) | ~r1_ordinal1(A_488, B_489) | ~v3_ordinal1(B_489) | ~v3_ordinal1(A_488))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.84/4.61  tff(c_46, plain, (![A_52]: (v3_ordinal1(k1_ordinal1(A_52)) | ~v3_ordinal1(A_52))), inference(cnfTransformation, [status(thm)], [f_103])).
% 11.84/4.61  tff(c_825, plain, (![B_138, A_139]: (r2_hidden(B_138, A_139) | B_138=A_139 | r2_hidden(A_139, B_138) | ~v3_ordinal1(B_138) | ~v3_ordinal1(A_139))), inference(cnfTransformation, [status(thm)], [f_99])).
% 11.84/4.61  tff(c_48, plain, (![B_54, A_53]: (~r1_tarski(B_54, A_53) | ~r2_hidden(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.84/4.61  tff(c_2618, plain, (![B_232, A_233]: (~r1_tarski(B_232, A_233) | r2_hidden(B_232, A_233) | B_232=A_233 | ~v3_ordinal1(B_232) | ~v3_ordinal1(A_233))), inference(resolution, [status(thm)], [c_825, c_48])).
% 11.84/4.61  tff(c_54, plain, (~r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.84/4.61  tff(c_88, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_54])).
% 11.84/4.61  tff(c_2628, plain, (~r1_tarski('#skF_1', '#skF_2') | '#skF_2'='#skF_1' | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_2618, c_88])).
% 11.84/4.61  tff(c_2636, plain, (~r1_tarski('#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_2628])).
% 11.84/4.61  tff(c_2637, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_2636])).
% 11.84/4.61  tff(c_60, plain, (r2_hidden('#skF_1', '#skF_2') | r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 11.84/4.61  tff(c_99, plain, (r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_88, c_60])).
% 11.84/4.61  tff(c_40, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | ~r1_ordinal1(A_46, B_47) | ~v3_ordinal1(B_47) | ~v3_ordinal1(A_46))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.84/4.61  tff(c_36, plain, (![A_45]: (k2_xboole_0(A_45, k1_tarski(A_45))=k1_ordinal1(A_45))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.84/4.61  tff(c_202, plain, (![A_83, C_84, B_85]: (r1_tarski(A_83, C_84) | ~r1_tarski(k2_xboole_0(A_83, B_85), C_84))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.84/4.61  tff(c_503, plain, (![A_115, C_116]: (r1_tarski(A_115, C_116) | ~r1_tarski(k1_ordinal1(A_115), C_116))), inference(superposition, [status(thm), theory('equality')], [c_36, c_202])).
% 11.84/4.61  tff(c_7765, plain, (![A_425, B_426]: (r1_tarski(A_425, B_426) | ~r1_ordinal1(k1_ordinal1(A_425), B_426) | ~v3_ordinal1(B_426) | ~v3_ordinal1(k1_ordinal1(A_425)))), inference(resolution, [status(thm)], [c_40, c_503])).
% 11.84/4.61  tff(c_7799, plain, (r1_tarski('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_99, c_7765])).
% 11.84/4.61  tff(c_7812, plain, (r1_tarski('#skF_1', '#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_7799])).
% 11.84/4.61  tff(c_7813, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_2637, c_7812])).
% 11.84/4.61  tff(c_7816, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_46, c_7813])).
% 11.84/4.61  tff(c_7820, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_7816])).
% 11.84/4.61  tff(c_7821, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_2636])).
% 11.84/4.61  tff(c_7823, plain, (r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7821, c_99])).
% 11.84/4.61  tff(c_455, plain, (![A_113, B_114]: (r1_tarski(A_113, B_114) | ~r1_ordinal1(A_113, B_114) | ~v3_ordinal1(B_114) | ~v3_ordinal1(A_113))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.84/4.61  tff(c_42, plain, (![A_48]: (k1_ordinal1(A_48)!=A_48)), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.84/4.61  tff(c_75, plain, (![A_62]: (k2_xboole_0(A_62, k1_tarski(A_62))=k1_ordinal1(A_62))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.84/4.61  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.84/4.61  tff(c_81, plain, (![A_62]: (r1_tarski(A_62, k1_ordinal1(A_62)))), inference(superposition, [status(thm), theory('equality')], [c_75, c_10])).
% 11.84/4.61  tff(c_163, plain, (![B_76, A_77]: (B_76=A_77 | ~r1_tarski(B_76, A_77) | ~r1_tarski(A_77, B_76))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.84/4.61  tff(c_169, plain, (![A_62]: (k1_ordinal1(A_62)=A_62 | ~r1_tarski(k1_ordinal1(A_62), A_62))), inference(resolution, [status(thm)], [c_81, c_163])).
% 11.84/4.61  tff(c_178, plain, (![A_62]: (~r1_tarski(k1_ordinal1(A_62), A_62))), inference(negUnitSimplification, [status(thm)], [c_42, c_169])).
% 11.84/4.61  tff(c_7995, plain, (![B_435]: (~r1_ordinal1(k1_ordinal1(B_435), B_435) | ~v3_ordinal1(B_435) | ~v3_ordinal1(k1_ordinal1(B_435)))), inference(resolution, [status(thm)], [c_455, c_178])).
% 11.84/4.61  tff(c_7998, plain, (~v3_ordinal1('#skF_1') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_7823, c_7995])).
% 11.84/4.61  tff(c_8009, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_7998])).
% 11.84/4.61  tff(c_8014, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_46, c_8009])).
% 11.84/4.61  tff(c_8018, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_8014])).
% 11.84/4.61  tff(c_8020, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_54])).
% 11.84/4.61  tff(c_8021, plain, (![B_436, A_437]: (~r1_tarski(B_436, A_437) | ~r2_hidden(A_437, B_436))), inference(cnfTransformation, [status(thm)], [f_108])).
% 11.84/4.61  tff(c_8025, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_8020, c_8021])).
% 11.84/4.61  tff(c_8538, plain, (~r1_ordinal1('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_8494, c_8025])).
% 11.84/4.61  tff(c_8552, plain, (~r1_ordinal1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_8538])).
% 11.84/4.61  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.84/4.61  tff(c_12, plain, (![A_8, C_10, B_9]: (r1_tarski(k2_xboole_0(A_8, C_10), B_9) | ~r1_tarski(C_10, B_9) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.84/4.61  tff(c_8141, plain, (![B_457, A_458]: (B_457=A_458 | ~r1_tarski(B_457, A_458) | ~r1_tarski(A_458, B_457))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.84/4.61  tff(c_9183, plain, (![A_551, B_552]: (k2_xboole_0(A_551, B_552)=A_551 | ~r1_tarski(k2_xboole_0(A_551, B_552), A_551))), inference(resolution, [status(thm)], [c_10, c_8141])).
% 11.84/4.61  tff(c_9187, plain, (![B_9, C_10]: (k2_xboole_0(B_9, C_10)=B_9 | ~r1_tarski(C_10, B_9) | ~r1_tarski(B_9, B_9))), inference(resolution, [status(thm)], [c_12, c_9183])).
% 11.84/4.61  tff(c_9204, plain, (![B_553, C_554]: (k2_xboole_0(B_553, C_554)=B_553 | ~r1_tarski(C_554, B_553))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_9187])).
% 11.84/4.61  tff(c_9300, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_9204])).
% 11.84/4.61  tff(c_34, plain, (![B_44, A_43]: (r1_ordinal1(B_44, A_43) | r1_ordinal1(A_43, B_44) | ~v3_ordinal1(B_44) | ~v3_ordinal1(A_43))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.84/4.61  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.84/4.61  tff(c_11618, plain, (![A_656, B_657, B_658]: (r1_tarski(A_656, B_657) | ~r1_ordinal1(k2_xboole_0(A_656, B_658), B_657) | ~v3_ordinal1(B_657) | ~v3_ordinal1(k2_xboole_0(A_656, B_658)))), inference(resolution, [status(thm)], [c_8494, c_8])).
% 11.84/4.61  tff(c_21703, plain, (![A_935, A_936, B_937]: (r1_tarski(A_935, A_936) | r1_ordinal1(A_936, k2_xboole_0(A_935, B_937)) | ~v3_ordinal1(k2_xboole_0(A_935, B_937)) | ~v3_ordinal1(A_936))), inference(resolution, [status(thm)], [c_34, c_11618])).
% 11.84/4.61  tff(c_21783, plain, (![B_2, A_936]: (r1_tarski(B_2, A_936) | r1_ordinal1(A_936, B_2) | ~v3_ordinal1(k2_xboole_0(B_2, B_2)) | ~v3_ordinal1(A_936))), inference(superposition, [status(thm), theory('equality')], [c_9300, c_21703])).
% 11.84/4.61  tff(c_21818, plain, (![B_2, A_936]: (r1_tarski(B_2, A_936) | r1_ordinal1(A_936, B_2) | ~v3_ordinal1(B_2) | ~v3_ordinal1(A_936))), inference(demodulation, [status(thm), theory('equality')], [c_9300, c_21783])).
% 11.84/4.61  tff(c_30, plain, (![A_39, B_40]: (r1_tarski(k1_tarski(A_39), B_40) | ~r2_hidden(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.84/4.61  tff(c_8566, plain, (![A_490, C_491, B_492]: (r1_tarski(k2_xboole_0(A_490, C_491), B_492) | ~r1_tarski(C_491, B_492) | ~r1_tarski(A_490, B_492))), inference(cnfTransformation, [status(thm)], [f_43])).
% 11.84/4.61  tff(c_9982, plain, (![A_576, B_577]: (r1_tarski(k1_ordinal1(A_576), B_577) | ~r1_tarski(k1_tarski(A_576), B_577) | ~r1_tarski(A_576, B_577))), inference(superposition, [status(thm), theory('equality')], [c_36, c_8566])).
% 11.84/4.61  tff(c_10063, plain, (![A_39, B_40]: (r1_tarski(k1_ordinal1(A_39), B_40) | ~r1_tarski(A_39, B_40) | ~r2_hidden(A_39, B_40))), inference(resolution, [status(thm)], [c_30, c_9982])).
% 11.84/4.61  tff(c_8469, plain, (![B_486, A_487]: (r1_ordinal1(B_486, A_487) | r1_ordinal1(A_487, B_486) | ~v3_ordinal1(B_486) | ~v3_ordinal1(A_487))), inference(cnfTransformation, [status(thm)], [f_71])).
% 11.84/4.61  tff(c_8019, plain, (~r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_54])).
% 11.84/4.61  tff(c_8472, plain, (r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1')) | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_8469, c_8019])).
% 11.84/4.61  tff(c_8478, plain, (r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_8472])).
% 11.84/4.61  tff(c_8482, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitLeft, [status(thm)], [c_8478])).
% 11.84/4.61  tff(c_8485, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_46, c_8482])).
% 11.84/4.61  tff(c_8489, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_8485])).
% 11.84/4.61  tff(c_8491, plain, (v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitRight, [status(thm)], [c_8478])).
% 11.84/4.61  tff(c_8490, plain, (r1_ordinal1('#skF_2', k1_ordinal1('#skF_1'))), inference(splitRight, [status(thm)], [c_8478])).
% 11.84/4.61  tff(c_18154, plain, (![B_859, A_860]: (k2_xboole_0(B_859, A_860)=B_859 | ~r1_ordinal1(A_860, B_859) | ~v3_ordinal1(B_859) | ~v3_ordinal1(A_860))), inference(resolution, [status(thm)], [c_40, c_9204])).
% 11.84/4.61  tff(c_18178, plain, (k2_xboole_0(k1_ordinal1('#skF_1'), '#skF_2')=k1_ordinal1('#skF_1') | ~v3_ordinal1(k1_ordinal1('#skF_1')) | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_8490, c_18154])).
% 11.84/4.61  tff(c_18201, plain, (k2_xboole_0(k1_ordinal1('#skF_1'), '#skF_2')=k1_ordinal1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_8491, c_18178])).
% 11.84/4.61  tff(c_38, plain, (![A_46, B_47]: (r1_ordinal1(A_46, B_47) | ~r1_tarski(A_46, B_47) | ~v3_ordinal1(B_47) | ~v3_ordinal1(A_46))), inference(cnfTransformation, [status(thm)], [f_81])).
% 11.84/4.61  tff(c_8585, plain, (![A_490, C_491, B_492]: (r1_ordinal1(k2_xboole_0(A_490, C_491), B_492) | ~v3_ordinal1(B_492) | ~v3_ordinal1(k2_xboole_0(A_490, C_491)) | ~r1_tarski(C_491, B_492) | ~r1_tarski(A_490, B_492))), inference(resolution, [status(thm)], [c_8566, c_38])).
% 11.84/4.61  tff(c_18406, plain, (![B_492]: (r1_ordinal1(k1_ordinal1('#skF_1'), B_492) | ~v3_ordinal1(B_492) | ~v3_ordinal1(k2_xboole_0(k1_ordinal1('#skF_1'), '#skF_2')) | ~r1_tarski('#skF_2', B_492) | ~r1_tarski(k1_ordinal1('#skF_1'), B_492))), inference(superposition, [status(thm), theory('equality')], [c_18201, c_8585])).
% 11.84/4.61  tff(c_18890, plain, (![B_868]: (r1_ordinal1(k1_ordinal1('#skF_1'), B_868) | ~v3_ordinal1(B_868) | ~r1_tarski('#skF_2', B_868) | ~r1_tarski(k1_ordinal1('#skF_1'), B_868))), inference(demodulation, [status(thm), theory('equality')], [c_8491, c_18201, c_18406])).
% 11.84/4.61  tff(c_26091, plain, (![B_1043]: (r1_ordinal1(k1_ordinal1('#skF_1'), B_1043) | ~v3_ordinal1(B_1043) | ~r1_tarski('#skF_2', B_1043) | ~r1_tarski('#skF_1', B_1043) | ~r2_hidden('#skF_1', B_1043))), inference(resolution, [status(thm)], [c_10063, c_18890])).
% 11.84/4.61  tff(c_26125, plain, (~v3_ordinal1('#skF_2') | ~r1_tarski('#skF_2', '#skF_2') | ~r1_tarski('#skF_1', '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_26091, c_8019])).
% 11.84/4.61  tff(c_26154, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8020, c_6, c_50, c_26125])).
% 11.84/4.61  tff(c_26157, plain, (r1_ordinal1('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_21818, c_26154])).
% 11.84/4.61  tff(c_26163, plain, (r1_ordinal1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_26157])).
% 11.84/4.61  tff(c_26165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8552, c_26163])).
% 11.84/4.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.84/4.61  
% 11.84/4.61  Inference rules
% 11.84/4.61  ----------------------
% 11.84/4.61  #Ref     : 0
% 11.84/4.61  #Sup     : 5547
% 11.84/4.61  #Fact    : 12
% 11.84/4.61  #Define  : 0
% 11.84/4.61  #Split   : 8
% 11.84/4.61  #Chain   : 0
% 11.84/4.61  #Close   : 0
% 11.84/4.61  
% 11.84/4.61  Ordering : KBO
% 11.84/4.61  
% 11.84/4.61  Simplification rules
% 11.84/4.61  ----------------------
% 11.84/4.61  #Subsume      : 844
% 11.84/4.61  #Demod        : 3478
% 11.84/4.61  #Tautology    : 2798
% 11.84/4.61  #SimpNegUnit  : 49
% 11.84/4.61  #BackRed      : 35
% 11.84/4.61  
% 11.84/4.61  #Partial instantiations: 0
% 11.84/4.61  #Strategies tried      : 1
% 11.84/4.61  
% 11.84/4.61  Timing (in seconds)
% 11.84/4.61  ----------------------
% 11.84/4.61  Preprocessing        : 0.35
% 11.84/4.61  Parsing              : 0.18
% 11.84/4.61  CNF conversion       : 0.02
% 11.84/4.61  Main loop            : 3.47
% 11.84/4.61  Inferencing          : 0.84
% 11.84/4.61  Reduction            : 1.54
% 11.84/4.61  Demodulation         : 1.22
% 11.84/4.61  BG Simplification    : 0.08
% 11.84/4.61  Subsumption          : 0.80
% 11.84/4.61  Abstraction          : 0.13
% 11.84/4.61  MUC search           : 0.00
% 11.84/4.61  Cooper               : 0.00
% 11.84/4.61  Total                : 3.86
% 11.84/4.61  Index Insertion      : 0.00
% 11.84/4.61  Index Deletion       : 0.00
% 11.84/4.61  Index Matching       : 0.00
% 11.84/4.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
