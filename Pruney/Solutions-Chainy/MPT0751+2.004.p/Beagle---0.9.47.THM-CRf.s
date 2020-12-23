%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:26 EST 2020

% Result     : Theorem 11.28s
% Output     : CNFRefutation 11.28s
% Verified   : 
% Statistics : Number of formulae       :   99 (1130 expanded)
%              Number of leaves         :   28 ( 391 expanded)
%              Depth                    :   16
%              Number of atoms          :  197 (2964 expanded)
%              Number of equality atoms :   17 ( 305 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v4_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v4_ordinal1,type,(
    v4_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_143,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ( ~ ( ~ v4_ordinal1(A)
              & ! [B] :
                  ( v3_ordinal1(B)
                 => A != k1_ordinal1(B) ) )
          & ~ ( ? [B] :
                  ( v3_ordinal1(B)
                  & A = k1_ordinal1(B) )
              & v4_ordinal1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v3_ordinal1(B)
     => ( r2_hidden(A,B)
       => v3_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_ordinal1)).

tff(f_64,axiom,(
    ! [A] :
    ? [B] :
    ! [C] :
      ( r2_hidden(C,B)
    <=> ( r2_hidden(C,A)
        & v3_ordinal1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s1_xboole_0__e3_53__ordinal1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_117,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v4_ordinal1(A)
      <=> ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(B,A)
             => r2_hidden(k1_ordinal1(B),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).

tff(f_82,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_91,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
          <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_100,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,k1_ordinal1(B))
          <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_122,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_62,plain,(
    v3_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_74,plain,
    ( ~ v4_ordinal1('#skF_5')
    | v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_80,plain,(
    ~ v4_ordinal1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_8753,plain,(
    ! [A_418,B_419] :
      ( r2_hidden('#skF_1'(A_418,B_419),A_418)
      | r1_tarski(A_418,B_419) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_36,plain,(
    ! [A_22,B_23] :
      ( v3_ordinal1(A_22)
      | ~ r2_hidden(A_22,B_23)
      | ~ v3_ordinal1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_8775,plain,(
    ! [A_418,B_419] :
      ( v3_ordinal1('#skF_1'(A_418,B_419))
      | ~ v3_ordinal1(A_418)
      | r1_tarski(A_418,B_419) ) ),
    inference(resolution,[status(thm)],[c_8753,c_36])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8790,plain,(
    ! [C_426,A_427] :
      ( r2_hidden(C_426,'#skF_2'(A_427))
      | ~ v3_ordinal1(C_426)
      | ~ r2_hidden(C_426,A_427) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14851,plain,(
    ! [A_690,A_691] :
      ( r1_tarski(A_690,'#skF_2'(A_691))
      | ~ v3_ordinal1('#skF_1'(A_690,'#skF_2'(A_691)))
      | ~ r2_hidden('#skF_1'(A_690,'#skF_2'(A_691)),A_691) ) ),
    inference(resolution,[status(thm)],[c_8790,c_4])).

tff(c_14903,plain,(
    ! [A_692] :
      ( ~ v3_ordinal1('#skF_1'(A_692,'#skF_2'(A_692)))
      | r1_tarski(A_692,'#skF_2'(A_692)) ) ),
    inference(resolution,[status(thm)],[c_6,c_14851])).

tff(c_14914,plain,(
    ! [A_693] :
      ( ~ v3_ordinal1(A_693)
      | r1_tarski(A_693,'#skF_2'(A_693)) ) ),
    inference(resolution,[status(thm)],[c_8775,c_14903])).

tff(c_26,plain,(
    ! [C_18,A_13] :
      ( r2_hidden(C_18,A_13)
      | ~ r2_hidden(C_18,'#skF_2'(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10175,plain,(
    ! [A_521,B_522] :
      ( r2_hidden('#skF_1'('#skF_2'(A_521),B_522),A_521)
      | r1_tarski('#skF_2'(A_521),B_522) ) ),
    inference(resolution,[status(thm)],[c_8753,c_26])).

tff(c_10216,plain,(
    ! [A_523] : r1_tarski('#skF_2'(A_523),A_523) ),
    inference(resolution,[status(thm)],[c_10175,c_4])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10227,plain,(
    ! [A_523] :
      ( '#skF_2'(A_523) = A_523
      | ~ r1_tarski(A_523,'#skF_2'(A_523)) ) ),
    inference(resolution,[status(thm)],[c_10216,c_8])).

tff(c_15022,plain,(
    ! [A_694] :
      ( '#skF_2'(A_694) = A_694
      | ~ v3_ordinal1(A_694) ) ),
    inference(resolution,[status(thm)],[c_14914,c_10227])).

tff(c_15050,plain,(
    '#skF_2'('#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_62,c_15022])).

tff(c_8726,plain,(
    ! [A_414] :
      ( r2_hidden('#skF_4'(A_414),A_414)
      | v4_ordinal1(A_414)
      | ~ v3_ordinal1(A_414) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_8741,plain,(
    ! [A_13] :
      ( r2_hidden('#skF_4'('#skF_2'(A_13)),A_13)
      | v4_ordinal1('#skF_2'(A_13))
      | ~ v3_ordinal1('#skF_2'(A_13)) ) ),
    inference(resolution,[status(thm)],[c_8726,c_26])).

tff(c_15110,plain,
    ( r2_hidden('#skF_4'('#skF_5'),'#skF_5')
    | v4_ordinal1('#skF_2'('#skF_5'))
    | ~ v3_ordinal1('#skF_2'('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_15050,c_8741])).

tff(c_15236,plain,
    ( r2_hidden('#skF_4'('#skF_5'),'#skF_5')
    | v4_ordinal1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_15050,c_15050,c_15110])).

tff(c_15237,plain,(
    r2_hidden('#skF_4'('#skF_5'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_15236])).

tff(c_15554,plain,
    ( v3_ordinal1('#skF_4'('#skF_5'))
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_15237,c_36])).

tff(c_15564,plain,(
    v3_ordinal1('#skF_4'('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_15554])).

tff(c_38,plain,(
    ! [A_24] :
      ( v3_ordinal1(k1_ordinal1(A_24))
      | ~ v3_ordinal1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_42,plain,(
    ! [A_25,B_27] :
      ( r1_ordinal1(k1_ordinal1(A_25),B_27)
      | ~ r2_hidden(A_25,B_27)
      | ~ v3_ordinal1(B_27)
      | ~ v3_ordinal1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_64,plain,(
    ! [B_41] :
      ( k1_ordinal1(B_41) != '#skF_5'
      | ~ v3_ordinal1(B_41)
      | v4_ordinal1('#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_8637,plain,(
    ! [B_41] :
      ( k1_ordinal1(B_41) != '#skF_5'
      | ~ v3_ordinal1(B_41) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_64])).

tff(c_15639,plain,(
    k1_ordinal1('#skF_4'('#skF_5')) != '#skF_5' ),
    inference(resolution,[status(thm)],[c_15564,c_8637])).

tff(c_9560,plain,(
    ! [A_501,B_502] :
      ( r2_hidden(A_501,k1_ordinal1(B_502))
      | ~ r1_ordinal1(A_501,B_502)
      | ~ v3_ordinal1(B_502)
      | ~ v3_ordinal1(A_501) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_30,plain,(
    ! [B_21,A_20] :
      ( B_21 = A_20
      | r2_hidden(A_20,B_21)
      | ~ r2_hidden(A_20,k1_ordinal1(B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_9851,plain,(
    ! [B_502,A_501] :
      ( B_502 = A_501
      | r2_hidden(A_501,B_502)
      | ~ r1_ordinal1(A_501,B_502)
      | ~ v3_ordinal1(B_502)
      | ~ v3_ordinal1(A_501) ) ),
    inference(resolution,[status(thm)],[c_9560,c_30])).

tff(c_22,plain,(
    ! [C_18,A_13] :
      ( r2_hidden(C_18,'#skF_2'(A_13))
      | ~ v3_ordinal1(C_18)
      | ~ r2_hidden(C_18,A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8981,plain,(
    ! [A_440] :
      ( ~ r2_hidden(k1_ordinal1('#skF_4'(A_440)),A_440)
      | v4_ordinal1(A_440)
      | ~ v3_ordinal1(A_440) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_17265,plain,(
    ! [A_725] :
      ( v4_ordinal1('#skF_2'(A_725))
      | ~ v3_ordinal1('#skF_2'(A_725))
      | ~ v3_ordinal1(k1_ordinal1('#skF_4'('#skF_2'(A_725))))
      | ~ r2_hidden(k1_ordinal1('#skF_4'('#skF_2'(A_725))),A_725) ) ),
    inference(resolution,[status(thm)],[c_22,c_8981])).

tff(c_17287,plain,
    ( v4_ordinal1('#skF_2'('#skF_5'))
    | ~ v3_ordinal1('#skF_2'('#skF_5'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_4'('#skF_2'('#skF_5'))))
    | ~ r2_hidden(k1_ordinal1('#skF_4'('#skF_5')),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_15050,c_17265])).

tff(c_17329,plain,
    ( v4_ordinal1('#skF_5')
    | ~ v3_ordinal1(k1_ordinal1('#skF_4'('#skF_5')))
    | ~ r2_hidden(k1_ordinal1('#skF_4'('#skF_5')),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15050,c_62,c_15050,c_15050,c_17287])).

tff(c_17330,plain,
    ( ~ v3_ordinal1(k1_ordinal1('#skF_4'('#skF_5')))
    | ~ r2_hidden(k1_ordinal1('#skF_4'('#skF_5')),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_17329])).

tff(c_17716,plain,(
    ~ r2_hidden(k1_ordinal1('#skF_4'('#skF_5')),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_17330])).

tff(c_17722,plain,
    ( k1_ordinal1('#skF_4'('#skF_5')) = '#skF_5'
    | ~ r1_ordinal1(k1_ordinal1('#skF_4'('#skF_5')),'#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1(k1_ordinal1('#skF_4'('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_9851,c_17716])).

tff(c_17731,plain,
    ( k1_ordinal1('#skF_4'('#skF_5')) = '#skF_5'
    | ~ r1_ordinal1(k1_ordinal1('#skF_4'('#skF_5')),'#skF_5')
    | ~ v3_ordinal1(k1_ordinal1('#skF_4'('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_17722])).

tff(c_17732,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_4'('#skF_5')),'#skF_5')
    | ~ v3_ordinal1(k1_ordinal1('#skF_4'('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_15639,c_17731])).

tff(c_18078,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_4'('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_17732])).

tff(c_18081,plain,(
    ~ v3_ordinal1('#skF_4'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_38,c_18078])).

tff(c_18085,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15564,c_18081])).

tff(c_18086,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_4'('#skF_5')),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_17732])).

tff(c_18110,plain,
    ( ~ r2_hidden('#skF_4'('#skF_5'),'#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_4'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_42,c_18086])).

tff(c_18120,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15564,c_62,c_15237,c_18110])).

tff(c_18121,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_4'('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_17330])).

tff(c_18125,plain,(
    ~ v3_ordinal1('#skF_4'('#skF_5')) ),
    inference(resolution,[status(thm)],[c_38,c_18121])).

tff(c_18129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15564,c_18125])).

tff(c_18131,plain,(
    v4_ordinal1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_70,plain,
    ( ~ v4_ordinal1('#skF_5')
    | k1_ordinal1('#skF_6') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_18134,plain,(
    k1_ordinal1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18131,c_70])).

tff(c_32,plain,(
    ! [B_21] : r2_hidden(B_21,k1_ordinal1(B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_18138,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_18134,c_32])).

tff(c_18130,plain,(
    v3_ordinal1('#skF_6') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_20108,plain,(
    ! [B_854,A_855] :
      ( r2_hidden(k1_ordinal1(B_854),A_855)
      | ~ r2_hidden(B_854,A_855)
      | ~ v3_ordinal1(B_854)
      | ~ v4_ordinal1(A_855)
      | ~ v3_ordinal1(A_855) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_20193,plain,(
    ! [A_855] :
      ( r2_hidden('#skF_5',A_855)
      | ~ r2_hidden('#skF_6',A_855)
      | ~ v3_ordinal1('#skF_6')
      | ~ v4_ordinal1(A_855)
      | ~ v3_ordinal1(A_855) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18134,c_20108])).

tff(c_20712,plain,(
    ! [A_871] :
      ( r2_hidden('#skF_5',A_871)
      | ~ r2_hidden('#skF_6',A_871)
      | ~ v4_ordinal1(A_871)
      | ~ v3_ordinal1(A_871) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18130,c_20193])).

tff(c_18222,plain,(
    ! [A_766,B_767] :
      ( r2_hidden('#skF_1'(A_766,B_767),A_766)
      | r1_tarski(A_766,B_767) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20541,plain,(
    ! [A_866,B_867] :
      ( r2_hidden('#skF_1'('#skF_2'(A_866),B_867),A_866)
      | r1_tarski('#skF_2'(A_866),B_867) ) ),
    inference(resolution,[status(thm)],[c_18222,c_26])).

tff(c_20617,plain,(
    ! [A_868] : r1_tarski('#skF_2'(A_868),A_868) ),
    inference(resolution,[status(thm)],[c_20541,c_4])).

tff(c_18619,plain,(
    ! [C_807,A_808] :
      ( r2_hidden(C_807,'#skF_2'(A_808))
      | ~ v3_ordinal1(C_807)
      | ~ r2_hidden(C_807,A_808) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_60,plain,(
    ! [B_38,A_37] :
      ( ~ r1_tarski(B_38,A_37)
      | ~ r2_hidden(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_18699,plain,(
    ! [A_808,C_807] :
      ( ~ r1_tarski('#skF_2'(A_808),C_807)
      | ~ v3_ordinal1(C_807)
      | ~ r2_hidden(C_807,A_808) ) ),
    inference(resolution,[status(thm)],[c_18619,c_60])).

tff(c_20629,plain,(
    ! [A_868] :
      ( ~ v3_ordinal1(A_868)
      | ~ r2_hidden(A_868,A_868) ) ),
    inference(resolution,[status(thm)],[c_20617,c_18699])).

tff(c_20716,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | ~ v4_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_20712,c_20629])).

tff(c_20774,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_18131,c_18138,c_20716])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:59:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.28/3.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.28/3.82  
% 11.28/3.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.28/3.82  %$ r2_hidden > r1_tarski > r1_ordinal1 > v4_ordinal1 > v3_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_1
% 11.28/3.82  
% 11.28/3.82  %Foreground sorts:
% 11.28/3.82  
% 11.28/3.82  
% 11.28/3.82  %Background operators:
% 11.28/3.82  
% 11.28/3.82  
% 11.28/3.82  %Foreground operators:
% 11.28/3.82  tff('#skF_2', type, '#skF_2': $i > $i).
% 11.28/3.82  tff('#skF_4', type, '#skF_4': $i > $i).
% 11.28/3.82  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 11.28/3.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.28/3.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.28/3.82  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.28/3.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.28/3.82  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 11.28/3.82  tff('#skF_5', type, '#skF_5': $i).
% 11.28/3.82  tff('#skF_6', type, '#skF_6': $i).
% 11.28/3.82  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 11.28/3.82  tff(v4_ordinal1, type, v4_ordinal1: $i > $o).
% 11.28/3.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.28/3.82  tff('#skF_3', type, '#skF_3': $i > $i).
% 11.28/3.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.28/3.82  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.28/3.82  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.28/3.82  
% 11.28/3.84  tff(f_143, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (~(~v4_ordinal1(A) & (![B]: (v3_ordinal1(B) => ~(A = k1_ordinal1(B))))) & ~((?[B]: (v3_ordinal1(B) & (A = k1_ordinal1(B)))) & v4_ordinal1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_ordinal1)).
% 11.28/3.84  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 11.28/3.84  tff(f_78, axiom, (![A, B]: (v3_ordinal1(B) => (r2_hidden(A, B) => v3_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_ordinal1)).
% 11.28/3.84  tff(f_64, axiom, (![A]: (?[B]: (![C]: (r2_hidden(C, B) <=> (r2_hidden(C, A) & v3_ordinal1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s1_xboole_0__e3_53__ordinal1)).
% 11.28/3.84  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.28/3.84  tff(f_117, axiom, (![A]: (v3_ordinal1(A) => (v4_ordinal1(A) <=> (![B]: (v3_ordinal1(B) => (r2_hidden(B, A) => r2_hidden(k1_ordinal1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_ordinal1)).
% 11.28/3.84  tff(f_82, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 11.28/3.84  tff(f_91, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_ordinal1)).
% 11.28/3.84  tff(f_100, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 11.28/3.84  tff(f_72, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_ordinal1)).
% 11.28/3.84  tff(f_122, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 11.28/3.84  tff(c_62, plain, (v3_ordinal1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_143])).
% 11.28/3.84  tff(c_74, plain, (~v4_ordinal1('#skF_5') | v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_143])).
% 11.28/3.84  tff(c_80, plain, (~v4_ordinal1('#skF_5')), inference(splitLeft, [status(thm)], [c_74])).
% 11.28/3.84  tff(c_8753, plain, (![A_418, B_419]: (r2_hidden('#skF_1'(A_418, B_419), A_418) | r1_tarski(A_418, B_419))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.28/3.84  tff(c_36, plain, (![A_22, B_23]: (v3_ordinal1(A_22) | ~r2_hidden(A_22, B_23) | ~v3_ordinal1(B_23))), inference(cnfTransformation, [status(thm)], [f_78])).
% 11.28/3.84  tff(c_8775, plain, (![A_418, B_419]: (v3_ordinal1('#skF_1'(A_418, B_419)) | ~v3_ordinal1(A_418) | r1_tarski(A_418, B_419))), inference(resolution, [status(thm)], [c_8753, c_36])).
% 11.28/3.84  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.28/3.84  tff(c_8790, plain, (![C_426, A_427]: (r2_hidden(C_426, '#skF_2'(A_427)) | ~v3_ordinal1(C_426) | ~r2_hidden(C_426, A_427))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.28/3.84  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.28/3.84  tff(c_14851, plain, (![A_690, A_691]: (r1_tarski(A_690, '#skF_2'(A_691)) | ~v3_ordinal1('#skF_1'(A_690, '#skF_2'(A_691))) | ~r2_hidden('#skF_1'(A_690, '#skF_2'(A_691)), A_691))), inference(resolution, [status(thm)], [c_8790, c_4])).
% 11.28/3.84  tff(c_14903, plain, (![A_692]: (~v3_ordinal1('#skF_1'(A_692, '#skF_2'(A_692))) | r1_tarski(A_692, '#skF_2'(A_692)))), inference(resolution, [status(thm)], [c_6, c_14851])).
% 11.28/3.84  tff(c_14914, plain, (![A_693]: (~v3_ordinal1(A_693) | r1_tarski(A_693, '#skF_2'(A_693)))), inference(resolution, [status(thm)], [c_8775, c_14903])).
% 11.28/3.84  tff(c_26, plain, (![C_18, A_13]: (r2_hidden(C_18, A_13) | ~r2_hidden(C_18, '#skF_2'(A_13)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.28/3.84  tff(c_10175, plain, (![A_521, B_522]: (r2_hidden('#skF_1'('#skF_2'(A_521), B_522), A_521) | r1_tarski('#skF_2'(A_521), B_522))), inference(resolution, [status(thm)], [c_8753, c_26])).
% 11.28/3.84  tff(c_10216, plain, (![A_523]: (r1_tarski('#skF_2'(A_523), A_523))), inference(resolution, [status(thm)], [c_10175, c_4])).
% 11.28/3.84  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 11.28/3.84  tff(c_10227, plain, (![A_523]: ('#skF_2'(A_523)=A_523 | ~r1_tarski(A_523, '#skF_2'(A_523)))), inference(resolution, [status(thm)], [c_10216, c_8])).
% 11.28/3.84  tff(c_15022, plain, (![A_694]: ('#skF_2'(A_694)=A_694 | ~v3_ordinal1(A_694))), inference(resolution, [status(thm)], [c_14914, c_10227])).
% 11.28/3.84  tff(c_15050, plain, ('#skF_2'('#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_62, c_15022])).
% 11.28/3.84  tff(c_8726, plain, (![A_414]: (r2_hidden('#skF_4'(A_414), A_414) | v4_ordinal1(A_414) | ~v3_ordinal1(A_414))), inference(cnfTransformation, [status(thm)], [f_117])).
% 11.28/3.84  tff(c_8741, plain, (![A_13]: (r2_hidden('#skF_4'('#skF_2'(A_13)), A_13) | v4_ordinal1('#skF_2'(A_13)) | ~v3_ordinal1('#skF_2'(A_13)))), inference(resolution, [status(thm)], [c_8726, c_26])).
% 11.28/3.84  tff(c_15110, plain, (r2_hidden('#skF_4'('#skF_5'), '#skF_5') | v4_ordinal1('#skF_2'('#skF_5')) | ~v3_ordinal1('#skF_2'('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_15050, c_8741])).
% 11.28/3.84  tff(c_15236, plain, (r2_hidden('#skF_4'('#skF_5'), '#skF_5') | v4_ordinal1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_15050, c_15050, c_15110])).
% 11.28/3.84  tff(c_15237, plain, (r2_hidden('#skF_4'('#skF_5'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_80, c_15236])).
% 11.28/3.84  tff(c_15554, plain, (v3_ordinal1('#skF_4'('#skF_5')) | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_15237, c_36])).
% 11.28/3.84  tff(c_15564, plain, (v3_ordinal1('#skF_4'('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_15554])).
% 11.28/3.84  tff(c_38, plain, (![A_24]: (v3_ordinal1(k1_ordinal1(A_24)) | ~v3_ordinal1(A_24))), inference(cnfTransformation, [status(thm)], [f_82])).
% 11.28/3.84  tff(c_42, plain, (![A_25, B_27]: (r1_ordinal1(k1_ordinal1(A_25), B_27) | ~r2_hidden(A_25, B_27) | ~v3_ordinal1(B_27) | ~v3_ordinal1(A_25))), inference(cnfTransformation, [status(thm)], [f_91])).
% 11.28/3.84  tff(c_64, plain, (![B_41]: (k1_ordinal1(B_41)!='#skF_5' | ~v3_ordinal1(B_41) | v4_ordinal1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 11.28/3.84  tff(c_8637, plain, (![B_41]: (k1_ordinal1(B_41)!='#skF_5' | ~v3_ordinal1(B_41))), inference(negUnitSimplification, [status(thm)], [c_80, c_64])).
% 11.28/3.84  tff(c_15639, plain, (k1_ordinal1('#skF_4'('#skF_5'))!='#skF_5'), inference(resolution, [status(thm)], [c_15564, c_8637])).
% 11.28/3.84  tff(c_9560, plain, (![A_501, B_502]: (r2_hidden(A_501, k1_ordinal1(B_502)) | ~r1_ordinal1(A_501, B_502) | ~v3_ordinal1(B_502) | ~v3_ordinal1(A_501))), inference(cnfTransformation, [status(thm)], [f_100])).
% 11.28/3.84  tff(c_30, plain, (![B_21, A_20]: (B_21=A_20 | r2_hidden(A_20, B_21) | ~r2_hidden(A_20, k1_ordinal1(B_21)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.28/3.84  tff(c_9851, plain, (![B_502, A_501]: (B_502=A_501 | r2_hidden(A_501, B_502) | ~r1_ordinal1(A_501, B_502) | ~v3_ordinal1(B_502) | ~v3_ordinal1(A_501))), inference(resolution, [status(thm)], [c_9560, c_30])).
% 11.28/3.84  tff(c_22, plain, (![C_18, A_13]: (r2_hidden(C_18, '#skF_2'(A_13)) | ~v3_ordinal1(C_18) | ~r2_hidden(C_18, A_13))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.28/3.84  tff(c_8981, plain, (![A_440]: (~r2_hidden(k1_ordinal1('#skF_4'(A_440)), A_440) | v4_ordinal1(A_440) | ~v3_ordinal1(A_440))), inference(cnfTransformation, [status(thm)], [f_117])).
% 11.28/3.84  tff(c_17265, plain, (![A_725]: (v4_ordinal1('#skF_2'(A_725)) | ~v3_ordinal1('#skF_2'(A_725)) | ~v3_ordinal1(k1_ordinal1('#skF_4'('#skF_2'(A_725)))) | ~r2_hidden(k1_ordinal1('#skF_4'('#skF_2'(A_725))), A_725))), inference(resolution, [status(thm)], [c_22, c_8981])).
% 11.28/3.84  tff(c_17287, plain, (v4_ordinal1('#skF_2'('#skF_5')) | ~v3_ordinal1('#skF_2'('#skF_5')) | ~v3_ordinal1(k1_ordinal1('#skF_4'('#skF_2'('#skF_5')))) | ~r2_hidden(k1_ordinal1('#skF_4'('#skF_5')), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_15050, c_17265])).
% 11.28/3.84  tff(c_17329, plain, (v4_ordinal1('#skF_5') | ~v3_ordinal1(k1_ordinal1('#skF_4'('#skF_5'))) | ~r2_hidden(k1_ordinal1('#skF_4'('#skF_5')), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_15050, c_62, c_15050, c_15050, c_17287])).
% 11.28/3.84  tff(c_17330, plain, (~v3_ordinal1(k1_ordinal1('#skF_4'('#skF_5'))) | ~r2_hidden(k1_ordinal1('#skF_4'('#skF_5')), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_80, c_17329])).
% 11.28/3.84  tff(c_17716, plain, (~r2_hidden(k1_ordinal1('#skF_4'('#skF_5')), '#skF_5')), inference(splitLeft, [status(thm)], [c_17330])).
% 11.28/3.84  tff(c_17722, plain, (k1_ordinal1('#skF_4'('#skF_5'))='#skF_5' | ~r1_ordinal1(k1_ordinal1('#skF_4'('#skF_5')), '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1(k1_ordinal1('#skF_4'('#skF_5')))), inference(resolution, [status(thm)], [c_9851, c_17716])).
% 11.28/3.84  tff(c_17731, plain, (k1_ordinal1('#skF_4'('#skF_5'))='#skF_5' | ~r1_ordinal1(k1_ordinal1('#skF_4'('#skF_5')), '#skF_5') | ~v3_ordinal1(k1_ordinal1('#skF_4'('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_17722])).
% 11.28/3.84  tff(c_17732, plain, (~r1_ordinal1(k1_ordinal1('#skF_4'('#skF_5')), '#skF_5') | ~v3_ordinal1(k1_ordinal1('#skF_4'('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_15639, c_17731])).
% 11.28/3.84  tff(c_18078, plain, (~v3_ordinal1(k1_ordinal1('#skF_4'('#skF_5')))), inference(splitLeft, [status(thm)], [c_17732])).
% 11.28/3.84  tff(c_18081, plain, (~v3_ordinal1('#skF_4'('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_18078])).
% 11.28/3.84  tff(c_18085, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15564, c_18081])).
% 11.28/3.84  tff(c_18086, plain, (~r1_ordinal1(k1_ordinal1('#skF_4'('#skF_5')), '#skF_5')), inference(splitRight, [status(thm)], [c_17732])).
% 11.28/3.84  tff(c_18110, plain, (~r2_hidden('#skF_4'('#skF_5'), '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_4'('#skF_5'))), inference(resolution, [status(thm)], [c_42, c_18086])).
% 11.28/3.84  tff(c_18120, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15564, c_62, c_15237, c_18110])).
% 11.28/3.84  tff(c_18121, plain, (~v3_ordinal1(k1_ordinal1('#skF_4'('#skF_5')))), inference(splitRight, [status(thm)], [c_17330])).
% 11.28/3.84  tff(c_18125, plain, (~v3_ordinal1('#skF_4'('#skF_5'))), inference(resolution, [status(thm)], [c_38, c_18121])).
% 11.28/3.84  tff(c_18129, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15564, c_18125])).
% 11.28/3.84  tff(c_18131, plain, (v4_ordinal1('#skF_5')), inference(splitRight, [status(thm)], [c_74])).
% 11.28/3.84  tff(c_70, plain, (~v4_ordinal1('#skF_5') | k1_ordinal1('#skF_6')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_143])).
% 11.28/3.84  tff(c_18134, plain, (k1_ordinal1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_18131, c_70])).
% 11.28/3.84  tff(c_32, plain, (![B_21]: (r2_hidden(B_21, k1_ordinal1(B_21)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.28/3.84  tff(c_18138, plain, (r2_hidden('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_18134, c_32])).
% 11.28/3.84  tff(c_18130, plain, (v3_ordinal1('#skF_6')), inference(splitRight, [status(thm)], [c_74])).
% 11.28/3.84  tff(c_20108, plain, (![B_854, A_855]: (r2_hidden(k1_ordinal1(B_854), A_855) | ~r2_hidden(B_854, A_855) | ~v3_ordinal1(B_854) | ~v4_ordinal1(A_855) | ~v3_ordinal1(A_855))), inference(cnfTransformation, [status(thm)], [f_117])).
% 11.28/3.84  tff(c_20193, plain, (![A_855]: (r2_hidden('#skF_5', A_855) | ~r2_hidden('#skF_6', A_855) | ~v3_ordinal1('#skF_6') | ~v4_ordinal1(A_855) | ~v3_ordinal1(A_855))), inference(superposition, [status(thm), theory('equality')], [c_18134, c_20108])).
% 11.28/3.84  tff(c_20712, plain, (![A_871]: (r2_hidden('#skF_5', A_871) | ~r2_hidden('#skF_6', A_871) | ~v4_ordinal1(A_871) | ~v3_ordinal1(A_871))), inference(demodulation, [status(thm), theory('equality')], [c_18130, c_20193])).
% 11.28/3.84  tff(c_18222, plain, (![A_766, B_767]: (r2_hidden('#skF_1'(A_766, B_767), A_766) | r1_tarski(A_766, B_767))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.28/3.84  tff(c_20541, plain, (![A_866, B_867]: (r2_hidden('#skF_1'('#skF_2'(A_866), B_867), A_866) | r1_tarski('#skF_2'(A_866), B_867))), inference(resolution, [status(thm)], [c_18222, c_26])).
% 11.28/3.84  tff(c_20617, plain, (![A_868]: (r1_tarski('#skF_2'(A_868), A_868))), inference(resolution, [status(thm)], [c_20541, c_4])).
% 11.28/3.84  tff(c_18619, plain, (![C_807, A_808]: (r2_hidden(C_807, '#skF_2'(A_808)) | ~v3_ordinal1(C_807) | ~r2_hidden(C_807, A_808))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.28/3.84  tff(c_60, plain, (![B_38, A_37]: (~r1_tarski(B_38, A_37) | ~r2_hidden(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_122])).
% 11.28/3.84  tff(c_18699, plain, (![A_808, C_807]: (~r1_tarski('#skF_2'(A_808), C_807) | ~v3_ordinal1(C_807) | ~r2_hidden(C_807, A_808))), inference(resolution, [status(thm)], [c_18619, c_60])).
% 11.28/3.84  tff(c_20629, plain, (![A_868]: (~v3_ordinal1(A_868) | ~r2_hidden(A_868, A_868))), inference(resolution, [status(thm)], [c_20617, c_18699])).
% 11.28/3.84  tff(c_20716, plain, (~r2_hidden('#skF_6', '#skF_5') | ~v4_ordinal1('#skF_5') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_20712, c_20629])).
% 11.28/3.84  tff(c_20774, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_18131, c_18138, c_20716])).
% 11.28/3.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.28/3.84  
% 11.28/3.84  Inference rules
% 11.28/3.84  ----------------------
% 11.28/3.84  #Ref     : 0
% 11.28/3.84  #Sup     : 3978
% 11.28/3.84  #Fact    : 6
% 11.28/3.84  #Define  : 0
% 11.28/3.84  #Split   : 13
% 11.28/3.84  #Chain   : 0
% 11.28/3.84  #Close   : 0
% 11.28/3.84  
% 11.28/3.84  Ordering : KBO
% 11.28/3.84  
% 11.28/3.84  Simplification rules
% 11.28/3.84  ----------------------
% 11.28/3.84  #Subsume      : 1267
% 11.28/3.84  #Demod        : 2029
% 11.28/3.84  #Tautology    : 385
% 11.28/3.84  #SimpNegUnit  : 44
% 11.28/3.84  #BackRed      : 99
% 11.28/3.84  
% 11.28/3.84  #Partial instantiations: 0
% 11.28/3.84  #Strategies tried      : 1
% 11.28/3.84  
% 11.28/3.84  Timing (in seconds)
% 11.28/3.84  ----------------------
% 11.28/3.84  Preprocessing        : 0.32
% 11.28/3.84  Parsing              : 0.17
% 11.28/3.85  CNF conversion       : 0.03
% 11.28/3.85  Main loop            : 2.76
% 11.28/3.85  Inferencing          : 0.73
% 11.28/3.85  Reduction            : 0.85
% 11.28/3.85  Demodulation         : 0.53
% 11.28/3.85  BG Simplification    : 0.08
% 11.28/3.85  Subsumption          : 0.88
% 11.28/3.85  Abstraction          : 0.10
% 11.28/3.85  MUC search           : 0.00
% 11.28/3.85  Cooper               : 0.00
% 11.28/3.85  Total                : 3.12
% 11.28/3.85  Index Insertion      : 0.00
% 11.28/3.85  Index Deletion       : 0.00
% 11.28/3.85  Index Matching       : 0.00
% 11.28/3.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
