%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:17 EST 2020

% Result     : Theorem 40.68s
% Output     : CNFRefutation 40.77s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 315 expanded)
%              Number of leaves         :   23 ( 113 expanded)
%              Depth                    :   11
%              Number of atoms          :  146 ( 647 expanded)
%              Number of equality atoms :   53 ( 250 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k4_xboole_0(k2_tarski(A,B),C) = k1_xboole_0
      <=> ( r2_hidden(A,C)
          & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_50,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | ~ r2_hidden('#skF_9','#skF_10')
    | ~ r2_hidden('#skF_8','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_121,plain,(
    ~ r2_hidden('#skF_8','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_30,plain,(
    ! [D_15,B_11] : r2_hidden(D_15,k2_tarski(D_15,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_28,plain,(
    ! [D_15,A_10] : r2_hidden(D_15,k2_tarski(A_10,D_15)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_24,plain,(
    ! [A_9] : k4_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_81,plain,(
    ! [D_29,B_30,A_31] :
      ( ~ r2_hidden(D_29,B_30)
      | ~ r2_hidden(D_29,k4_xboole_0(A_31,B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_85,plain,(
    ! [D_32,A_33] :
      ( ~ r2_hidden(D_32,A_33)
      | ~ r2_hidden(D_32,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_81])).

tff(c_90,plain,(
    ! [D_15] : ~ r2_hidden(D_15,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_28,c_85])).

tff(c_56,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | k4_xboole_0(k2_tarski('#skF_8','#skF_9'),'#skF_10') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_93,plain,(
    k4_xboole_0(k2_tarski('#skF_8','#skF_9'),'#skF_10') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_122,plain,(
    ! [D_41,A_42,B_43] :
      ( r2_hidden(D_41,k4_xboole_0(A_42,B_43))
      | r2_hidden(D_41,B_43)
      | ~ r2_hidden(D_41,A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_131,plain,(
    ! [D_41] :
      ( r2_hidden(D_41,k1_xboole_0)
      | r2_hidden(D_41,'#skF_10')
      | ~ r2_hidden(D_41,k2_tarski('#skF_8','#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_122])).

tff(c_139,plain,(
    ! [D_44] :
      ( r2_hidden(D_44,'#skF_10')
      | ~ r2_hidden(D_44,k2_tarski('#skF_8','#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_131])).

tff(c_147,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(resolution,[status(thm)],[c_30,c_139])).

tff(c_152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_147])).

tff(c_154,plain,(
    r2_hidden('#skF_8','#skF_10') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_153,plain,
    ( ~ r2_hidden('#skF_9','#skF_10')
    | r2_hidden('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_155,plain,(
    ~ r2_hidden('#skF_9','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_158,plain,(
    ! [D_45,A_46,B_47] :
      ( r2_hidden(D_45,k4_xboole_0(A_46,B_47))
      | r2_hidden(D_45,B_47)
      | ~ r2_hidden(D_45,A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_167,plain,(
    ! [D_45] :
      ( r2_hidden(D_45,k1_xboole_0)
      | r2_hidden(D_45,'#skF_10')
      | ~ r2_hidden(D_45,k2_tarski('#skF_8','#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_158])).

tff(c_175,plain,(
    ! [D_48] :
      ( r2_hidden(D_48,'#skF_10')
      | ~ r2_hidden(D_48,k2_tarski('#skF_8','#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_167])).

tff(c_179,plain,(
    r2_hidden('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_28,c_175])).

tff(c_187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_179])).

tff(c_189,plain,(
    r2_hidden('#skF_9','#skF_10') ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_46,plain,
    ( k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') != k1_xboole_0
    | ~ r2_hidden('#skF_9','#skF_10')
    | ~ r2_hidden('#skF_8','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_224,plain,(
    k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_189,c_46])).

tff(c_48,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | ~ r2_hidden('#skF_9','#skF_10')
    | ~ r2_hidden('#skF_8','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_191,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_189,c_48])).

tff(c_188,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_275,plain,(
    ! [A_70,B_71,C_72] :
      ( r2_hidden('#skF_1'(A_70,B_71,C_72),A_70)
      | r2_hidden('#skF_2'(A_70,B_71,C_72),C_72)
      | k4_xboole_0(A_70,B_71) = C_72 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4329,plain,(
    ! [A_209,B_210,A_211,B_212] :
      ( r2_hidden('#skF_2'(A_209,B_210,k4_xboole_0(A_211,B_212)),A_211)
      | r2_hidden('#skF_1'(A_209,B_210,k4_xboole_0(A_211,B_212)),A_209)
      | k4_xboole_0(A_211,B_212) = k4_xboole_0(A_209,B_210) ) ),
    inference(resolution,[status(thm)],[c_275,c_6])).

tff(c_4508,plain,(
    ! [A_209,B_210,A_9] :
      ( r2_hidden('#skF_2'(A_209,B_210,k4_xboole_0(k1_xboole_0,A_9)),k1_xboole_0)
      | r2_hidden('#skF_1'(A_209,B_210,k1_xboole_0),A_209)
      | k4_xboole_0(k1_xboole_0,A_9) = k4_xboole_0(A_209,B_210) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_4329])).

tff(c_4566,plain,(
    ! [A_209,B_210] :
      ( r2_hidden('#skF_2'(A_209,B_210,k1_xboole_0),k1_xboole_0)
      | r2_hidden('#skF_1'(A_209,B_210,k1_xboole_0),A_209)
      | k4_xboole_0(A_209,B_210) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_4508])).

tff(c_4568,plain,(
    ! [A_213,B_214] :
      ( r2_hidden('#skF_1'(A_213,B_214,k1_xboole_0),A_213)
      | k4_xboole_0(A_213,B_214) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_4566])).

tff(c_26,plain,(
    ! [D_15,B_11,A_10] :
      ( D_15 = B_11
      | D_15 = A_10
      | ~ r2_hidden(D_15,k2_tarski(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_142959,plain,(
    ! [A_1461,B_1462,B_1463] :
      ( '#skF_1'(k2_tarski(A_1461,B_1462),B_1463,k1_xboole_0) = B_1462
      | '#skF_1'(k2_tarski(A_1461,B_1462),B_1463,k1_xboole_0) = A_1461
      | k4_xboole_0(k2_tarski(A_1461,B_1462),B_1463) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4568,c_26])).

tff(c_144383,plain,
    ( '#skF_1'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0) = '#skF_6'
    | '#skF_1'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_142959,c_224])).

tff(c_144388,plain,(
    '#skF_1'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0) = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_144383])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_144416,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | r2_hidden('#skF_2'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0),k1_xboole_0)
    | k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_144388,c_16])).

tff(c_144434,plain,
    ( r2_hidden('#skF_2'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0),k1_xboole_0)
    | k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_144416])).

tff(c_144436,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_90,c_144434])).

tff(c_144437,plain,(
    '#skF_1'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_144383])).

tff(c_144466,plain,
    ( ~ r2_hidden('#skF_6','#skF_7')
    | r2_hidden('#skF_2'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0),k1_xboole_0)
    | k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_144437,c_16])).

tff(c_144484,plain,
    ( r2_hidden('#skF_2'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0),k1_xboole_0)
    | k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_144466])).

tff(c_144486,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_224,c_90,c_144484])).

tff(c_144488,plain,(
    k4_xboole_0(k2_tarski('#skF_8','#skF_9'),'#skF_10') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_54,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | k4_xboole_0(k2_tarski('#skF_8','#skF_9'),'#skF_10') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_144489,plain,(
    k4_xboole_0(k2_tarski('#skF_8','#skF_9'),'#skF_10') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_144490,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_144488,c_144489])).

tff(c_144492,plain,(
    k4_xboole_0(k2_tarski('#skF_8','#skF_9'),'#skF_10') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_52,plain,
    ( k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') != k1_xboole_0
    | k4_xboole_0(k2_tarski('#skF_8','#skF_9'),'#skF_10') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_144525,plain,(
    k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_144492,c_52])).

tff(c_144491,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_144487,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_144538,plain,(
    ! [A_1479,B_1480,C_1481] :
      ( r2_hidden('#skF_1'(A_1479,B_1480,C_1481),A_1479)
      | r2_hidden('#skF_2'(A_1479,B_1480,C_1481),C_1481)
      | k4_xboole_0(A_1479,B_1480) = C_1481 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_152073,plain,(
    ! [A_1694,B_1695,A_1696,B_1697] :
      ( r2_hidden('#skF_2'(A_1694,B_1695,k4_xboole_0(A_1696,B_1697)),A_1696)
      | r2_hidden('#skF_1'(A_1694,B_1695,k4_xboole_0(A_1696,B_1697)),A_1694)
      | k4_xboole_0(A_1696,B_1697) = k4_xboole_0(A_1694,B_1695) ) ),
    inference(resolution,[status(thm)],[c_144538,c_6])).

tff(c_152249,plain,(
    ! [A_1694,B_1695,A_9] :
      ( r2_hidden('#skF_2'(A_1694,B_1695,k4_xboole_0(k1_xboole_0,A_9)),k1_xboole_0)
      | r2_hidden('#skF_1'(A_1694,B_1695,k1_xboole_0),A_1694)
      | k4_xboole_0(k1_xboole_0,A_9) = k4_xboole_0(A_1694,B_1695) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_152073])).

tff(c_152307,plain,(
    ! [A_1694,B_1695] :
      ( r2_hidden('#skF_2'(A_1694,B_1695,k1_xboole_0),k1_xboole_0)
      | r2_hidden('#skF_1'(A_1694,B_1695,k1_xboole_0),A_1694)
      | k4_xboole_0(A_1694,B_1695) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_152249])).

tff(c_152309,plain,(
    ! [A_1698,B_1699] :
      ( r2_hidden('#skF_1'(A_1698,B_1699,k1_xboole_0),A_1698)
      | k4_xboole_0(A_1698,B_1699) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_152307])).

tff(c_155665,plain,(
    ! [A_1770,B_1771,B_1772] :
      ( '#skF_1'(k2_tarski(A_1770,B_1771),B_1772,k1_xboole_0) = B_1771
      | '#skF_1'(k2_tarski(A_1770,B_1771),B_1772,k1_xboole_0) = A_1770
      | k4_xboole_0(k2_tarski(A_1770,B_1771),B_1772) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_152309,c_26])).

tff(c_155975,plain,
    ( '#skF_1'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0) = '#skF_6'
    | '#skF_1'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_155665,c_144525])).

tff(c_157164,plain,(
    '#skF_1'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0) = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_155975])).

tff(c_157180,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | r2_hidden('#skF_2'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0),k1_xboole_0)
    | k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_157164,c_16])).

tff(c_157196,plain,
    ( r2_hidden('#skF_2'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0),k1_xboole_0)
    | k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_144487,c_157180])).

tff(c_157198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_144525,c_90,c_157196])).

tff(c_157199,plain,(
    '#skF_1'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0) = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_155975])).

tff(c_157216,plain,
    ( ~ r2_hidden('#skF_6','#skF_7')
    | r2_hidden('#skF_2'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0),k1_xboole_0)
    | k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_157199,c_16])).

tff(c_157232,plain,
    ( r2_hidden('#skF_2'(k2_tarski('#skF_5','#skF_6'),'#skF_7',k1_xboole_0),k1_xboole_0)
    | k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_144491,c_157216])).

tff(c_157234,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_144525,c_90,c_157232])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:01:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 40.68/31.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 40.77/31.47  
% 40.77/31.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 40.77/31.48  %$ r2_hidden > r1_tarski > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_3
% 40.77/31.48  
% 40.77/31.48  %Foreground sorts:
% 40.77/31.48  
% 40.77/31.48  
% 40.77/31.48  %Background operators:
% 40.77/31.48  
% 40.77/31.48  
% 40.77/31.48  %Foreground operators:
% 40.77/31.48  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 40.77/31.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 40.77/31.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 40.77/31.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 40.77/31.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 40.77/31.48  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 40.77/31.48  tff('#skF_7', type, '#skF_7': $i).
% 40.77/31.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 40.77/31.48  tff('#skF_10', type, '#skF_10': $i).
% 40.77/31.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 40.77/31.48  tff('#skF_5', type, '#skF_5': $i).
% 40.77/31.48  tff('#skF_6', type, '#skF_6': $i).
% 40.77/31.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 40.77/31.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 40.77/31.48  tff('#skF_9', type, '#skF_9': $i).
% 40.77/31.48  tff('#skF_8', type, '#skF_8': $i).
% 40.77/31.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 40.77/31.48  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 40.77/31.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 40.77/31.48  
% 40.77/31.49  tff(f_59, negated_conjecture, ~(![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_xboole_0) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 40.77/31.49  tff(f_50, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 40.77/31.49  tff(f_41, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 40.77/31.49  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 40.77/31.49  tff(c_50, plain, (r2_hidden('#skF_5', '#skF_7') | ~r2_hidden('#skF_9', '#skF_10') | ~r2_hidden('#skF_8', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_59])).
% 40.77/31.49  tff(c_121, plain, (~r2_hidden('#skF_8', '#skF_10')), inference(splitLeft, [status(thm)], [c_50])).
% 40.77/31.49  tff(c_30, plain, (![D_15, B_11]: (r2_hidden(D_15, k2_tarski(D_15, B_11)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 40.77/31.49  tff(c_28, plain, (![D_15, A_10]: (r2_hidden(D_15, k2_tarski(A_10, D_15)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 40.77/31.49  tff(c_24, plain, (![A_9]: (k4_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 40.77/31.49  tff(c_81, plain, (![D_29, B_30, A_31]: (~r2_hidden(D_29, B_30) | ~r2_hidden(D_29, k4_xboole_0(A_31, B_30)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 40.77/31.49  tff(c_85, plain, (![D_32, A_33]: (~r2_hidden(D_32, A_33) | ~r2_hidden(D_32, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_81])).
% 40.77/31.49  tff(c_90, plain, (![D_15]: (~r2_hidden(D_15, k1_xboole_0))), inference(resolution, [status(thm)], [c_28, c_85])).
% 40.77/31.49  tff(c_56, plain, (r2_hidden('#skF_5', '#skF_7') | k4_xboole_0(k2_tarski('#skF_8', '#skF_9'), '#skF_10')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 40.77/31.49  tff(c_93, plain, (k4_xboole_0(k2_tarski('#skF_8', '#skF_9'), '#skF_10')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_56])).
% 40.77/31.49  tff(c_122, plain, (![D_41, A_42, B_43]: (r2_hidden(D_41, k4_xboole_0(A_42, B_43)) | r2_hidden(D_41, B_43) | ~r2_hidden(D_41, A_42))), inference(cnfTransformation, [status(thm)], [f_35])).
% 40.77/31.49  tff(c_131, plain, (![D_41]: (r2_hidden(D_41, k1_xboole_0) | r2_hidden(D_41, '#skF_10') | ~r2_hidden(D_41, k2_tarski('#skF_8', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_93, c_122])).
% 40.77/31.49  tff(c_139, plain, (![D_44]: (r2_hidden(D_44, '#skF_10') | ~r2_hidden(D_44, k2_tarski('#skF_8', '#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_90, c_131])).
% 40.77/31.49  tff(c_147, plain, (r2_hidden('#skF_8', '#skF_10')), inference(resolution, [status(thm)], [c_30, c_139])).
% 40.77/31.49  tff(c_152, plain, $false, inference(negUnitSimplification, [status(thm)], [c_121, c_147])).
% 40.77/31.49  tff(c_154, plain, (r2_hidden('#skF_8', '#skF_10')), inference(splitRight, [status(thm)], [c_50])).
% 40.77/31.49  tff(c_153, plain, (~r2_hidden('#skF_9', '#skF_10') | r2_hidden('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_50])).
% 40.77/31.49  tff(c_155, plain, (~r2_hidden('#skF_9', '#skF_10')), inference(splitLeft, [status(thm)], [c_153])).
% 40.77/31.49  tff(c_158, plain, (![D_45, A_46, B_47]: (r2_hidden(D_45, k4_xboole_0(A_46, B_47)) | r2_hidden(D_45, B_47) | ~r2_hidden(D_45, A_46))), inference(cnfTransformation, [status(thm)], [f_35])).
% 40.77/31.49  tff(c_167, plain, (![D_45]: (r2_hidden(D_45, k1_xboole_0) | r2_hidden(D_45, '#skF_10') | ~r2_hidden(D_45, k2_tarski('#skF_8', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_93, c_158])).
% 40.77/31.49  tff(c_175, plain, (![D_48]: (r2_hidden(D_48, '#skF_10') | ~r2_hidden(D_48, k2_tarski('#skF_8', '#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_90, c_167])).
% 40.77/31.49  tff(c_179, plain, (r2_hidden('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_28, c_175])).
% 40.77/31.49  tff(c_187, plain, $false, inference(negUnitSimplification, [status(thm)], [c_155, c_179])).
% 40.77/31.49  tff(c_189, plain, (r2_hidden('#skF_9', '#skF_10')), inference(splitRight, [status(thm)], [c_153])).
% 40.77/31.49  tff(c_46, plain, (k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')!=k1_xboole_0 | ~r2_hidden('#skF_9', '#skF_10') | ~r2_hidden('#skF_8', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_59])).
% 40.77/31.49  tff(c_224, plain, (k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_154, c_189, c_46])).
% 40.77/31.49  tff(c_48, plain, (r2_hidden('#skF_6', '#skF_7') | ~r2_hidden('#skF_9', '#skF_10') | ~r2_hidden('#skF_8', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_59])).
% 40.77/31.49  tff(c_191, plain, (r2_hidden('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_189, c_48])).
% 40.77/31.49  tff(c_188, plain, (r2_hidden('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_153])).
% 40.77/31.49  tff(c_275, plain, (![A_70, B_71, C_72]: (r2_hidden('#skF_1'(A_70, B_71, C_72), A_70) | r2_hidden('#skF_2'(A_70, B_71, C_72), C_72) | k4_xboole_0(A_70, B_71)=C_72)), inference(cnfTransformation, [status(thm)], [f_35])).
% 40.77/31.49  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 40.77/31.49  tff(c_4329, plain, (![A_209, B_210, A_211, B_212]: (r2_hidden('#skF_2'(A_209, B_210, k4_xboole_0(A_211, B_212)), A_211) | r2_hidden('#skF_1'(A_209, B_210, k4_xboole_0(A_211, B_212)), A_209) | k4_xboole_0(A_211, B_212)=k4_xboole_0(A_209, B_210))), inference(resolution, [status(thm)], [c_275, c_6])).
% 40.77/31.49  tff(c_4508, plain, (![A_209, B_210, A_9]: (r2_hidden('#skF_2'(A_209, B_210, k4_xboole_0(k1_xboole_0, A_9)), k1_xboole_0) | r2_hidden('#skF_1'(A_209, B_210, k1_xboole_0), A_209) | k4_xboole_0(k1_xboole_0, A_9)=k4_xboole_0(A_209, B_210))), inference(superposition, [status(thm), theory('equality')], [c_24, c_4329])).
% 40.77/31.49  tff(c_4566, plain, (![A_209, B_210]: (r2_hidden('#skF_2'(A_209, B_210, k1_xboole_0), k1_xboole_0) | r2_hidden('#skF_1'(A_209, B_210, k1_xboole_0), A_209) | k4_xboole_0(A_209, B_210)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_4508])).
% 40.77/31.49  tff(c_4568, plain, (![A_213, B_214]: (r2_hidden('#skF_1'(A_213, B_214, k1_xboole_0), A_213) | k4_xboole_0(A_213, B_214)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_90, c_4566])).
% 40.77/31.49  tff(c_26, plain, (![D_15, B_11, A_10]: (D_15=B_11 | D_15=A_10 | ~r2_hidden(D_15, k2_tarski(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 40.77/31.49  tff(c_142959, plain, (![A_1461, B_1462, B_1463]: ('#skF_1'(k2_tarski(A_1461, B_1462), B_1463, k1_xboole_0)=B_1462 | '#skF_1'(k2_tarski(A_1461, B_1462), B_1463, k1_xboole_0)=A_1461 | k4_xboole_0(k2_tarski(A_1461, B_1462), B_1463)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4568, c_26])).
% 40.77/31.49  tff(c_144383, plain, ('#skF_1'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0)='#skF_6' | '#skF_1'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0)='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_142959, c_224])).
% 40.77/31.49  tff(c_144388, plain, ('#skF_1'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0)='#skF_5'), inference(splitLeft, [status(thm)], [c_144383])).
% 40.77/31.49  tff(c_16, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 40.77/31.49  tff(c_144416, plain, (~r2_hidden('#skF_5', '#skF_7') | r2_hidden('#skF_2'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0), k1_xboole_0) | k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_144388, c_16])).
% 40.77/31.49  tff(c_144434, plain, (r2_hidden('#skF_2'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0), k1_xboole_0) | k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_188, c_144416])).
% 40.77/31.49  tff(c_144436, plain, $false, inference(negUnitSimplification, [status(thm)], [c_224, c_90, c_144434])).
% 40.77/31.49  tff(c_144437, plain, ('#skF_1'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0)='#skF_6'), inference(splitRight, [status(thm)], [c_144383])).
% 40.77/31.49  tff(c_144466, plain, (~r2_hidden('#skF_6', '#skF_7') | r2_hidden('#skF_2'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0), k1_xboole_0) | k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_144437, c_16])).
% 40.77/31.49  tff(c_144484, plain, (r2_hidden('#skF_2'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0), k1_xboole_0) | k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_191, c_144466])).
% 40.77/31.49  tff(c_144486, plain, $false, inference(negUnitSimplification, [status(thm)], [c_224, c_90, c_144484])).
% 40.77/31.49  tff(c_144488, plain, (k4_xboole_0(k2_tarski('#skF_8', '#skF_9'), '#skF_10')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_56])).
% 40.77/31.49  tff(c_54, plain, (r2_hidden('#skF_6', '#skF_7') | k4_xboole_0(k2_tarski('#skF_8', '#skF_9'), '#skF_10')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 40.77/31.49  tff(c_144489, plain, (k4_xboole_0(k2_tarski('#skF_8', '#skF_9'), '#skF_10')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_54])).
% 40.77/31.49  tff(c_144490, plain, $false, inference(negUnitSimplification, [status(thm)], [c_144488, c_144489])).
% 40.77/31.49  tff(c_144492, plain, (k4_xboole_0(k2_tarski('#skF_8', '#skF_9'), '#skF_10')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_54])).
% 40.77/31.49  tff(c_52, plain, (k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')!=k1_xboole_0 | k4_xboole_0(k2_tarski('#skF_8', '#skF_9'), '#skF_10')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 40.77/31.49  tff(c_144525, plain, (k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_144492, c_52])).
% 40.77/31.49  tff(c_144491, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_54])).
% 40.77/31.49  tff(c_144487, plain, (r2_hidden('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_56])).
% 40.77/31.49  tff(c_144538, plain, (![A_1479, B_1480, C_1481]: (r2_hidden('#skF_1'(A_1479, B_1480, C_1481), A_1479) | r2_hidden('#skF_2'(A_1479, B_1480, C_1481), C_1481) | k4_xboole_0(A_1479, B_1480)=C_1481)), inference(cnfTransformation, [status(thm)], [f_35])).
% 40.77/31.49  tff(c_152073, plain, (![A_1694, B_1695, A_1696, B_1697]: (r2_hidden('#skF_2'(A_1694, B_1695, k4_xboole_0(A_1696, B_1697)), A_1696) | r2_hidden('#skF_1'(A_1694, B_1695, k4_xboole_0(A_1696, B_1697)), A_1694) | k4_xboole_0(A_1696, B_1697)=k4_xboole_0(A_1694, B_1695))), inference(resolution, [status(thm)], [c_144538, c_6])).
% 40.77/31.49  tff(c_152249, plain, (![A_1694, B_1695, A_9]: (r2_hidden('#skF_2'(A_1694, B_1695, k4_xboole_0(k1_xboole_0, A_9)), k1_xboole_0) | r2_hidden('#skF_1'(A_1694, B_1695, k1_xboole_0), A_1694) | k4_xboole_0(k1_xboole_0, A_9)=k4_xboole_0(A_1694, B_1695))), inference(superposition, [status(thm), theory('equality')], [c_24, c_152073])).
% 40.77/31.49  tff(c_152307, plain, (![A_1694, B_1695]: (r2_hidden('#skF_2'(A_1694, B_1695, k1_xboole_0), k1_xboole_0) | r2_hidden('#skF_1'(A_1694, B_1695, k1_xboole_0), A_1694) | k4_xboole_0(A_1694, B_1695)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_152249])).
% 40.77/31.49  tff(c_152309, plain, (![A_1698, B_1699]: (r2_hidden('#skF_1'(A_1698, B_1699, k1_xboole_0), A_1698) | k4_xboole_0(A_1698, B_1699)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_90, c_152307])).
% 40.77/31.49  tff(c_155665, plain, (![A_1770, B_1771, B_1772]: ('#skF_1'(k2_tarski(A_1770, B_1771), B_1772, k1_xboole_0)=B_1771 | '#skF_1'(k2_tarski(A_1770, B_1771), B_1772, k1_xboole_0)=A_1770 | k4_xboole_0(k2_tarski(A_1770, B_1771), B_1772)=k1_xboole_0)), inference(resolution, [status(thm)], [c_152309, c_26])).
% 40.77/31.49  tff(c_155975, plain, ('#skF_1'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0)='#skF_6' | '#skF_1'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0)='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_155665, c_144525])).
% 40.77/31.49  tff(c_157164, plain, ('#skF_1'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0)='#skF_5'), inference(splitLeft, [status(thm)], [c_155975])).
% 40.77/31.49  tff(c_157180, plain, (~r2_hidden('#skF_5', '#skF_7') | r2_hidden('#skF_2'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0), k1_xboole_0) | k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_157164, c_16])).
% 40.77/31.49  tff(c_157196, plain, (r2_hidden('#skF_2'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0), k1_xboole_0) | k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_144487, c_157180])).
% 40.77/31.49  tff(c_157198, plain, $false, inference(negUnitSimplification, [status(thm)], [c_144525, c_90, c_157196])).
% 40.77/31.49  tff(c_157199, plain, ('#skF_1'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0)='#skF_6'), inference(splitRight, [status(thm)], [c_155975])).
% 40.77/31.49  tff(c_157216, plain, (~r2_hidden('#skF_6', '#skF_7') | r2_hidden('#skF_2'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0), k1_xboole_0) | k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_157199, c_16])).
% 40.77/31.49  tff(c_157232, plain, (r2_hidden('#skF_2'(k2_tarski('#skF_5', '#skF_6'), '#skF_7', k1_xboole_0), k1_xboole_0) | k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_144491, c_157216])).
% 40.77/31.49  tff(c_157234, plain, $false, inference(negUnitSimplification, [status(thm)], [c_144525, c_90, c_157232])).
% 40.77/31.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 40.77/31.49  
% 40.77/31.49  Inference rules
% 40.77/31.49  ----------------------
% 40.77/31.49  #Ref     : 0
% 40.77/31.49  #Sup     : 39936
% 40.77/31.49  #Fact    : 46
% 40.77/31.49  #Define  : 0
% 40.77/31.49  #Split   : 16
% 40.77/31.49  #Chain   : 0
% 40.77/31.49  #Close   : 0
% 40.77/31.49  
% 40.77/31.49  Ordering : KBO
% 40.77/31.49  
% 40.77/31.49  Simplification rules
% 40.77/31.49  ----------------------
% 40.77/31.49  #Subsume      : 19024
% 40.77/31.49  #Demod        : 48161
% 40.77/31.49  #Tautology    : 9964
% 40.77/31.49  #SimpNegUnit  : 1647
% 40.77/31.49  #BackRed      : 81
% 40.77/31.49  
% 40.77/31.49  #Partial instantiations: 0
% 40.77/31.49  #Strategies tried      : 1
% 40.77/31.49  
% 40.77/31.49  Timing (in seconds)
% 40.77/31.49  ----------------------
% 40.77/31.50  Preprocessing        : 0.31
% 40.77/31.50  Parsing              : 0.15
% 40.77/31.50  CNF conversion       : 0.02
% 40.77/31.50  Main loop            : 30.35
% 40.77/31.50  Inferencing          : 3.99
% 40.77/31.50  Reduction            : 16.01
% 40.77/31.50  Demodulation         : 14.07
% 40.77/31.50  BG Simplification    : 0.39
% 40.77/31.50  Subsumption          : 8.67
% 40.77/31.50  Abstraction          : 1.03
% 40.77/31.50  MUC search           : 0.00
% 40.77/31.50  Cooper               : 0.00
% 40.77/31.50  Total                : 30.69
% 40.77/31.50  Index Insertion      : 0.00
% 40.77/31.50  Index Deletion       : 0.00
% 40.77/31.50  Index Matching       : 0.00
% 40.77/31.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
