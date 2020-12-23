%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0878+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:00 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   29 ( 108 expanded)
%              Number of leaves         :    9 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   61 ( 303 expanded)
%              Number of equality atoms :   58 ( 300 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_43,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_zfmisc_1(A,A,A) = k3_zfmisc_1(B,B,B)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_mcart_1)).

tff(f_38,axiom,(
    ! [A,B,C,D,E,F] :
      ( k3_zfmisc_1(A,B,C) = k3_zfmisc_1(D,E,F)
     => ( A = k1_xboole_0
        | B = k1_xboole_0
        | C = k1_xboole_0
        | ( A = D
          & B = E
          & C = F ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_mcart_1)).

tff(c_8,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k3_zfmisc_1('#skF_1','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_30,plain,(
    ! [B_16,D_15,E_14,F_13,A_18,C_17] :
      ( D_15 = A_18
      | k1_xboole_0 = C_17
      | k1_xboole_0 = B_16
      | k1_xboole_0 = A_18
      | k3_zfmisc_1(D_15,E_14,F_13) != k3_zfmisc_1(A_18,B_16,C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_33,plain,(
    ! [A_18,C_17,B_16] :
      ( A_18 = '#skF_2'
      | k1_xboole_0 = C_17
      | k1_xboole_0 = B_16
      | k1_xboole_0 = A_18
      | k3_zfmisc_1(A_18,B_16,C_17) != k3_zfmisc_1('#skF_1','#skF_1','#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_30])).

tff(c_66,plain,
    ( '#skF_2' = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_33])).

tff(c_67,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_66])).

tff(c_76,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_36,plain,(
    ! [D_15,E_14,F_13] :
      ( D_15 = '#skF_2'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_2'
      | k3_zfmisc_1(D_15,E_14,F_13) != k3_zfmisc_1('#skF_1','#skF_1','#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_30])).

tff(c_48,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_56,plain,(
    ! [A_18,C_17,B_16] :
      ( A_18 = '#skF_2'
      | C_17 = '#skF_2'
      | B_16 = '#skF_2'
      | A_18 = '#skF_2'
      | k3_zfmisc_1(A_18,B_16,C_17) != k3_zfmisc_1('#skF_1','#skF_1','#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_48,c_33])).

tff(c_59,plain,
    ( '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_56])).

tff(c_61,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_8,c_8,c_8,c_59])).

tff(c_62,plain,(
    ! [D_15,E_14,F_13] :
      ( k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_2'
      | D_15 = '#skF_2'
      | k3_zfmisc_1(D_15,E_14,F_13) != k3_zfmisc_1('#skF_1','#skF_1','#skF_1') ) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_86,plain,(
    ! [D_15,E_14,F_13] :
      ( '#skF_2' = '#skF_1'
      | '#skF_2' = '#skF_1'
      | D_15 = '#skF_2'
      | k3_zfmisc_1(D_15,E_14,F_13) != k3_zfmisc_1('#skF_1','#skF_1','#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_76,c_62])).

tff(c_87,plain,(
    ! [D_15,E_14,F_13] :
      ( D_15 = '#skF_2'
      | k3_zfmisc_1(D_15,E_14,F_13) != k3_zfmisc_1('#skF_1','#skF_1','#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_8,c_86])).

tff(c_90,plain,(
    '#skF_2' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_87])).

tff(c_92,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_90])).

tff(c_94,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_93,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_95,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_94,c_93])).

%------------------------------------------------------------------------------
