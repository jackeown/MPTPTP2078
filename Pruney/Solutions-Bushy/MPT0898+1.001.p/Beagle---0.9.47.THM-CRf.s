%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0898+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:02 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   24 (  78 expanded)
%              Number of leaves         :    9 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   60 ( 262 expanded)
%              Number of equality atoms :   58 ( 260 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_47,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_zfmisc_1(A,A,A,A) = k4_zfmisc_1(B,B,B,B)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_mcart_1)).

tff(f_42,axiom,(
    ! [A,B,C,D,E,F,G,H] :
      ( k4_zfmisc_1(A,B,C,D) = k4_zfmisc_1(E,F,G,H)
     => ( A = k1_xboole_0
        | B = k1_xboole_0
        | C = k1_xboole_0
        | D = k1_xboole_0
        | ( A = E
          & B = F
          & C = G
          & D = H ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_mcart_1)).

tff(c_10,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    k4_zfmisc_1('#skF_2','#skF_2','#skF_2','#skF_2') = k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_21,plain,(
    ! [A_15,G_10,H_16,F_9,C_14,B_13,E_11,D_12] :
      ( G_10 = C_14
      | k1_xboole_0 = D_12
      | k1_xboole_0 = C_14
      | k1_xboole_0 = B_13
      | k1_xboole_0 = A_15
      | k4_zfmisc_1(E_11,F_9,G_10,H_16) != k4_zfmisc_1(A_15,B_13,C_14,D_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_27,plain,(
    ! [G_10,E_11,F_9,H_16] :
      ( G_10 = '#skF_2'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_2'
      | k4_zfmisc_1(E_11,F_9,G_10,H_16) != k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_21])).

tff(c_61,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_27])).

tff(c_32,plain,(
    ! [C_22,E_19,H_24,B_21,D_20,A_23,F_17,G_18] :
      ( F_17 = B_21
      | k1_xboole_0 = D_20
      | k1_xboole_0 = C_22
      | k1_xboole_0 = B_21
      | k1_xboole_0 = A_23
      | k4_zfmisc_1(E_19,F_17,G_18,H_24) != k4_zfmisc_1(A_23,B_21,C_22,D_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_35,plain,(
    ! [B_21,D_20,C_22,A_23] :
      ( B_21 = '#skF_2'
      | k1_xboole_0 = D_20
      | k1_xboole_0 = C_22
      | k1_xboole_0 = B_21
      | k1_xboole_0 = A_23
      | k4_zfmisc_1(A_23,B_21,C_22,D_20) != k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_32])).

tff(c_70,plain,(
    ! [B_21,D_20,C_22,A_23] :
      ( B_21 = '#skF_2'
      | D_20 = '#skF_2'
      | C_22 = '#skF_2'
      | B_21 = '#skF_2'
      | A_23 = '#skF_2'
      | k4_zfmisc_1(A_23,B_21,C_22,D_20) != k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_61,c_61,c_61,c_35])).

tff(c_73,plain,
    ( '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_70])).

tff(c_75,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_10,c_10,c_10,c_10,c_73])).

tff(c_77,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_27])).

tff(c_76,plain,(
    ! [G_10,E_11,F_9,H_16] :
      ( k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_2'
      | G_10 = '#skF_2'
      | k4_zfmisc_1(E_11,F_9,G_10,H_16) != k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ) ),
    inference(splitRight,[status(thm)],[c_27])).

tff(c_108,plain,(
    ! [G_10,E_11,F_9,H_16] :
      ( G_10 = '#skF_2'
      | k4_zfmisc_1(E_11,F_9,G_10,H_16) != k4_zfmisc_1('#skF_1','#skF_1','#skF_1','#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_77,c_77,c_76])).

tff(c_111,plain,(
    '#skF_2' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_108])).

tff(c_113,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_111])).

%------------------------------------------------------------------------------
