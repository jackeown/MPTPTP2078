%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0915+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:04 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 125 expanded)
%              Number of leaves         :   21 (  60 expanded)
%              Depth                    :    6
%              Number of atoms          :   88 ( 578 expanded)
%              Number of equality atoms :   77 ( 485 expanded)
%              Maximal formula depth    :   23 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & D != k1_xboole_0
          & E != k1_xboole_0
          & F != k1_xboole_0
          & ? [G] :
              ( m1_subset_1(G,k3_zfmisc_1(A,B,C))
              & ? [H] :
                  ( m1_subset_1(H,k3_zfmisc_1(D,E,F))
                  & G = H
                  & ~ ( k5_mcart_1(A,B,C,G) = k5_mcart_1(D,E,F,H)
                      & k6_mcart_1(A,B,C,G) = k6_mcart_1(D,E,F,H)
                      & k7_mcart_1(A,B,C,G) = k7_mcart_1(D,E,F,H) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_mcart_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_10,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_14,plain,(
    m1_subset_1('#skF_7',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_27,plain,(
    m1_subset_1('#skF_8',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14])).

tff(c_98,plain,(
    ! [A_22,B_23,C_24,D_25] :
      ( k7_mcart_1(A_22,B_23,C_24,D_25) = k2_mcart_1(D_25)
      | ~ m1_subset_1(D_25,k3_zfmisc_1(A_22,B_23,C_24))
      | k1_xboole_0 = C_24
      | k1_xboole_0 = B_23
      | k1_xboole_0 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_104,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_27,c_98])).

tff(c_110,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_24,c_22,c_104])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_16,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_12,plain,(
    m1_subset_1('#skF_8',k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_101,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_12,c_98])).

tff(c_107,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_18,c_16,c_101])).

tff(c_8,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7') != k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8')
    | k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7') != k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8')
    | k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7') != k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_28,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_8') != k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8')
    | k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_8') != k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8')
    | k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_8') != k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_10,c_8])).

tff(c_33,plain,(
    k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_8') != k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_68,plain,(
    ! [A_18,B_19,C_20,D_21] :
      ( k5_mcart_1(A_18,B_19,C_20,D_21) = k1_mcart_1(k1_mcart_1(D_21))
      | ~ m1_subset_1(D_21,k3_zfmisc_1(A_18,B_19,C_20))
      | k1_xboole_0 = C_20
      | k1_xboole_0 = B_19
      | k1_xboole_0 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_71,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_12,c_68])).

tff(c_77,plain,(
    k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_18,c_16,c_71])).

tff(c_74,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_8')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_27,c_68])).

tff(c_80,plain,(
    k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_24,c_22,c_74])).

tff(c_89,plain,(
    k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_8') = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_80])).

tff(c_91,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_89])).

tff(c_92,plain,
    ( k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_8') != k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8')
    | k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_8') != k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_137,plain,(
    k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_8') != k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_107,c_92])).

tff(c_139,plain,(
    ! [A_30,B_31,C_32,D_33] :
      ( k6_mcart_1(A_30,B_31,C_32,D_33) = k2_mcart_1(k1_mcart_1(D_33))
      | ~ m1_subset_1(D_33,k3_zfmisc_1(A_30,B_31,C_32))
      | k1_xboole_0 = C_32
      | k1_xboole_0 = B_31
      | k1_xboole_0 = A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_142,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_12,c_139])).

tff(c_148,plain,(
    k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_18,c_16,c_142])).

tff(c_145,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_8')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_27,c_139])).

tff(c_151,plain,(
    k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_24,c_22,c_145])).

tff(c_156,plain,(
    k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_8') = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_151])).

tff(c_157,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_156])).

%------------------------------------------------------------------------------
