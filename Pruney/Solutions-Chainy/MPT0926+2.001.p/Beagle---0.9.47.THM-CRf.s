%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:23 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 162 expanded)
%              Number of leaves         :   24 (  79 expanded)
%              Depth                    :    7
%              Number of atoms          :  121 ( 968 expanded)
%              Number of equality atoms :  110 ( 841 expanded)
%              Maximal formula depth    :   28 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k10_mcart_1,type,(
    k10_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k11_mcart_1,type,(
    k11_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k8_mcart_1,type,(
    k8_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k9_mcart_1,type,(
    k9_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C,D,E,F,G,H] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & D != k1_xboole_0
          & E != k1_xboole_0
          & F != k1_xboole_0
          & G != k1_xboole_0
          & H != k1_xboole_0
          & ? [I] :
              ( m1_subset_1(I,k4_zfmisc_1(A,B,C,D))
              & ? [J] :
                  ( m1_subset_1(J,k4_zfmisc_1(E,F,G,H))
                  & I = J
                  & ~ ( k8_mcart_1(A,B,C,D,I) = k8_mcart_1(E,F,G,H,J)
                      & k9_mcart_1(A,B,C,D,I) = k9_mcart_1(E,F,G,H,J)
                      & k10_mcart_1(A,B,C,D,I) = k10_mcart_1(E,F,G,H,J)
                      & k11_mcart_1(A,B,C,D,I) = k11_mcart_1(E,F,G,H,J) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_mcart_1)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & ~ ! [E] :
              ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
             => ( k8_mcart_1(A,B,C,D,E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))
                & k9_mcart_1(A,B,C,D,E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E)))
                & k10_mcart_1(A,B,C,D,E) = k2_mcart_1(k1_mcart_1(E))
                & k11_mcart_1(A,B,C,D,E) = k2_mcart_1(E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_16,plain,(
    m1_subset_1('#skF_9',k4_zfmisc_1('#skF_1','#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_73,plain,(
    ! [B_22,A_25,D_21,C_23,E_24] :
      ( k9_mcart_1(A_25,B_22,C_23,D_21,E_24) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E_24)))
      | ~ m1_subset_1(E_24,k4_zfmisc_1(A_25,B_22,C_23,D_21))
      | k1_xboole_0 = D_21
      | k1_xboole_0 = C_23
      | k1_xboole_0 = B_22
      | k1_xboole_0 = A_25 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_77,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_16,c_73])).

tff(c_83,plain,(
    k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_26,c_77])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_12,plain,(
    '#skF_10' = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_14,plain,(
    m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_33,plain,(
    m1_subset_1('#skF_9',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_14])).

tff(c_75,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_33,c_73])).

tff(c_80,plain,(
    k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_18,c_75])).

tff(c_97,plain,(
    k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_80])).

tff(c_60,plain,(
    ! [C_18,B_17,E_19,A_20,D_16] :
      ( k2_mcart_1(k1_mcart_1(E_19)) = k10_mcart_1(A_20,B_17,C_18,D_16,E_19)
      | ~ m1_subset_1(E_19,k4_zfmisc_1(A_20,B_17,C_18,D_16))
      | k1_xboole_0 = D_16
      | k1_xboole_0 = C_18
      | k1_xboole_0 = B_17
      | k1_xboole_0 = A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_66,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) = k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_16,c_60])).

tff(c_72,plain,(
    k2_mcart_1(k1_mcart_1('#skF_9')) = k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_26,c_66])).

tff(c_63,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) = k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_33,c_60])).

tff(c_69,plain,(
    k2_mcart_1(k1_mcart_1('#skF_9')) = k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_18,c_63])).

tff(c_88,plain,(
    k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_69])).

tff(c_39,plain,(
    ! [A_15,D_11,E_14,B_12,C_13] :
      ( k11_mcart_1(A_15,B_12,C_13,D_11,E_14) = k2_mcart_1(E_14)
      | ~ m1_subset_1(E_14,k4_zfmisc_1(A_15,B_12,C_13,D_11))
      | k1_xboole_0 = D_11
      | k1_xboole_0 = C_13
      | k1_xboole_0 = B_12
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_45,plain,
    ( k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_16,c_39])).

tff(c_51,plain,(
    k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9') = k2_mcart_1('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_26,c_45])).

tff(c_42,plain,
    ( k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_33,c_39])).

tff(c_48,plain,(
    k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = k2_mcart_1('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_18,c_42])).

tff(c_10,plain,
    ( k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') != k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') != k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') != k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') != k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_34,plain,
    ( k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') != k11_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') != k10_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') != k9_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') != k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_12,c_12,c_10])).

tff(c_131,plain,(
    k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') != k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_88,c_51,c_48,c_34])).

tff(c_110,plain,(
    ! [B_27,E_29,A_30,D_26,C_28] :
      ( k8_mcart_1(A_30,B_27,C_28,D_26,E_29) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E_29)))
      | ~ m1_subset_1(E_29,k4_zfmisc_1(A_30,B_27,C_28,D_26))
      | k1_xboole_0 = D_26
      | k1_xboole_0 = C_28
      | k1_xboole_0 = B_27
      | k1_xboole_0 = A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_114,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_16,c_110])).

tff(c_120,plain,(
    k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_26,c_114])).

tff(c_112,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_33,c_110])).

tff(c_117,plain,(
    k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9'))) = k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_22,c_20,c_18,c_112])).

tff(c_125,plain,(
    k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9') = k8_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_117])).

tff(c_132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_125])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:24:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.19  
% 2.01/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.19  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_9 > #skF_8 > #skF_4
% 2.01/1.19  
% 2.01/1.19  %Foreground sorts:
% 2.01/1.19  
% 2.01/1.19  
% 2.01/1.19  %Background operators:
% 2.01/1.19  
% 2.01/1.19  
% 2.01/1.19  %Foreground operators:
% 2.01/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.19  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.01/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.01/1.19  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 2.01/1.19  tff('#skF_7', type, '#skF_7': $i).
% 2.01/1.19  tff('#skF_10', type, '#skF_10': $i).
% 2.01/1.19  tff('#skF_5', type, '#skF_5': $i).
% 2.01/1.19  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.01/1.19  tff('#skF_6', type, '#skF_6': $i).
% 2.01/1.19  tff('#skF_2', type, '#skF_2': $i).
% 2.01/1.19  tff('#skF_3', type, '#skF_3': $i).
% 2.01/1.19  tff('#skF_1', type, '#skF_1': $i).
% 2.01/1.19  tff('#skF_9', type, '#skF_9': $i).
% 2.01/1.19  tff('#skF_8', type, '#skF_8': $i).
% 2.01/1.19  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.01/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.19  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.01/1.19  tff('#skF_4', type, '#skF_4': $i).
% 2.01/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.19  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.01/1.19  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.01/1.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.01/1.19  
% 2.13/1.21  tff(f_93, negated_conjecture, ~(![A, B, C, D, E, F, G, H]: ~((((((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(E = k1_xboole_0)) & ~(F = k1_xboole_0)) & ~(G = k1_xboole_0)) & ~(H = k1_xboole_0)) & (?[I]: (m1_subset_1(I, k4_zfmisc_1(A, B, C, D)) & (?[J]: ((m1_subset_1(J, k4_zfmisc_1(E, F, G, H)) & (I = J)) & ~((((k8_mcart_1(A, B, C, D, I) = k8_mcart_1(E, F, G, H, J)) & (k9_mcart_1(A, B, C, D, I) = k9_mcart_1(E, F, G, H, J))) & (k10_mcart_1(A, B, C, D, I) = k10_mcart_1(E, F, G, H, J))) & (k11_mcart_1(A, B, C, D, I) = k11_mcart_1(E, F, G, H, J))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_mcart_1)).
% 2.13/1.21  tff(f_50, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ((((k8_mcart_1(A, B, C, D, E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))) & (k9_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E))))) & (k10_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(E)))) & (k11_mcart_1(A, B, C, D, E) = k2_mcart_1(E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_mcart_1)).
% 2.13/1.21  tff(c_32, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.13/1.21  tff(c_30, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.13/1.21  tff(c_28, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.13/1.21  tff(c_26, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.13/1.21  tff(c_16, plain, (m1_subset_1('#skF_9', k4_zfmisc_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.13/1.21  tff(c_73, plain, (![B_22, A_25, D_21, C_23, E_24]: (k9_mcart_1(A_25, B_22, C_23, D_21, E_24)=k2_mcart_1(k1_mcart_1(k1_mcart_1(E_24))) | ~m1_subset_1(E_24, k4_zfmisc_1(A_25, B_22, C_23, D_21)) | k1_xboole_0=D_21 | k1_xboole_0=C_23 | k1_xboole_0=B_22 | k1_xboole_0=A_25)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.13/1.21  tff(c_77, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))=k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_16, c_73])).
% 2.13/1.21  tff(c_83, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))=k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_26, c_77])).
% 2.13/1.21  tff(c_24, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.13/1.21  tff(c_22, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.13/1.21  tff(c_20, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.13/1.21  tff(c_18, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.13/1.21  tff(c_12, plain, ('#skF_10'='#skF_9'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.13/1.21  tff(c_14, plain, (m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.13/1.21  tff(c_33, plain, (m1_subset_1('#skF_9', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_14])).
% 2.13/1.21  tff(c_75, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))=k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_33, c_73])).
% 2.13/1.21  tff(c_80, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))=k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_18, c_75])).
% 2.13/1.21  tff(c_97, plain, (k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')=k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_83, c_80])).
% 2.13/1.21  tff(c_60, plain, (![C_18, B_17, E_19, A_20, D_16]: (k2_mcart_1(k1_mcart_1(E_19))=k10_mcart_1(A_20, B_17, C_18, D_16, E_19) | ~m1_subset_1(E_19, k4_zfmisc_1(A_20, B_17, C_18, D_16)) | k1_xboole_0=D_16 | k1_xboole_0=C_18 | k1_xboole_0=B_17 | k1_xboole_0=A_20)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.13/1.21  tff(c_66, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_16, c_60])).
% 2.13/1.21  tff(c_72, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_26, c_66])).
% 2.13/1.21  tff(c_63, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_33, c_60])).
% 2.13/1.21  tff(c_69, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_18, c_63])).
% 2.13/1.21  tff(c_88, plain, (k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')=k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_69])).
% 2.13/1.21  tff(c_39, plain, (![A_15, D_11, E_14, B_12, C_13]: (k11_mcart_1(A_15, B_12, C_13, D_11, E_14)=k2_mcart_1(E_14) | ~m1_subset_1(E_14, k4_zfmisc_1(A_15, B_12, C_13, D_11)) | k1_xboole_0=D_11 | k1_xboole_0=C_13 | k1_xboole_0=B_12 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.13/1.21  tff(c_45, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_16, c_39])).
% 2.13/1.21  tff(c_51, plain, (k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')=k2_mcart_1('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_26, c_45])).
% 2.13/1.21  tff(c_42, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_33, c_39])).
% 2.13/1.21  tff(c_48, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')=k2_mcart_1('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_18, c_42])).
% 2.13/1.21  tff(c_10, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')!=k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')!=k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')!=k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')!=k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.13/1.21  tff(c_34, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')!=k11_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')!=k10_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')!=k9_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')!=k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_12, c_12, c_10])).
% 2.13/1.21  tff(c_131, plain, (k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')!=k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_88, c_51, c_48, c_34])).
% 2.13/1.21  tff(c_110, plain, (![B_27, E_29, A_30, D_26, C_28]: (k8_mcart_1(A_30, B_27, C_28, D_26, E_29)=k1_mcart_1(k1_mcart_1(k1_mcart_1(E_29))) | ~m1_subset_1(E_29, k4_zfmisc_1(A_30, B_27, C_28, D_26)) | k1_xboole_0=D_26 | k1_xboole_0=C_28 | k1_xboole_0=B_27 | k1_xboole_0=A_30)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.13/1.21  tff(c_114, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))=k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_16, c_110])).
% 2.13/1.21  tff(c_120, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))=k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_26, c_114])).
% 2.13/1.21  tff(c_112, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))=k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_33, c_110])).
% 2.13/1.21  tff(c_117, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_9')))=k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_24, c_22, c_20, c_18, c_112])).
% 2.13/1.21  tff(c_125, plain, (k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9')=k8_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_117])).
% 2.13/1.21  tff(c_132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131, c_125])).
% 2.13/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.21  
% 2.13/1.21  Inference rules
% 2.13/1.21  ----------------------
% 2.13/1.21  #Ref     : 0
% 2.13/1.21  #Sup     : 30
% 2.13/1.21  #Fact    : 0
% 2.13/1.21  #Define  : 0
% 2.13/1.21  #Split   : 0
% 2.13/1.21  #Chain   : 0
% 2.13/1.21  #Close   : 0
% 2.13/1.21  
% 2.13/1.21  Ordering : KBO
% 2.13/1.21  
% 2.13/1.21  Simplification rules
% 2.13/1.21  ----------------------
% 2.13/1.21  #Subsume      : 0
% 2.13/1.21  #Demod        : 12
% 2.13/1.21  #Tautology    : 22
% 2.13/1.21  #SimpNegUnit  : 9
% 2.13/1.21  #BackRed      : 3
% 2.13/1.21  
% 2.13/1.21  #Partial instantiations: 0
% 2.13/1.21  #Strategies tried      : 1
% 2.13/1.21  
% 2.13/1.21  Timing (in seconds)
% 2.13/1.21  ----------------------
% 2.13/1.21  Preprocessing        : 0.31
% 2.13/1.21  Parsing              : 0.17
% 2.13/1.21  CNF conversion       : 0.02
% 2.13/1.21  Main loop            : 0.14
% 2.13/1.21  Inferencing          : 0.05
% 2.13/1.21  Reduction            : 0.05
% 2.13/1.21  Demodulation         : 0.04
% 2.13/1.21  BG Simplification    : 0.01
% 2.13/1.21  Subsumption          : 0.01
% 2.13/1.21  Abstraction          : 0.01
% 2.13/1.21  MUC search           : 0.00
% 2.13/1.21  Cooper               : 0.00
% 2.13/1.21  Total                : 0.48
% 2.13/1.21  Index Insertion      : 0.00
% 2.13/1.21  Index Deletion       : 0.00
% 2.13/1.21  Index Matching       : 0.00
% 2.13/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
