%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:43 EST 2020

% Result     : Theorem 6.39s
% Output     : CNFRefutation 6.39s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 126 expanded)
%              Number of leaves         :   33 (  59 expanded)
%              Depth                    :    9
%              Number of atoms          :  131 ( 308 expanded)
%              Number of equality atoms :  105 ( 242 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_42,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_118,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & ~ ! [D] :
                ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
               => ( D != k5_mcart_1(A,B,C,D)
                  & D != k6_mcart_1(A,B,C,D)
                  & D != k7_mcart_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

tff(f_74,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_24,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_85,plain,(
    ! [A_52,B_53] : ~ r2_hidden(A_52,k2_zfmisc_1(A_52,B_53)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_88,plain,(
    ! [A_9] : ~ r2_hidden(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_85])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_52,plain,(
    m1_subset_1('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_3998,plain,(
    ! [A_6611,B_6612,C_6613] : k4_tarski(k4_tarski(A_6611,B_6612),C_6613) = k3_mcart_1(A_6611,B_6612,C_6613) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_48,plain,(
    ! [A_43,B_44] : k2_mcart_1(k4_tarski(A_43,B_44)) = B_44 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_34,plain,(
    ! [B_22,C_23] : k2_mcart_1(k4_tarski(B_22,C_23)) != k4_tarski(B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_60,plain,(
    ! [B_22,C_23] : k4_tarski(B_22,C_23) != C_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_34])).

tff(c_4013,plain,(
    ! [A_6611,B_6612,C_6613] : k3_mcart_1(A_6611,B_6612,C_6613) != C_6613 ),
    inference(superposition,[status(thm),theory(equality)],[c_3998,c_60])).

tff(c_50,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7'
    | k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7'
    | k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_156,plain,(
    k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_3645,plain,(
    ! [A_6276,B_6277,C_6278,D_6279] :
      ( k3_mcart_1(k5_mcart_1(A_6276,B_6277,C_6278,D_6279),k6_mcart_1(A_6276,B_6277,C_6278,D_6279),k7_mcart_1(A_6276,B_6277,C_6278,D_6279)) = D_6279
      | ~ m1_subset_1(D_6279,k3_zfmisc_1(A_6276,B_6277,C_6278))
      | k1_xboole_0 = C_6278
      | k1_xboole_0 = B_6277
      | k1_xboole_0 = A_6276 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3694,plain,
    ( k3_mcart_1('#skF_7',k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7')) = '#skF_7'
    | ~ m1_subset_1('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_3645])).

tff(c_3698,plain,
    ( k3_mcart_1('#skF_7',k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7')) = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_3694])).

tff(c_3699,plain,(
    k3_mcart_1('#skF_7',k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7')) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_56,c_54,c_3698])).

tff(c_38,plain,(
    ! [A_24] :
      ( r2_hidden('#skF_3'(A_24),A_24)
      | k1_xboole_0 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_140,plain,(
    ! [D_68,B_69,A_70] :
      ( D_68 = B_69
      | D_68 = A_70
      | ~ r2_hidden(D_68,k2_tarski(A_70,B_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_151,plain,(
    ! [A_70,B_69] :
      ( '#skF_3'(k2_tarski(A_70,B_69)) = B_69
      | '#skF_3'(k2_tarski(A_70,B_69)) = A_70
      | k2_tarski(A_70,B_69) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_38,c_140])).

tff(c_1226,plain,(
    ! [B_1902] :
      ( k2_tarski(B_1902,B_1902) = k1_xboole_0
      | '#skF_3'(k2_tarski(B_1902,B_1902)) = B_1902 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_151])).

tff(c_4,plain,(
    ! [D_6,A_1] : r2_hidden(D_6,k2_tarski(A_1,D_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_325,plain,(
    ! [C_105,A_106,D_107,E_108] :
      ( ~ r2_hidden(C_105,A_106)
      | k3_mcart_1(C_105,D_107,E_108) != '#skF_3'(A_106)
      | k1_xboole_0 = A_106 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_333,plain,(
    ! [D_6,D_107,E_108,A_1] :
      ( k3_mcart_1(D_6,D_107,E_108) != '#skF_3'(k2_tarski(A_1,D_6))
      | k2_tarski(A_1,D_6) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_325])).

tff(c_1250,plain,(
    ! [B_1902,D_107,E_108] :
      ( k3_mcart_1(B_1902,D_107,E_108) != B_1902
      | k2_tarski(B_1902,B_1902) = k1_xboole_0
      | k2_tarski(B_1902,B_1902) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1226,c_333])).

tff(c_3740,plain,(
    k2_tarski('#skF_7','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3699,c_1250])).

tff(c_3778,plain,(
    r2_hidden('#skF_7',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3740,c_4])).

tff(c_3930,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_3778])).

tff(c_3931,plain,
    ( k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7'
    | k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_3933,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_3931])).

tff(c_7425,plain,(
    ! [A_12868,B_12869,C_12870,D_12871] :
      ( k3_mcart_1(k5_mcart_1(A_12868,B_12869,C_12870,D_12871),k6_mcart_1(A_12868,B_12869,C_12870,D_12871),k7_mcart_1(A_12868,B_12869,C_12870,D_12871)) = D_12871
      | ~ m1_subset_1(D_12871,k3_zfmisc_1(A_12868,B_12869,C_12870))
      | k1_xboole_0 = C_12870
      | k1_xboole_0 = B_12869
      | k1_xboole_0 = A_12868 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_7474,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_7') = '#skF_7'
    | ~ m1_subset_1('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3933,c_7425])).

tff(c_7478,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_7') = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_7474])).

tff(c_7480,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_56,c_54,c_4013,c_7478])).

tff(c_7481,plain,(
    k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_3931])).

tff(c_11077,plain,(
    ! [A_19570,B_19571,C_19572,D_19573] :
      ( k3_mcart_1(k5_mcart_1(A_19570,B_19571,C_19572,D_19573),k6_mcart_1(A_19570,B_19571,C_19572,D_19573),k7_mcart_1(A_19570,B_19571,C_19572,D_19573)) = D_19573
      | ~ m1_subset_1(D_19573,k3_zfmisc_1(A_19570,B_19571,C_19572))
      | k1_xboole_0 = C_19572
      | k1_xboole_0 = B_19571
      | k1_xboole_0 = A_19570 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_11126,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_7',k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7')) = '#skF_7'
    | ~ m1_subset_1('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_7481,c_11077])).

tff(c_11130,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_7',k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7')) = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_11126])).

tff(c_11131,plain,(
    k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_7',k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7')) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_56,c_54,c_11130])).

tff(c_7914,plain,(
    ! [B_13067] :
      ( k2_tarski(B_13067,B_13067) = k1_xboole_0
      | '#skF_3'(k2_tarski(B_13067,B_13067)) = B_13067 ) ),
    inference(factorization,[status(thm),theory(equality)],[c_151])).

tff(c_7598,plain,(
    ! [D_12995,A_12996,C_12997,E_12998] :
      ( ~ r2_hidden(D_12995,A_12996)
      | k3_mcart_1(C_12997,D_12995,E_12998) != '#skF_3'(A_12996)
      | k1_xboole_0 = A_12996 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_7606,plain,(
    ! [C_12997,D_6,E_12998,A_1] :
      ( k3_mcart_1(C_12997,D_6,E_12998) != '#skF_3'(k2_tarski(A_1,D_6))
      | k2_tarski(A_1,D_6) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_7598])).

tff(c_7929,plain,(
    ! [C_12997,B_13067,E_12998] :
      ( k3_mcart_1(C_12997,B_13067,E_12998) != B_13067
      | k2_tarski(B_13067,B_13067) = k1_xboole_0
      | k2_tarski(B_13067,B_13067) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7914,c_7606])).

tff(c_11172,plain,(
    k2_tarski('#skF_7','#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_11131,c_7929])).

tff(c_11210,plain,(
    r2_hidden('#skF_7',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_11172,c_4])).

tff(c_11362,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_11210])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:59:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.39/2.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.39/2.36  
% 6.39/2.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.39/2.36  %$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 6.39/2.36  
% 6.39/2.36  %Foreground sorts:
% 6.39/2.36  
% 6.39/2.36  
% 6.39/2.36  %Background operators:
% 6.39/2.36  
% 6.39/2.36  
% 6.39/2.36  %Foreground operators:
% 6.39/2.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.39/2.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.39/2.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.39/2.36  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.39/2.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.39/2.36  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 6.39/2.36  tff('#skF_7', type, '#skF_7': $i).
% 6.39/2.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.39/2.36  tff('#skF_5', type, '#skF_5': $i).
% 6.39/2.36  tff('#skF_6', type, '#skF_6': $i).
% 6.39/2.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.39/2.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.39/2.36  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 6.39/2.36  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 6.39/2.36  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 6.39/2.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.39/2.36  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 6.39/2.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.39/2.36  tff('#skF_4', type, '#skF_4': $i).
% 6.39/2.36  tff('#skF_3', type, '#skF_3': $i > $i).
% 6.39/2.36  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 6.39/2.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.39/2.36  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 6.39/2.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.39/2.36  
% 6.39/2.38  tff(f_42, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.39/2.38  tff(f_45, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 6.39/2.38  tff(f_118, negated_conjecture, ~(![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ((~(D = k5_mcart_1(A, B, C, D)) & ~(D = k6_mcart_1(A, B, C, D))) & ~(D = k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_mcart_1)).
% 6.39/2.38  tff(f_47, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 6.39/2.38  tff(f_94, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 6.39/2.38  tff(f_58, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 6.39/2.38  tff(f_90, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_mcart_1)).
% 6.39/2.38  tff(f_74, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_mcart_1)).
% 6.39/2.38  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 6.39/2.38  tff(c_24, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.39/2.38  tff(c_85, plain, (![A_52, B_53]: (~r2_hidden(A_52, k2_zfmisc_1(A_52, B_53)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.39/2.38  tff(c_88, plain, (![A_9]: (~r2_hidden(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_85])).
% 6.39/2.38  tff(c_58, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.39/2.38  tff(c_56, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.39/2.38  tff(c_54, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.39/2.38  tff(c_52, plain, (m1_subset_1('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.39/2.38  tff(c_3998, plain, (![A_6611, B_6612, C_6613]: (k4_tarski(k4_tarski(A_6611, B_6612), C_6613)=k3_mcart_1(A_6611, B_6612, C_6613))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.39/2.38  tff(c_48, plain, (![A_43, B_44]: (k2_mcart_1(k4_tarski(A_43, B_44))=B_44)), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.39/2.38  tff(c_34, plain, (![B_22, C_23]: (k2_mcart_1(k4_tarski(B_22, C_23))!=k4_tarski(B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.39/2.38  tff(c_60, plain, (![B_22, C_23]: (k4_tarski(B_22, C_23)!=C_23)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_34])).
% 6.39/2.38  tff(c_4013, plain, (![A_6611, B_6612, C_6613]: (k3_mcart_1(A_6611, B_6612, C_6613)!=C_6613)), inference(superposition, [status(thm), theory('equality')], [c_3998, c_60])).
% 6.39/2.38  tff(c_50, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7' | k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7' | k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(cnfTransformation, [status(thm)], [f_118])).
% 6.39/2.38  tff(c_156, plain, (k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(splitLeft, [status(thm)], [c_50])).
% 6.39/2.38  tff(c_3645, plain, (![A_6276, B_6277, C_6278, D_6279]: (k3_mcart_1(k5_mcart_1(A_6276, B_6277, C_6278, D_6279), k6_mcart_1(A_6276, B_6277, C_6278, D_6279), k7_mcart_1(A_6276, B_6277, C_6278, D_6279))=D_6279 | ~m1_subset_1(D_6279, k3_zfmisc_1(A_6276, B_6277, C_6278)) | k1_xboole_0=C_6278 | k1_xboole_0=B_6277 | k1_xboole_0=A_6276)), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.39/2.38  tff(c_3694, plain, (k3_mcart_1('#skF_7', k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'))='#skF_7' | ~m1_subset_1('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_156, c_3645])).
% 6.39/2.38  tff(c_3698, plain, (k3_mcart_1('#skF_7', k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'))='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_3694])).
% 6.39/2.38  tff(c_3699, plain, (k3_mcart_1('#skF_7', k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'))='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_58, c_56, c_54, c_3698])).
% 6.39/2.38  tff(c_38, plain, (![A_24]: (r2_hidden('#skF_3'(A_24), A_24) | k1_xboole_0=A_24)), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.39/2.38  tff(c_140, plain, (![D_68, B_69, A_70]: (D_68=B_69 | D_68=A_70 | ~r2_hidden(D_68, k2_tarski(A_70, B_69)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.39/2.38  tff(c_151, plain, (![A_70, B_69]: ('#skF_3'(k2_tarski(A_70, B_69))=B_69 | '#skF_3'(k2_tarski(A_70, B_69))=A_70 | k2_tarski(A_70, B_69)=k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_140])).
% 6.39/2.38  tff(c_1226, plain, (![B_1902]: (k2_tarski(B_1902, B_1902)=k1_xboole_0 | '#skF_3'(k2_tarski(B_1902, B_1902))=B_1902)), inference(factorization, [status(thm), theory('equality')], [c_151])).
% 6.39/2.38  tff(c_4, plain, (![D_6, A_1]: (r2_hidden(D_6, k2_tarski(A_1, D_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.39/2.38  tff(c_325, plain, (![C_105, A_106, D_107, E_108]: (~r2_hidden(C_105, A_106) | k3_mcart_1(C_105, D_107, E_108)!='#skF_3'(A_106) | k1_xboole_0=A_106)), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.39/2.38  tff(c_333, plain, (![D_6, D_107, E_108, A_1]: (k3_mcart_1(D_6, D_107, E_108)!='#skF_3'(k2_tarski(A_1, D_6)) | k2_tarski(A_1, D_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_325])).
% 6.39/2.38  tff(c_1250, plain, (![B_1902, D_107, E_108]: (k3_mcart_1(B_1902, D_107, E_108)!=B_1902 | k2_tarski(B_1902, B_1902)=k1_xboole_0 | k2_tarski(B_1902, B_1902)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1226, c_333])).
% 6.39/2.38  tff(c_3740, plain, (k2_tarski('#skF_7', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_3699, c_1250])).
% 6.39/2.38  tff(c_3778, plain, (r2_hidden('#skF_7', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3740, c_4])).
% 6.39/2.38  tff(c_3930, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_3778])).
% 6.39/2.38  tff(c_3931, plain, (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7' | k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(splitRight, [status(thm)], [c_50])).
% 6.39/2.38  tff(c_3933, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(splitLeft, [status(thm)], [c_3931])).
% 6.39/2.38  tff(c_7425, plain, (![A_12868, B_12869, C_12870, D_12871]: (k3_mcart_1(k5_mcart_1(A_12868, B_12869, C_12870, D_12871), k6_mcart_1(A_12868, B_12869, C_12870, D_12871), k7_mcart_1(A_12868, B_12869, C_12870, D_12871))=D_12871 | ~m1_subset_1(D_12871, k3_zfmisc_1(A_12868, B_12869, C_12870)) | k1_xboole_0=C_12870 | k1_xboole_0=B_12869 | k1_xboole_0=A_12868)), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.39/2.38  tff(c_7474, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_7')='#skF_7' | ~m1_subset_1('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3933, c_7425])).
% 6.39/2.38  tff(c_7478, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_7')='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_7474])).
% 6.39/2.38  tff(c_7480, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_56, c_54, c_4013, c_7478])).
% 6.39/2.38  tff(c_7481, plain, (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(splitRight, [status(thm)], [c_3931])).
% 6.39/2.38  tff(c_11077, plain, (![A_19570, B_19571, C_19572, D_19573]: (k3_mcart_1(k5_mcart_1(A_19570, B_19571, C_19572, D_19573), k6_mcart_1(A_19570, B_19571, C_19572, D_19573), k7_mcart_1(A_19570, B_19571, C_19572, D_19573))=D_19573 | ~m1_subset_1(D_19573, k3_zfmisc_1(A_19570, B_19571, C_19572)) | k1_xboole_0=C_19572 | k1_xboole_0=B_19571 | k1_xboole_0=A_19570)), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.39/2.38  tff(c_11126, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_7', k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'))='#skF_7' | ~m1_subset_1('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_7481, c_11077])).
% 6.39/2.38  tff(c_11130, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_7', k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'))='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_11126])).
% 6.39/2.38  tff(c_11131, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_7', k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'))='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_58, c_56, c_54, c_11130])).
% 6.39/2.38  tff(c_7914, plain, (![B_13067]: (k2_tarski(B_13067, B_13067)=k1_xboole_0 | '#skF_3'(k2_tarski(B_13067, B_13067))=B_13067)), inference(factorization, [status(thm), theory('equality')], [c_151])).
% 6.39/2.38  tff(c_7598, plain, (![D_12995, A_12996, C_12997, E_12998]: (~r2_hidden(D_12995, A_12996) | k3_mcart_1(C_12997, D_12995, E_12998)!='#skF_3'(A_12996) | k1_xboole_0=A_12996)), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.39/2.38  tff(c_7606, plain, (![C_12997, D_6, E_12998, A_1]: (k3_mcart_1(C_12997, D_6, E_12998)!='#skF_3'(k2_tarski(A_1, D_6)) | k2_tarski(A_1, D_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_7598])).
% 6.39/2.38  tff(c_7929, plain, (![C_12997, B_13067, E_12998]: (k3_mcart_1(C_12997, B_13067, E_12998)!=B_13067 | k2_tarski(B_13067, B_13067)=k1_xboole_0 | k2_tarski(B_13067, B_13067)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7914, c_7606])).
% 6.39/2.38  tff(c_11172, plain, (k2_tarski('#skF_7', '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_11131, c_7929])).
% 6.39/2.38  tff(c_11210, plain, (r2_hidden('#skF_7', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_11172, c_4])).
% 6.39/2.38  tff(c_11362, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_11210])).
% 6.39/2.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.39/2.38  
% 6.39/2.38  Inference rules
% 6.39/2.38  ----------------------
% 6.39/2.38  #Ref     : 0
% 6.39/2.38  #Sup     : 1174
% 6.39/2.38  #Fact    : 18
% 6.39/2.38  #Define  : 0
% 6.39/2.38  #Split   : 2
% 6.39/2.38  #Chain   : 0
% 6.39/2.38  #Close   : 0
% 6.39/2.38  
% 6.39/2.38  Ordering : KBO
% 6.39/2.38  
% 6.39/2.38  Simplification rules
% 6.39/2.38  ----------------------
% 6.39/2.38  #Subsume      : 218
% 6.39/2.38  #Demod        : 167
% 6.39/2.38  #Tautology    : 284
% 6.39/2.38  #SimpNegUnit  : 40
% 6.39/2.38  #BackRed      : 3
% 6.39/2.38  
% 6.39/2.38  #Partial instantiations: 10260
% 6.39/2.38  #Strategies tried      : 1
% 6.39/2.38  
% 6.39/2.38  Timing (in seconds)
% 6.39/2.38  ----------------------
% 6.39/2.38  Preprocessing        : 0.34
% 6.39/2.38  Parsing              : 0.17
% 6.39/2.38  CNF conversion       : 0.03
% 6.39/2.38  Main loop            : 1.24
% 6.39/2.38  Inferencing          : 0.71
% 6.39/2.38  Reduction            : 0.25
% 6.39/2.38  Demodulation         : 0.17
% 6.39/2.38  BG Simplification    : 0.06
% 6.39/2.38  Subsumption          : 0.16
% 6.39/2.38  Abstraction          : 0.06
% 6.39/2.38  MUC search           : 0.00
% 6.39/2.38  Cooper               : 0.00
% 6.39/2.38  Total                : 1.63
% 6.39/2.38  Index Insertion      : 0.00
% 6.39/2.38  Index Deletion       : 0.00
% 6.39/2.38  Index Matching       : 0.00
% 6.39/2.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
