%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:43 EST 2020

% Result     : Theorem 8.48s
% Output     : CNFRefutation 8.48s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 308 expanded)
%              Number of leaves         :   34 ( 127 expanded)
%              Depth                    :   13
%              Number of atoms          :  189 ( 932 expanded)
%              Number of equality atoms :  157 ( 776 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_114,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_138,negated_conjecture,(
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

tff(f_94,axiom,(
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

tff(f_47,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_98,axiom,(
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

tff(f_74,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

tff(c_24,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_111,plain,(
    ! [A_61,B_62] : ~ r2_hidden(A_61,k2_zfmisc_1(A_61,B_62)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_114,plain,(
    ! [A_9] : ~ r2_hidden(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_111])).

tff(c_50,plain,(
    ! [A_36] :
      ( r2_hidden('#skF_3'(A_36),A_36)
      | k1_xboole_0 = A_36 ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_7674,plain,(
    ! [D_12311,B_12312,A_12313] :
      ( D_12311 = B_12312
      | D_12311 = A_12313
      | ~ r2_hidden(D_12311,k2_tarski(A_12313,B_12312)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_7685,plain,(
    ! [A_12313,B_12312] :
      ( '#skF_3'(k2_tarski(A_12313,B_12312)) = B_12312
      | '#skF_3'(k2_tarski(A_12313,B_12312)) = A_12313
      | k2_tarski(A_12313,B_12312) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_50,c_7674])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_58,plain,(
    m1_subset_1('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_14535,plain,(
    ! [A_24877,B_24878,C_24879,D_24880] :
      ( k7_mcart_1(A_24877,B_24878,C_24879,D_24880) = k2_mcart_1(D_24880)
      | ~ m1_subset_1(D_24880,k3_zfmisc_1(A_24877,B_24878,C_24879))
      | k1_xboole_0 = C_24879
      | k1_xboole_0 = B_24878
      | k1_xboole_0 = A_24877 ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_14552,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = k2_mcart_1('#skF_7')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_58,c_14535])).

tff(c_14558,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = k2_mcart_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_62,c_60,c_14552])).

tff(c_146,plain,(
    ! [A_69,B_70,C_71] : k4_tarski(k4_tarski(A_69,B_70),C_71) = k3_mcart_1(A_69,B_70,C_71) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_48,plain,(
    ! [A_34,B_35] : k2_mcart_1(k4_tarski(A_34,B_35)) = B_35 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_34,plain,(
    ! [B_22,C_23] : k2_mcart_1(k4_tarski(B_22,C_23)) != k4_tarski(B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_66,plain,(
    ! [B_22,C_23] : k4_tarski(B_22,C_23) != C_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_34])).

tff(c_164,plain,(
    ! [A_69,B_70,C_71] : k3_mcart_1(A_69,B_70,C_71) != C_71 ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_66])).

tff(c_3550,plain,(
    ! [A_6156,B_6157,C_6158,D_6159] :
      ( k7_mcart_1(A_6156,B_6157,C_6158,D_6159) = k2_mcart_1(D_6159)
      | ~ m1_subset_1(D_6159,k3_zfmisc_1(A_6156,B_6157,C_6158))
      | k1_xboole_0 = C_6158
      | k1_xboole_0 = B_6157
      | k1_xboole_0 = A_6156 ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3568,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = k2_mcart_1('#skF_7')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_58,c_3550])).

tff(c_3574,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = k2_mcart_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_62,c_60,c_3568])).

tff(c_56,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7'
    | k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7'
    | k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_173,plain,(
    k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_5122,plain,(
    ! [A_9026,B_9027,C_9028,D_9029] :
      ( k3_mcart_1(k5_mcart_1(A_9026,B_9027,C_9028,D_9029),k6_mcart_1(A_9026,B_9027,C_9028,D_9029),k7_mcart_1(A_9026,B_9027,C_9028,D_9029)) = D_9029
      | ~ m1_subset_1(D_9029,k3_zfmisc_1(A_9026,B_9027,C_9028))
      | k1_xboole_0 = C_9028
      | k1_xboole_0 = B_9027
      | k1_xboole_0 = A_9026 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_5176,plain,
    ( k3_mcart_1('#skF_7',k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7')) = '#skF_7'
    | ~ m1_subset_1('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_5122])).

tff(c_5183,plain,
    ( k3_mcart_1('#skF_7',k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k2_mcart_1('#skF_7')) = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_3574,c_5176])).

tff(c_5184,plain,(
    k3_mcart_1('#skF_7',k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k2_mcart_1('#skF_7')) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_62,c_60,c_5183])).

tff(c_46,plain,(
    ! [A_34,B_35] : k1_mcart_1(k4_tarski(A_34,B_35)) = A_34 ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_158,plain,(
    ! [A_69,B_70,C_71] : k1_mcart_1(k3_mcart_1(A_69,B_70,C_71)) = k4_tarski(A_69,B_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_46])).

tff(c_5200,plain,(
    k4_tarski('#skF_7',k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7')) = k1_mcart_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_5184,c_158])).

tff(c_258,plain,(
    ! [D_91,B_92,A_93] :
      ( D_91 = B_92
      | D_91 = A_93
      | ~ r2_hidden(D_91,k2_tarski(A_93,B_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1062,plain,(
    ! [A_1821,B_1822] :
      ( '#skF_3'(k2_tarski(A_1821,B_1822)) = B_1822
      | '#skF_3'(k2_tarski(A_1821,B_1822)) = A_1821
      | k2_tarski(A_1821,B_1822) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_50,c_258])).

tff(c_4,plain,(
    ! [D_6,A_1] : r2_hidden(D_6,k2_tarski(A_1,D_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_330,plain,(
    ! [C_102,A_103,D_104] :
      ( ~ r2_hidden(C_102,A_103)
      | k4_tarski(C_102,D_104) != '#skF_3'(A_103)
      | k1_xboole_0 = A_103 ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_339,plain,(
    ! [D_6,D_104,A_1] :
      ( k4_tarski(D_6,D_104) != '#skF_3'(k2_tarski(A_1,D_6))
      | k2_tarski(A_1,D_6) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_330])).

tff(c_1113,plain,(
    ! [B_1822,D_104,A_1821] :
      ( k4_tarski(B_1822,D_104) != A_1821
      | k2_tarski(A_1821,B_1822) = k1_xboole_0
      | '#skF_3'(k2_tarski(A_1821,B_1822)) = B_1822
      | k2_tarski(A_1821,B_1822) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1062,c_339])).

tff(c_7067,plain,(
    ! [A_12088] :
      ( k1_mcart_1('#skF_7') != A_12088
      | k2_tarski(A_12088,'#skF_7') = k1_xboole_0
      | '#skF_3'(k2_tarski(A_12088,'#skF_7')) = '#skF_7'
      | k2_tarski(A_12088,'#skF_7') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5200,c_1113])).

tff(c_30,plain,(
    ! [A_13,B_14,C_15] : k4_tarski(k4_tarski(A_13,B_14),C_15) = k3_mcart_1(A_13,B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_5783,plain,(
    ! [C_10224] : k3_mcart_1('#skF_7',k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),C_10224) = k4_tarski(k1_mcart_1('#skF_7'),C_10224) ),
    inference(superposition,[status(thm),theory(equality)],[c_5200,c_30])).

tff(c_5789,plain,(
    k4_tarski(k1_mcart_1('#skF_7'),k2_mcart_1('#skF_7')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_5783,c_5184])).

tff(c_6,plain,(
    ! [D_6,B_2] : r2_hidden(D_6,k2_tarski(D_6,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_338,plain,(
    ! [D_6,D_104,B_2] :
      ( k4_tarski(D_6,D_104) != '#skF_3'(k2_tarski(D_6,B_2))
      | k2_tarski(D_6,B_2) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_330])).

tff(c_5873,plain,(
    ! [B_2] :
      ( '#skF_3'(k2_tarski(k1_mcart_1('#skF_7'),B_2)) != '#skF_7'
      | k2_tarski(k1_mcart_1('#skF_7'),B_2) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5789,c_338])).

tff(c_7457,plain,(
    k2_tarski(k1_mcart_1('#skF_7'),'#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7067,c_5873])).

tff(c_7513,plain,(
    r2_hidden(k1_mcart_1('#skF_7'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_7457,c_6])).

tff(c_7661,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_7513])).

tff(c_7662,plain,
    ( k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7'
    | k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_7737,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_7662])).

tff(c_12469,plain,(
    ! [A_21098,B_21099,C_21100,D_21101] :
      ( k3_mcart_1(k5_mcart_1(A_21098,B_21099,C_21100,D_21101),k6_mcart_1(A_21098,B_21099,C_21100,D_21101),k7_mcart_1(A_21098,B_21099,C_21100,D_21101)) = D_21101
      | ~ m1_subset_1(D_21101,k3_zfmisc_1(A_21098,B_21099,C_21100))
      | k1_xboole_0 = C_21100
      | k1_xboole_0 = B_21099
      | k1_xboole_0 = A_21098 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_12520,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_7') = '#skF_7'
    | ~ m1_subset_1('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_7737,c_12469])).

tff(c_12524,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_7') = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_12520])).

tff(c_12526,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_62,c_60,c_164,c_12524])).

tff(c_12527,plain,(
    k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_7662])).

tff(c_16645,plain,(
    ! [A_29389,B_29390,C_29391,D_29392] :
      ( k3_mcart_1(k5_mcart_1(A_29389,B_29390,C_29391,D_29392),k6_mcart_1(A_29389,B_29390,C_29391,D_29392),k7_mcart_1(A_29389,B_29390,C_29391,D_29392)) = D_29392
      | ~ m1_subset_1(D_29392,k3_zfmisc_1(A_29389,B_29390,C_29391))
      | k1_xboole_0 = C_29391
      | k1_xboole_0 = B_29390
      | k1_xboole_0 = A_29389 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_16693,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_7',k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7')) = '#skF_7'
    | ~ m1_subset_1('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_12527,c_16645])).

tff(c_16700,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_7',k2_mcart_1('#skF_7')) = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_14558,c_16693])).

tff(c_16701,plain,(
    k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_7',k2_mcart_1('#skF_7')) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_62,c_60,c_16700])).

tff(c_16711,plain,(
    k4_tarski(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_7') = k1_mcart_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_16701,c_158])).

tff(c_12602,plain,(
    ! [D_21219,A_21220,C_21221] :
      ( ~ r2_hidden(D_21219,A_21220)
      | k4_tarski(C_21221,D_21219) != '#skF_3'(A_21220)
      | k1_xboole_0 = A_21220 ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_12611,plain,(
    ! [C_21221,D_6,A_1] :
      ( k4_tarski(C_21221,D_6) != '#skF_3'(k2_tarski(A_1,D_6))
      | k2_tarski(A_1,D_6) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_12602])).

tff(c_16791,plain,(
    ! [A_29933] :
      ( '#skF_3'(k2_tarski(A_29933,'#skF_7')) != k1_mcart_1('#skF_7')
      | k2_tarski(A_29933,'#skF_7') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16711,c_12611])).

tff(c_18100,plain,(
    ! [A_32454] :
      ( k1_mcart_1('#skF_7') != A_32454
      | k2_tarski(A_32454,'#skF_7') = k1_xboole_0
      | '#skF_3'(k2_tarski(A_32454,'#skF_7')) = '#skF_7'
      | k2_tarski(A_32454,'#skF_7') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7685,c_16791])).

tff(c_17273,plain,(
    ! [C_30479] : k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_7'),'#skF_7',C_30479) = k4_tarski(k1_mcart_1('#skF_7'),C_30479) ),
    inference(superposition,[status(thm),theory(equality)],[c_16711,c_30])).

tff(c_17279,plain,(
    k4_tarski(k1_mcart_1('#skF_7'),k2_mcart_1('#skF_7')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_17273,c_16701])).

tff(c_12612,plain,(
    ! [C_21222,A_21223,D_21224] :
      ( ~ r2_hidden(C_21222,A_21223)
      | k4_tarski(C_21222,D_21224) != '#skF_3'(A_21223)
      | k1_xboole_0 = A_21223 ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_12620,plain,(
    ! [D_6,D_21224,B_2] :
      ( k4_tarski(D_6,D_21224) != '#skF_3'(k2_tarski(D_6,B_2))
      | k2_tarski(D_6,B_2) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_12612])).

tff(c_17356,plain,(
    ! [B_2] :
      ( '#skF_3'(k2_tarski(k1_mcart_1('#skF_7'),B_2)) != '#skF_7'
      | k2_tarski(k1_mcart_1('#skF_7'),B_2) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17279,c_12620])).

tff(c_18490,plain,(
    k2_tarski(k1_mcart_1('#skF_7'),'#skF_7') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18100,c_17356])).

tff(c_18540,plain,(
    r2_hidden(k1_mcart_1('#skF_7'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18490,c_6])).

tff(c_18686,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_18540])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.48/2.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.48/2.91  
% 8.48/2.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.48/2.91  %$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 8.48/2.91  
% 8.48/2.91  %Foreground sorts:
% 8.48/2.91  
% 8.48/2.91  
% 8.48/2.91  %Background operators:
% 8.48/2.91  
% 8.48/2.91  
% 8.48/2.91  %Foreground operators:
% 8.48/2.91  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 8.48/2.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.48/2.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.48/2.91  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.48/2.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.48/2.91  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 8.48/2.91  tff('#skF_7', type, '#skF_7': $i).
% 8.48/2.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.48/2.91  tff('#skF_5', type, '#skF_5': $i).
% 8.48/2.91  tff('#skF_6', type, '#skF_6': $i).
% 8.48/2.91  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.48/2.91  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.48/2.91  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 8.48/2.91  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 8.48/2.91  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 8.48/2.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.48/2.91  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 8.48/2.91  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.48/2.91  tff('#skF_4', type, '#skF_4': $i).
% 8.48/2.91  tff('#skF_3', type, '#skF_3': $i > $i).
% 8.48/2.91  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 8.48/2.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.48/2.91  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 8.48/2.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.48/2.91  
% 8.48/2.93  tff(f_42, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.48/2.93  tff(f_45, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 8.48/2.93  tff(f_114, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 8.48/2.93  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 8.48/2.93  tff(f_138, negated_conjecture, ~(![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ((~(D = k5_mcart_1(A, B, C, D)) & ~(D = k6_mcart_1(A, B, C, D))) & ~(D = k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_mcart_1)).
% 8.48/2.93  tff(f_94, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 8.48/2.93  tff(f_47, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 8.48/2.93  tff(f_98, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 8.48/2.93  tff(f_58, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 8.48/2.93  tff(f_74, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_mcart_1)).
% 8.48/2.93  tff(c_24, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.48/2.93  tff(c_111, plain, (![A_61, B_62]: (~r2_hidden(A_61, k2_zfmisc_1(A_61, B_62)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.48/2.93  tff(c_114, plain, (![A_9]: (~r2_hidden(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_111])).
% 8.48/2.93  tff(c_50, plain, (![A_36]: (r2_hidden('#skF_3'(A_36), A_36) | k1_xboole_0=A_36)), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.48/2.93  tff(c_7674, plain, (![D_12311, B_12312, A_12313]: (D_12311=B_12312 | D_12311=A_12313 | ~r2_hidden(D_12311, k2_tarski(A_12313, B_12312)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.48/2.93  tff(c_7685, plain, (![A_12313, B_12312]: ('#skF_3'(k2_tarski(A_12313, B_12312))=B_12312 | '#skF_3'(k2_tarski(A_12313, B_12312))=A_12313 | k2_tarski(A_12313, B_12312)=k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_7674])).
% 8.48/2.93  tff(c_64, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.48/2.93  tff(c_62, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.48/2.93  tff(c_60, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.48/2.93  tff(c_58, plain, (m1_subset_1('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.48/2.93  tff(c_14535, plain, (![A_24877, B_24878, C_24879, D_24880]: (k7_mcart_1(A_24877, B_24878, C_24879, D_24880)=k2_mcart_1(D_24880) | ~m1_subset_1(D_24880, k3_zfmisc_1(A_24877, B_24878, C_24879)) | k1_xboole_0=C_24879 | k1_xboole_0=B_24878 | k1_xboole_0=A_24877)), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.48/2.93  tff(c_14552, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')=k2_mcart_1('#skF_7') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_58, c_14535])).
% 8.48/2.93  tff(c_14558, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')=k2_mcart_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_64, c_62, c_60, c_14552])).
% 8.48/2.93  tff(c_146, plain, (![A_69, B_70, C_71]: (k4_tarski(k4_tarski(A_69, B_70), C_71)=k3_mcart_1(A_69, B_70, C_71))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.48/2.93  tff(c_48, plain, (![A_34, B_35]: (k2_mcart_1(k4_tarski(A_34, B_35))=B_35)), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.48/2.93  tff(c_34, plain, (![B_22, C_23]: (k2_mcart_1(k4_tarski(B_22, C_23))!=k4_tarski(B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.48/2.93  tff(c_66, plain, (![B_22, C_23]: (k4_tarski(B_22, C_23)!=C_23)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_34])).
% 8.48/2.93  tff(c_164, plain, (![A_69, B_70, C_71]: (k3_mcart_1(A_69, B_70, C_71)!=C_71)), inference(superposition, [status(thm), theory('equality')], [c_146, c_66])).
% 8.48/2.93  tff(c_3550, plain, (![A_6156, B_6157, C_6158, D_6159]: (k7_mcart_1(A_6156, B_6157, C_6158, D_6159)=k2_mcart_1(D_6159) | ~m1_subset_1(D_6159, k3_zfmisc_1(A_6156, B_6157, C_6158)) | k1_xboole_0=C_6158 | k1_xboole_0=B_6157 | k1_xboole_0=A_6156)), inference(cnfTransformation, [status(thm)], [f_94])).
% 8.48/2.93  tff(c_3568, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')=k2_mcart_1('#skF_7') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_58, c_3550])).
% 8.48/2.93  tff(c_3574, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')=k2_mcart_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_64, c_62, c_60, c_3568])).
% 8.48/2.93  tff(c_56, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7' | k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7' | k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(cnfTransformation, [status(thm)], [f_138])).
% 8.48/2.93  tff(c_173, plain, (k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(splitLeft, [status(thm)], [c_56])).
% 8.48/2.93  tff(c_5122, plain, (![A_9026, B_9027, C_9028, D_9029]: (k3_mcart_1(k5_mcart_1(A_9026, B_9027, C_9028, D_9029), k6_mcart_1(A_9026, B_9027, C_9028, D_9029), k7_mcart_1(A_9026, B_9027, C_9028, D_9029))=D_9029 | ~m1_subset_1(D_9029, k3_zfmisc_1(A_9026, B_9027, C_9028)) | k1_xboole_0=C_9028 | k1_xboole_0=B_9027 | k1_xboole_0=A_9026)), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.48/2.93  tff(c_5176, plain, (k3_mcart_1('#skF_7', k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'))='#skF_7' | ~m1_subset_1('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_173, c_5122])).
% 8.48/2.93  tff(c_5183, plain, (k3_mcart_1('#skF_7', k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k2_mcart_1('#skF_7'))='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_3574, c_5176])).
% 8.48/2.93  tff(c_5184, plain, (k3_mcart_1('#skF_7', k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k2_mcart_1('#skF_7'))='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_64, c_62, c_60, c_5183])).
% 8.48/2.93  tff(c_46, plain, (![A_34, B_35]: (k1_mcart_1(k4_tarski(A_34, B_35))=A_34)), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.48/2.93  tff(c_158, plain, (![A_69, B_70, C_71]: (k1_mcart_1(k3_mcart_1(A_69, B_70, C_71))=k4_tarski(A_69, B_70))), inference(superposition, [status(thm), theory('equality')], [c_146, c_46])).
% 8.48/2.93  tff(c_5200, plain, (k4_tarski('#skF_7', k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'))=k1_mcart_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_5184, c_158])).
% 8.48/2.93  tff(c_258, plain, (![D_91, B_92, A_93]: (D_91=B_92 | D_91=A_93 | ~r2_hidden(D_91, k2_tarski(A_93, B_92)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.48/2.93  tff(c_1062, plain, (![A_1821, B_1822]: ('#skF_3'(k2_tarski(A_1821, B_1822))=B_1822 | '#skF_3'(k2_tarski(A_1821, B_1822))=A_1821 | k2_tarski(A_1821, B_1822)=k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_258])).
% 8.48/2.93  tff(c_4, plain, (![D_6, A_1]: (r2_hidden(D_6, k2_tarski(A_1, D_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.48/2.93  tff(c_330, plain, (![C_102, A_103, D_104]: (~r2_hidden(C_102, A_103) | k4_tarski(C_102, D_104)!='#skF_3'(A_103) | k1_xboole_0=A_103)), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.48/2.93  tff(c_339, plain, (![D_6, D_104, A_1]: (k4_tarski(D_6, D_104)!='#skF_3'(k2_tarski(A_1, D_6)) | k2_tarski(A_1, D_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_330])).
% 8.48/2.93  tff(c_1113, plain, (![B_1822, D_104, A_1821]: (k4_tarski(B_1822, D_104)!=A_1821 | k2_tarski(A_1821, B_1822)=k1_xboole_0 | '#skF_3'(k2_tarski(A_1821, B_1822))=B_1822 | k2_tarski(A_1821, B_1822)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1062, c_339])).
% 8.48/2.93  tff(c_7067, plain, (![A_12088]: (k1_mcart_1('#skF_7')!=A_12088 | k2_tarski(A_12088, '#skF_7')=k1_xboole_0 | '#skF_3'(k2_tarski(A_12088, '#skF_7'))='#skF_7' | k2_tarski(A_12088, '#skF_7')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5200, c_1113])).
% 8.48/2.93  tff(c_30, plain, (![A_13, B_14, C_15]: (k4_tarski(k4_tarski(A_13, B_14), C_15)=k3_mcart_1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.48/2.93  tff(c_5783, plain, (![C_10224]: (k3_mcart_1('#skF_7', k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), C_10224)=k4_tarski(k1_mcart_1('#skF_7'), C_10224))), inference(superposition, [status(thm), theory('equality')], [c_5200, c_30])).
% 8.48/2.93  tff(c_5789, plain, (k4_tarski(k1_mcart_1('#skF_7'), k2_mcart_1('#skF_7'))='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_5783, c_5184])).
% 8.48/2.93  tff(c_6, plain, (![D_6, B_2]: (r2_hidden(D_6, k2_tarski(D_6, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 8.48/2.93  tff(c_338, plain, (![D_6, D_104, B_2]: (k4_tarski(D_6, D_104)!='#skF_3'(k2_tarski(D_6, B_2)) | k2_tarski(D_6, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_330])).
% 8.48/2.93  tff(c_5873, plain, (![B_2]: ('#skF_3'(k2_tarski(k1_mcart_1('#skF_7'), B_2))!='#skF_7' | k2_tarski(k1_mcart_1('#skF_7'), B_2)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5789, c_338])).
% 8.48/2.93  tff(c_7457, plain, (k2_tarski(k1_mcart_1('#skF_7'), '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7067, c_5873])).
% 8.48/2.93  tff(c_7513, plain, (r2_hidden(k1_mcart_1('#skF_7'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7457, c_6])).
% 8.48/2.93  tff(c_7661, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_7513])).
% 8.48/2.93  tff(c_7662, plain, (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7' | k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(splitRight, [status(thm)], [c_56])).
% 8.48/2.93  tff(c_7737, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(splitLeft, [status(thm)], [c_7662])).
% 8.48/2.93  tff(c_12469, plain, (![A_21098, B_21099, C_21100, D_21101]: (k3_mcart_1(k5_mcart_1(A_21098, B_21099, C_21100, D_21101), k6_mcart_1(A_21098, B_21099, C_21100, D_21101), k7_mcart_1(A_21098, B_21099, C_21100, D_21101))=D_21101 | ~m1_subset_1(D_21101, k3_zfmisc_1(A_21098, B_21099, C_21100)) | k1_xboole_0=C_21100 | k1_xboole_0=B_21099 | k1_xboole_0=A_21098)), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.48/2.93  tff(c_12520, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_7')='#skF_7' | ~m1_subset_1('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_7737, c_12469])).
% 8.48/2.93  tff(c_12524, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_7')='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_12520])).
% 8.48/2.93  tff(c_12526, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_62, c_60, c_164, c_12524])).
% 8.48/2.93  tff(c_12527, plain, (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')='#skF_7'), inference(splitRight, [status(thm)], [c_7662])).
% 8.48/2.93  tff(c_16645, plain, (![A_29389, B_29390, C_29391, D_29392]: (k3_mcart_1(k5_mcart_1(A_29389, B_29390, C_29391, D_29392), k6_mcart_1(A_29389, B_29390, C_29391, D_29392), k7_mcart_1(A_29389, B_29390, C_29391, D_29392))=D_29392 | ~m1_subset_1(D_29392, k3_zfmisc_1(A_29389, B_29390, C_29391)) | k1_xboole_0=C_29391 | k1_xboole_0=B_29390 | k1_xboole_0=A_29389)), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.48/2.93  tff(c_16693, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_7', k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'))='#skF_7' | ~m1_subset_1('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_12527, c_16645])).
% 8.48/2.93  tff(c_16700, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_7', k2_mcart_1('#skF_7'))='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_14558, c_16693])).
% 8.48/2.93  tff(c_16701, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_7', k2_mcart_1('#skF_7'))='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_64, c_62, c_60, c_16700])).
% 8.48/2.93  tff(c_16711, plain, (k4_tarski(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_7')=k1_mcart_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_16701, c_158])).
% 8.48/2.93  tff(c_12602, plain, (![D_21219, A_21220, C_21221]: (~r2_hidden(D_21219, A_21220) | k4_tarski(C_21221, D_21219)!='#skF_3'(A_21220) | k1_xboole_0=A_21220)), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.48/2.93  tff(c_12611, plain, (![C_21221, D_6, A_1]: (k4_tarski(C_21221, D_6)!='#skF_3'(k2_tarski(A_1, D_6)) | k2_tarski(A_1, D_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_12602])).
% 8.48/2.93  tff(c_16791, plain, (![A_29933]: ('#skF_3'(k2_tarski(A_29933, '#skF_7'))!=k1_mcart_1('#skF_7') | k2_tarski(A_29933, '#skF_7')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16711, c_12611])).
% 8.48/2.93  tff(c_18100, plain, (![A_32454]: (k1_mcart_1('#skF_7')!=A_32454 | k2_tarski(A_32454, '#skF_7')=k1_xboole_0 | '#skF_3'(k2_tarski(A_32454, '#skF_7'))='#skF_7' | k2_tarski(A_32454, '#skF_7')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_7685, c_16791])).
% 8.48/2.93  tff(c_17273, plain, (![C_30479]: (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_7'), '#skF_7', C_30479)=k4_tarski(k1_mcart_1('#skF_7'), C_30479))), inference(superposition, [status(thm), theory('equality')], [c_16711, c_30])).
% 8.48/2.93  tff(c_17279, plain, (k4_tarski(k1_mcart_1('#skF_7'), k2_mcart_1('#skF_7'))='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_17273, c_16701])).
% 8.48/2.93  tff(c_12612, plain, (![C_21222, A_21223, D_21224]: (~r2_hidden(C_21222, A_21223) | k4_tarski(C_21222, D_21224)!='#skF_3'(A_21223) | k1_xboole_0=A_21223)), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.48/2.93  tff(c_12620, plain, (![D_6, D_21224, B_2]: (k4_tarski(D_6, D_21224)!='#skF_3'(k2_tarski(D_6, B_2)) | k2_tarski(D_6, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_12612])).
% 8.48/2.93  tff(c_17356, plain, (![B_2]: ('#skF_3'(k2_tarski(k1_mcart_1('#skF_7'), B_2))!='#skF_7' | k2_tarski(k1_mcart_1('#skF_7'), B_2)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_17279, c_12620])).
% 8.48/2.93  tff(c_18490, plain, (k2_tarski(k1_mcart_1('#skF_7'), '#skF_7')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_18100, c_17356])).
% 8.48/2.93  tff(c_18540, plain, (r2_hidden(k1_mcart_1('#skF_7'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18490, c_6])).
% 8.48/2.93  tff(c_18686, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_18540])).
% 8.48/2.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.48/2.93  
% 8.48/2.93  Inference rules
% 8.48/2.93  ----------------------
% 8.48/2.93  #Ref     : 2
% 8.48/2.93  #Sup     : 2190
% 8.48/2.93  #Fact    : 44
% 8.48/2.93  #Define  : 0
% 8.48/2.93  #Split   : 8
% 8.48/2.93  #Chain   : 0
% 8.48/2.93  #Close   : 0
% 8.48/2.93  
% 8.48/2.93  Ordering : KBO
% 8.48/2.93  
% 8.48/2.93  Simplification rules
% 8.48/2.93  ----------------------
% 8.48/2.93  #Subsume      : 645
% 8.48/2.93  #Demod        : 307
% 8.48/2.93  #Tautology    : 579
% 8.48/2.93  #SimpNegUnit  : 129
% 8.48/2.93  #BackRed      : 4
% 8.48/2.93  
% 8.48/2.93  #Partial instantiations: 16910
% 8.48/2.93  #Strategies tried      : 1
% 8.48/2.93  
% 8.48/2.93  Timing (in seconds)
% 8.48/2.93  ----------------------
% 8.65/2.93  Preprocessing        : 0.35
% 8.65/2.93  Parsing              : 0.18
% 8.65/2.93  CNF conversion       : 0.03
% 8.65/2.93  Main loop            : 1.80
% 8.65/2.93  Inferencing          : 1.00
% 8.65/2.93  Reduction            : 0.38
% 8.65/2.93  Demodulation         : 0.25
% 8.65/2.93  BG Simplification    : 0.08
% 8.65/2.93  Subsumption          : 0.25
% 8.65/2.93  Abstraction          : 0.09
% 8.65/2.93  MUC search           : 0.00
% 8.65/2.93  Cooper               : 0.00
% 8.65/2.93  Total                : 2.19
% 8.65/2.93  Index Insertion      : 0.00
% 8.65/2.93  Index Deletion       : 0.00
% 8.65/2.93  Index Matching       : 0.00
% 8.65/2.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
