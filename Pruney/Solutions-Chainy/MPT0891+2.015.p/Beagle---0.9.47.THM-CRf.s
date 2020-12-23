%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:42 EST 2020

% Result     : Theorem 12.98s
% Output     : CNFRefutation 12.98s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 202 expanded)
%              Number of leaves         :   35 (  87 expanded)
%              Depth                    :   10
%              Number of atoms          :  144 ( 498 expanded)
%              Number of equality atoms :  108 ( 311 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & ~ ! [D] :
                ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
               => ( D != k5_mcart_1(A,B,C,D)
                  & D != k6_mcart_1(A,B,C,D)
                  & D != k7_mcart_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_mcart_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_76,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_22,plain,(
    ! [C_11] : r2_hidden(C_11,k1_tarski(C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_44,plain,(
    ! [A_25] :
      ( r2_hidden('#skF_5'(A_25),A_25)
      | k1_xboole_0 = A_25 ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_137,plain,(
    ! [D_67,A_68,B_69] :
      ( r2_hidden(D_67,A_68)
      | ~ r2_hidden(D_67,k4_xboole_0(A_68,B_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_145,plain,(
    ! [A_68,B_69] :
      ( r2_hidden('#skF_5'(k4_xboole_0(A_68,B_69)),A_68)
      | k4_xboole_0(A_68,B_69) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_44,c_137])).

tff(c_128,plain,(
    ! [D_64,B_65,A_66] :
      ( ~ r2_hidden(D_64,B_65)
      | ~ r2_hidden(D_64,k4_xboole_0(A_66,B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_35967,plain,(
    ! [A_108349,B_108350] :
      ( ~ r2_hidden('#skF_5'(k4_xboole_0(A_108349,B_108350)),B_108350)
      | k4_xboole_0(A_108349,B_108350) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_44,c_128])).

tff(c_35981,plain,(
    ! [A_108351] : k4_xboole_0(A_108351,A_108351) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_145,c_35967])).

tff(c_32,plain,(
    ! [B_13,A_12] :
      ( ~ r2_hidden(B_13,A_12)
      | k4_xboole_0(A_12,k1_tarski(B_13)) != A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_36002,plain,(
    ! [B_13] :
      ( ~ r2_hidden(B_13,k1_tarski(B_13))
      | k1_tarski(B_13) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_35981,c_32])).

tff(c_36017,plain,(
    ! [B_13] : k1_tarski(B_13) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_36002])).

tff(c_89,plain,(
    ! [C_57,A_58] :
      ( C_57 = A_58
      | ~ r2_hidden(C_57,k1_tarski(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_97,plain,(
    ! [A_58] :
      ( '#skF_5'(k1_tarski(A_58)) = A_58
      | k1_tarski(A_58) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_44,c_89])).

tff(c_36021,plain,(
    ! [A_58] : '#skF_5'(k1_tarski(A_58)) = A_58 ),
    inference(negUnitSimplification,[status(thm)],[c_36017,c_97])).

tff(c_36481,plain,(
    ! [D_109811,A_109812,C_109813,E_109814] :
      ( ~ r2_hidden(D_109811,A_109812)
      | k3_mcart_1(C_109813,D_109811,E_109814) != '#skF_5'(A_109812)
      | k1_xboole_0 = A_109812 ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_36489,plain,(
    ! [C_109813,C_11,E_109814] :
      ( k3_mcart_1(C_109813,C_11,E_109814) != '#skF_5'(k1_tarski(C_11))
      | k1_tarski(C_11) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_36481])).

tff(c_36494,plain,(
    ! [C_109813,C_11,E_109814] :
      ( k3_mcart_1(C_109813,C_11,E_109814) != C_11
      | k1_tarski(C_11) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36021,c_36489])).

tff(c_36495,plain,(
    ! [C_109813,C_11,E_109814] : k3_mcart_1(C_109813,C_11,E_109814) != C_11 ),
    inference(negUnitSimplification,[status(thm)],[c_36017,c_36494])).

tff(c_58,plain,(
    m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_161,plain,(
    ! [A_73,B_74,C_75] : k4_tarski(k4_tarski(A_73,B_74),C_75) = k3_mcart_1(A_73,B_74,C_75) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_54,plain,(
    ! [A_44,B_45] : k2_mcart_1(k4_tarski(A_44,B_45)) = B_45 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_40,plain,(
    ! [B_23,C_24] : k2_mcart_1(k4_tarski(B_23,C_24)) != k4_tarski(B_23,C_24) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_66,plain,(
    ! [B_23,C_24] : k4_tarski(B_23,C_24) != C_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_40])).

tff(c_176,plain,(
    ! [A_73,B_74,C_75] : k3_mcart_1(A_73,B_74,C_75) != C_75 ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_66])).

tff(c_228,plain,(
    ! [A_97,B_98] :
      ( r2_hidden('#skF_5'(k4_xboole_0(A_97,B_98)),A_97)
      | k4_xboole_0(A_97,B_98) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_44,c_137])).

tff(c_136,plain,(
    ! [A_66,B_65] :
      ( ~ r2_hidden('#skF_5'(k4_xboole_0(A_66,B_65)),B_65)
      | k4_xboole_0(A_66,B_65) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_44,c_128])).

tff(c_255,plain,(
    ! [A_99] : k4_xboole_0(A_99,A_99) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_228,c_136])).

tff(c_273,plain,(
    ! [B_13] :
      ( ~ r2_hidden(B_13,k1_tarski(B_13))
      | k1_tarski(B_13) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_32])).

tff(c_288,plain,(
    ! [B_13] : k1_tarski(B_13) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_273])).

tff(c_655,plain,(
    ! [A_58] : '#skF_5'(k1_tarski(A_58)) = A_58 ),
    inference(negUnitSimplification,[status(thm)],[c_288,c_97])).

tff(c_660,plain,(
    ! [A_1332] : '#skF_5'(k1_tarski(A_1332)) = A_1332 ),
    inference(negUnitSimplification,[status(thm)],[c_288,c_97])).

tff(c_217,plain,(
    ! [C_90,A_91,D_92,E_93] :
      ( ~ r2_hidden(C_90,A_91)
      | k3_mcart_1(C_90,D_92,E_93) != '#skF_5'(A_91)
      | k1_xboole_0 = A_91 ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_222,plain,(
    ! [A_25,D_92,E_93] :
      ( k3_mcart_1('#skF_5'(A_25),D_92,E_93) != '#skF_5'(A_25)
      | k1_xboole_0 = A_25 ) ),
    inference(resolution,[status(thm)],[c_44,c_217])).

tff(c_666,plain,(
    ! [A_1332,D_92,E_93] :
      ( k3_mcart_1(A_1332,D_92,E_93) != '#skF_5'(k1_tarski(A_1332))
      | k1_tarski(A_1332) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_660,c_222])).

tff(c_733,plain,(
    ! [A_1332,D_92,E_93] :
      ( k3_mcart_1(A_1332,D_92,E_93) != A_1332
      | k1_tarski(A_1332) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_655,c_666])).

tff(c_734,plain,(
    ! [A_1332,D_92,E_93] : k3_mcart_1(A_1332,D_92,E_93) != A_1332 ),
    inference(negUnitSimplification,[status(thm)],[c_288,c_733])).

tff(c_56,plain,
    ( k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9'
    | k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9'
    | k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_189,plain,(
    k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_15058,plain,(
    ! [A_45043,B_45044,C_45045,D_45046] :
      ( k3_mcart_1(k5_mcart_1(A_45043,B_45044,C_45045,D_45046),k6_mcart_1(A_45043,B_45044,C_45045,D_45046),k7_mcart_1(A_45043,B_45044,C_45045,D_45046)) = D_45046
      | ~ m1_subset_1(D_45046,k3_zfmisc_1(A_45043,B_45044,C_45045))
      | k1_xboole_0 = C_45045
      | k1_xboole_0 = B_45044
      | k1_xboole_0 = A_45043 ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_15200,plain,
    ( k3_mcart_1('#skF_9',k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9')) = '#skF_9'
    | ~ m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_15058])).

tff(c_15204,plain,
    ( k3_mcart_1('#skF_9',k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9')) = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_15200])).

tff(c_15206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_62,c_60,c_734,c_15204])).

tff(c_15207,plain,
    ( k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9'
    | k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_15219,plain,(
    k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_15207])).

tff(c_35721,plain,(
    ! [A_107802,B_107803,C_107804,D_107805] :
      ( k3_mcart_1(k5_mcart_1(A_107802,B_107803,C_107804,D_107805),k6_mcart_1(A_107802,B_107803,C_107804,D_107805),k7_mcart_1(A_107802,B_107803,C_107804,D_107805)) = D_107805
      | ~ m1_subset_1(D_107805,k3_zfmisc_1(A_107802,B_107803,C_107804))
      | k1_xboole_0 = C_107804
      | k1_xboole_0 = B_107803
      | k1_xboole_0 = A_107802 ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_35902,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9') = '#skF_9'
    | ~ m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_15219,c_35721])).

tff(c_35906,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9') = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_35902])).

tff(c_35908,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_62,c_60,c_176,c_35906])).

tff(c_35909,plain,(
    k6_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_15207])).

tff(c_51950,plain,(
    ! [A_158520,B_158521,C_158522,D_158523] :
      ( k3_mcart_1(k5_mcart_1(A_158520,B_158521,C_158522,D_158523),k6_mcart_1(A_158520,B_158521,C_158522,D_158523),k7_mcart_1(A_158520,B_158521,C_158522,D_158523)) = D_158523
      | ~ m1_subset_1(D_158523,k3_zfmisc_1(A_158520,B_158521,C_158522))
      | k1_xboole_0 = C_158522
      | k1_xboole_0 = B_158521
      | k1_xboole_0 = A_158520 ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_52104,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9',k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9')) = '#skF_9'
    | ~ m1_subset_1('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_35909,c_51950])).

tff(c_52108,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_9',k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9')) = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52104])).

tff(c_52110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_62,c_60,c_36495,c_52108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:10:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.98/5.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.98/5.57  
% 12.98/5.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.98/5.57  %$ r2_hidden > m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4
% 12.98/5.57  
% 12.98/5.57  %Foreground sorts:
% 12.98/5.57  
% 12.98/5.57  
% 12.98/5.57  %Background operators:
% 12.98/5.57  
% 12.98/5.57  
% 12.98/5.57  %Foreground operators:
% 12.98/5.57  tff('#skF_5', type, '#skF_5': $i > $i).
% 12.98/5.57  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 12.98/5.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.98/5.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.98/5.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.98/5.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.98/5.57  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 12.98/5.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.98/5.57  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 12.98/5.57  tff('#skF_7', type, '#skF_7': $i).
% 12.98/5.57  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 12.98/5.57  tff('#skF_6', type, '#skF_6': $i).
% 12.98/5.57  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 12.98/5.57  tff('#skF_9', type, '#skF_9': $i).
% 12.98/5.57  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 12.98/5.57  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 12.98/5.57  tff('#skF_8', type, '#skF_8': $i).
% 12.98/5.57  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 12.98/5.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.98/5.57  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 12.98/5.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.98/5.57  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 12.98/5.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.98/5.57  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 12.98/5.57  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 12.98/5.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.98/5.57  
% 12.98/5.59  tff(f_120, negated_conjecture, ~(![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ((~(D = k5_mcart_1(A, B, C, D)) & ~(D = k6_mcart_1(A, B, C, D))) & ~(D = k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_mcart_1)).
% 12.98/5.59  tff(f_42, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 12.98/5.59  tff(f_76, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 12.98/5.59  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 12.98/5.59  tff(f_47, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 12.98/5.59  tff(f_49, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 12.98/5.59  tff(f_96, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 12.98/5.59  tff(f_60, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 12.98/5.59  tff(f_92, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_mcart_1)).
% 12.98/5.59  tff(c_64, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_120])).
% 12.98/5.59  tff(c_62, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_120])).
% 12.98/5.59  tff(c_60, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_120])).
% 12.98/5.59  tff(c_22, plain, (![C_11]: (r2_hidden(C_11, k1_tarski(C_11)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.98/5.59  tff(c_44, plain, (![A_25]: (r2_hidden('#skF_5'(A_25), A_25) | k1_xboole_0=A_25)), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.98/5.59  tff(c_137, plain, (![D_67, A_68, B_69]: (r2_hidden(D_67, A_68) | ~r2_hidden(D_67, k4_xboole_0(A_68, B_69)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.98/5.59  tff(c_145, plain, (![A_68, B_69]: (r2_hidden('#skF_5'(k4_xboole_0(A_68, B_69)), A_68) | k4_xboole_0(A_68, B_69)=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_137])).
% 12.98/5.59  tff(c_128, plain, (![D_64, B_65, A_66]: (~r2_hidden(D_64, B_65) | ~r2_hidden(D_64, k4_xboole_0(A_66, B_65)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.98/5.59  tff(c_35967, plain, (![A_108349, B_108350]: (~r2_hidden('#skF_5'(k4_xboole_0(A_108349, B_108350)), B_108350) | k4_xboole_0(A_108349, B_108350)=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_128])).
% 12.98/5.59  tff(c_35981, plain, (![A_108351]: (k4_xboole_0(A_108351, A_108351)=k1_xboole_0)), inference(resolution, [status(thm)], [c_145, c_35967])).
% 12.98/5.59  tff(c_32, plain, (![B_13, A_12]: (~r2_hidden(B_13, A_12) | k4_xboole_0(A_12, k1_tarski(B_13))!=A_12)), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.98/5.59  tff(c_36002, plain, (![B_13]: (~r2_hidden(B_13, k1_tarski(B_13)) | k1_tarski(B_13)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_35981, c_32])).
% 12.98/5.59  tff(c_36017, plain, (![B_13]: (k1_tarski(B_13)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_36002])).
% 12.98/5.59  tff(c_89, plain, (![C_57, A_58]: (C_57=A_58 | ~r2_hidden(C_57, k1_tarski(A_58)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.98/5.59  tff(c_97, plain, (![A_58]: ('#skF_5'(k1_tarski(A_58))=A_58 | k1_tarski(A_58)=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_89])).
% 12.98/5.59  tff(c_36021, plain, (![A_58]: ('#skF_5'(k1_tarski(A_58))=A_58)), inference(negUnitSimplification, [status(thm)], [c_36017, c_97])).
% 12.98/5.59  tff(c_36481, plain, (![D_109811, A_109812, C_109813, E_109814]: (~r2_hidden(D_109811, A_109812) | k3_mcart_1(C_109813, D_109811, E_109814)!='#skF_5'(A_109812) | k1_xboole_0=A_109812)), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.98/5.59  tff(c_36489, plain, (![C_109813, C_11, E_109814]: (k3_mcart_1(C_109813, C_11, E_109814)!='#skF_5'(k1_tarski(C_11)) | k1_tarski(C_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_36481])).
% 12.98/5.59  tff(c_36494, plain, (![C_109813, C_11, E_109814]: (k3_mcart_1(C_109813, C_11, E_109814)!=C_11 | k1_tarski(C_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36021, c_36489])).
% 12.98/5.59  tff(c_36495, plain, (![C_109813, C_11, E_109814]: (k3_mcart_1(C_109813, C_11, E_109814)!=C_11)), inference(negUnitSimplification, [status(thm)], [c_36017, c_36494])).
% 12.98/5.59  tff(c_58, plain, (m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 12.98/5.59  tff(c_161, plain, (![A_73, B_74, C_75]: (k4_tarski(k4_tarski(A_73, B_74), C_75)=k3_mcart_1(A_73, B_74, C_75))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.98/5.59  tff(c_54, plain, (![A_44, B_45]: (k2_mcart_1(k4_tarski(A_44, B_45))=B_45)), inference(cnfTransformation, [status(thm)], [f_96])).
% 12.98/5.59  tff(c_40, plain, (![B_23, C_24]: (k2_mcart_1(k4_tarski(B_23, C_24))!=k4_tarski(B_23, C_24))), inference(cnfTransformation, [status(thm)], [f_60])).
% 12.98/5.59  tff(c_66, plain, (![B_23, C_24]: (k4_tarski(B_23, C_24)!=C_24)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_40])).
% 12.98/5.59  tff(c_176, plain, (![A_73, B_74, C_75]: (k3_mcart_1(A_73, B_74, C_75)!=C_75)), inference(superposition, [status(thm), theory('equality')], [c_161, c_66])).
% 12.98/5.59  tff(c_228, plain, (![A_97, B_98]: (r2_hidden('#skF_5'(k4_xboole_0(A_97, B_98)), A_97) | k4_xboole_0(A_97, B_98)=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_137])).
% 12.98/5.59  tff(c_136, plain, (![A_66, B_65]: (~r2_hidden('#skF_5'(k4_xboole_0(A_66, B_65)), B_65) | k4_xboole_0(A_66, B_65)=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_128])).
% 12.98/5.59  tff(c_255, plain, (![A_99]: (k4_xboole_0(A_99, A_99)=k1_xboole_0)), inference(resolution, [status(thm)], [c_228, c_136])).
% 12.98/5.59  tff(c_273, plain, (![B_13]: (~r2_hidden(B_13, k1_tarski(B_13)) | k1_tarski(B_13)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_255, c_32])).
% 12.98/5.59  tff(c_288, plain, (![B_13]: (k1_tarski(B_13)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_273])).
% 12.98/5.59  tff(c_655, plain, (![A_58]: ('#skF_5'(k1_tarski(A_58))=A_58)), inference(negUnitSimplification, [status(thm)], [c_288, c_97])).
% 12.98/5.59  tff(c_660, plain, (![A_1332]: ('#skF_5'(k1_tarski(A_1332))=A_1332)), inference(negUnitSimplification, [status(thm)], [c_288, c_97])).
% 12.98/5.59  tff(c_217, plain, (![C_90, A_91, D_92, E_93]: (~r2_hidden(C_90, A_91) | k3_mcart_1(C_90, D_92, E_93)!='#skF_5'(A_91) | k1_xboole_0=A_91)), inference(cnfTransformation, [status(thm)], [f_76])).
% 12.98/5.59  tff(c_222, plain, (![A_25, D_92, E_93]: (k3_mcart_1('#skF_5'(A_25), D_92, E_93)!='#skF_5'(A_25) | k1_xboole_0=A_25)), inference(resolution, [status(thm)], [c_44, c_217])).
% 12.98/5.59  tff(c_666, plain, (![A_1332, D_92, E_93]: (k3_mcart_1(A_1332, D_92, E_93)!='#skF_5'(k1_tarski(A_1332)) | k1_tarski(A_1332)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_660, c_222])).
% 12.98/5.59  tff(c_733, plain, (![A_1332, D_92, E_93]: (k3_mcart_1(A_1332, D_92, E_93)!=A_1332 | k1_tarski(A_1332)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_655, c_666])).
% 12.98/5.59  tff(c_734, plain, (![A_1332, D_92, E_93]: (k3_mcart_1(A_1332, D_92, E_93)!=A_1332)), inference(negUnitSimplification, [status(thm)], [c_288, c_733])).
% 12.98/5.59  tff(c_56, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9' | k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9' | k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_120])).
% 12.98/5.59  tff(c_189, plain, (k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitLeft, [status(thm)], [c_56])).
% 12.98/5.59  tff(c_15058, plain, (![A_45043, B_45044, C_45045, D_45046]: (k3_mcart_1(k5_mcart_1(A_45043, B_45044, C_45045, D_45046), k6_mcart_1(A_45043, B_45044, C_45045, D_45046), k7_mcart_1(A_45043, B_45044, C_45045, D_45046))=D_45046 | ~m1_subset_1(D_45046, k3_zfmisc_1(A_45043, B_45044, C_45045)) | k1_xboole_0=C_45045 | k1_xboole_0=B_45044 | k1_xboole_0=A_45043)), inference(cnfTransformation, [status(thm)], [f_92])).
% 12.98/5.59  tff(c_15200, plain, (k3_mcart_1('#skF_9', k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))='#skF_9' | ~m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_189, c_15058])).
% 12.98/5.59  tff(c_15204, plain, (k3_mcart_1('#skF_9', k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_15200])).
% 12.98/5.59  tff(c_15206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_62, c_60, c_734, c_15204])).
% 12.98/5.59  tff(c_15207, plain, (k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9' | k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitRight, [status(thm)], [c_56])).
% 12.98/5.59  tff(c_15219, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitLeft, [status(thm)], [c_15207])).
% 12.98/5.59  tff(c_35721, plain, (![A_107802, B_107803, C_107804, D_107805]: (k3_mcart_1(k5_mcart_1(A_107802, B_107803, C_107804, D_107805), k6_mcart_1(A_107802, B_107803, C_107804, D_107805), k7_mcart_1(A_107802, B_107803, C_107804, D_107805))=D_107805 | ~m1_subset_1(D_107805, k3_zfmisc_1(A_107802, B_107803, C_107804)) | k1_xboole_0=C_107804 | k1_xboole_0=B_107803 | k1_xboole_0=A_107802)), inference(cnfTransformation, [status(thm)], [f_92])).
% 12.98/5.59  tff(c_35902, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9')='#skF_9' | ~m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_15219, c_35721])).
% 12.98/5.59  tff(c_35906, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_35902])).
% 12.98/5.59  tff(c_35908, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_62, c_60, c_176, c_35906])).
% 12.98/5.59  tff(c_35909, plain, (k6_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9')='#skF_9'), inference(splitRight, [status(thm)], [c_15207])).
% 12.98/5.59  tff(c_51950, plain, (![A_158520, B_158521, C_158522, D_158523]: (k3_mcart_1(k5_mcart_1(A_158520, B_158521, C_158522, D_158523), k6_mcart_1(A_158520, B_158521, C_158522, D_158523), k7_mcart_1(A_158520, B_158521, C_158522, D_158523))=D_158523 | ~m1_subset_1(D_158523, k3_zfmisc_1(A_158520, B_158521, C_158522)) | k1_xboole_0=C_158522 | k1_xboole_0=B_158521 | k1_xboole_0=A_158520)), inference(cnfTransformation, [status(thm)], [f_92])).
% 12.98/5.59  tff(c_52104, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9', k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))='#skF_9' | ~m1_subset_1('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_35909, c_51950])).
% 12.98/5.59  tff(c_52108, plain, (k3_mcart_1(k5_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_9', k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_52104])).
% 12.98/5.59  tff(c_52110, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_62, c_60, c_36495, c_52108])).
% 12.98/5.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.98/5.59  
% 12.98/5.59  Inference rules
% 12.98/5.59  ----------------------
% 12.98/5.59  #Ref     : 3
% 12.98/5.59  #Sup     : 7954
% 12.98/5.59  #Fact    : 12
% 12.98/5.59  #Define  : 0
% 12.98/5.59  #Split   : 4
% 12.98/5.59  #Chain   : 0
% 12.98/5.59  #Close   : 0
% 12.98/5.59  
% 12.98/5.59  Ordering : KBO
% 12.98/5.59  
% 12.98/5.59  Simplification rules
% 12.98/5.59  ----------------------
% 12.98/5.59  #Subsume      : 1552
% 12.98/5.59  #Demod        : 2127
% 12.98/5.59  #Tautology    : 832
% 12.98/5.59  #SimpNegUnit  : 939
% 12.98/5.59  #BackRed      : 3
% 12.98/5.59  
% 12.98/5.59  #Partial instantiations: 72541
% 12.98/5.59  #Strategies tried      : 1
% 12.98/5.59  
% 12.98/5.59  Timing (in seconds)
% 12.98/5.59  ----------------------
% 12.98/5.59  Preprocessing        : 0.33
% 12.98/5.59  Parsing              : 0.17
% 12.98/5.59  CNF conversion       : 0.03
% 12.98/5.59  Main loop            : 4.49
% 12.98/5.59  Inferencing          : 1.99
% 12.98/5.59  Reduction            : 1.07
% 12.98/5.59  Demodulation         : 0.69
% 12.98/5.59  BG Simplification    : 0.20
% 12.98/5.59  Subsumption          : 1.02
% 12.98/5.59  Abstraction          : 0.27
% 12.98/5.59  MUC search           : 0.00
% 12.98/5.59  Cooper               : 0.00
% 12.98/5.59  Total                : 4.85
% 12.98/5.59  Index Insertion      : 0.00
% 12.98/5.59  Index Deletion       : 0.00
% 12.98/5.59  Index Matching       : 0.00
% 12.98/5.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
