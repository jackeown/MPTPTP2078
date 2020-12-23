%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:08 EST 2020

% Result     : Theorem 15.38s
% Output     : CNFRefutation 15.67s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 476 expanded)
%              Number of leaves         :   32 ( 186 expanded)
%              Depth                    :   14
%              Number of atoms          :  218 (1419 expanded)
%              Number of equality atoms :   60 ( 482 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_2 > #skF_6 > #skF_3 > #skF_13 > #skF_8 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_12 > #skF_4 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_56,plain,
    ( k1_xboole_0 = '#skF_13'
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_59,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_52,plain,(
    ! [A_69,B_70] : v1_relat_1('#skF_11'(A_69,B_70)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_50,plain,(
    ! [A_69,B_70] : v1_funct_1('#skF_11'(A_69,B_70)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_48,plain,(
    ! [A_69,B_70] : k1_relat_1('#skF_11'(A_69,B_70)) = A_69 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_411,plain,(
    ! [A_159,C_160] :
      ( r2_hidden('#skF_10'(A_159,k2_relat_1(A_159),C_160),k1_relat_1(A_159))
      | ~ r2_hidden(C_160,k2_relat_1(A_159))
      | ~ v1_funct_1(A_159)
      | ~ v1_relat_1(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_418,plain,(
    ! [A_69,B_70,C_160] :
      ( r2_hidden('#skF_10'('#skF_11'(A_69,B_70),k2_relat_1('#skF_11'(A_69,B_70)),C_160),A_69)
      | ~ r2_hidden(C_160,k2_relat_1('#skF_11'(A_69,B_70)))
      | ~ v1_funct_1('#skF_11'(A_69,B_70))
      | ~ v1_relat_1('#skF_11'(A_69,B_70)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_411])).

tff(c_422,plain,(
    ! [A_69,B_70,C_160] :
      ( r2_hidden('#skF_10'('#skF_11'(A_69,B_70),k2_relat_1('#skF_11'(A_69,B_70)),C_160),A_69)
      | ~ r2_hidden(C_160,k2_relat_1('#skF_11'(A_69,B_70))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_418])).

tff(c_284,plain,(
    ! [A_141,C_142] :
      ( k1_funct_1(A_141,'#skF_10'(A_141,k2_relat_1(A_141),C_142)) = C_142
      | ~ r2_hidden(C_142,k2_relat_1(A_141))
      | ~ v1_funct_1(A_141)
      | ~ v1_relat_1(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_46,plain,(
    ! [A_69,B_70,D_75] :
      ( k1_funct_1('#skF_11'(A_69,B_70),D_75) = B_70
      | ~ r2_hidden(D_75,A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_294,plain,(
    ! [C_142,B_70,A_69] :
      ( C_142 = B_70
      | ~ r2_hidden('#skF_10'('#skF_11'(A_69,B_70),k2_relat_1('#skF_11'(A_69,B_70)),C_142),A_69)
      | ~ r2_hidden(C_142,k2_relat_1('#skF_11'(A_69,B_70)))
      | ~ v1_funct_1('#skF_11'(A_69,B_70))
      | ~ v1_relat_1('#skF_11'(A_69,B_70)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_46])).

tff(c_55943,plain,(
    ! [C_8538,B_8539,A_8540] :
      ( C_8538 = B_8539
      | ~ r2_hidden('#skF_10'('#skF_11'(A_8540,B_8539),k2_relat_1('#skF_11'(A_8540,B_8539)),C_8538),A_8540)
      | ~ r2_hidden(C_8538,k2_relat_1('#skF_11'(A_8540,B_8539))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_294])).

tff(c_55975,plain,(
    ! [C_8599,B_8600,A_8601] :
      ( C_8599 = B_8600
      | ~ r2_hidden(C_8599,k2_relat_1('#skF_11'(A_8601,B_8600))) ) ),
    inference(resolution,[status(thm)],[c_422,c_55943])).

tff(c_57970,plain,(
    ! [A_8861,B_8862,B_8863] :
      ( '#skF_1'(k2_relat_1('#skF_11'(A_8861,B_8862)),B_8863) = B_8862
      | r1_tarski(k2_relat_1('#skF_11'(A_8861,B_8862)),B_8863) ) ),
    inference(resolution,[status(thm)],[c_6,c_55975])).

tff(c_54,plain,(
    ! [C_77] :
      ( ~ r1_tarski(k2_relat_1(C_77),'#skF_12')
      | k1_relat_1(C_77) != '#skF_13'
      | ~ v1_funct_1(C_77)
      | ~ v1_relat_1(C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_57989,plain,(
    ! [A_8861,B_8862] :
      ( k1_relat_1('#skF_11'(A_8861,B_8862)) != '#skF_13'
      | ~ v1_funct_1('#skF_11'(A_8861,B_8862))
      | ~ v1_relat_1('#skF_11'(A_8861,B_8862))
      | '#skF_1'(k2_relat_1('#skF_11'(A_8861,B_8862)),'#skF_12') = B_8862 ) ),
    inference(resolution,[status(thm)],[c_57970,c_54])).

tff(c_58000,plain,(
    ! [A_8864,B_8865] :
      ( A_8864 != '#skF_13'
      | '#skF_1'(k2_relat_1('#skF_11'(A_8864,B_8865)),'#skF_12') = B_8865 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_57989])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58048,plain,(
    ! [B_8869,A_8870] :
      ( ~ r2_hidden(B_8869,'#skF_12')
      | r1_tarski(k2_relat_1('#skF_11'(A_8870,B_8869)),'#skF_12')
      | A_8870 != '#skF_13' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58000,c_4])).

tff(c_58062,plain,(
    ! [A_8870,B_8869] :
      ( k1_relat_1('#skF_11'(A_8870,B_8869)) != '#skF_13'
      | ~ v1_funct_1('#skF_11'(A_8870,B_8869))
      | ~ v1_relat_1('#skF_11'(A_8870,B_8869))
      | ~ r2_hidden(B_8869,'#skF_12')
      | A_8870 != '#skF_13' ) ),
    inference(resolution,[status(thm)],[c_58048,c_54])).

tff(c_58070,plain,(
    ! [B_8869,A_8870] :
      ( ~ r2_hidden(B_8869,'#skF_12')
      | A_8870 != '#skF_13' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_58062])).

tff(c_58071,plain,(
    ! [A_8870] : A_8870 != '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_58070])).

tff(c_58092,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_58071])).

tff(c_58094,plain,(
    ! [B_8874] : ~ r2_hidden(B_8874,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_58070])).

tff(c_58146,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_8,c_58094])).

tff(c_58161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_58146])).

tff(c_58163,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_58190,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58163,c_8])).

tff(c_16,plain,(
    ! [A_10,C_25] :
      ( r2_hidden(k4_tarski('#skF_6'(A_10,k2_relat_1(A_10),C_25),C_25),A_10)
      | ~ r2_hidden(C_25,k2_relat_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_58251,plain,(
    ! [A_8911,D_8912] :
      ( r2_hidden(k1_funct_1(A_8911,D_8912),k2_relat_1(A_8911))
      | ~ r2_hidden(D_8912,k1_relat_1(A_8911))
      | ~ v1_funct_1(A_8911)
      | ~ v1_relat_1(A_8911) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_58256,plain,(
    ! [B_70,A_69,D_75] :
      ( r2_hidden(B_70,k2_relat_1('#skF_11'(A_69,B_70)))
      | ~ r2_hidden(D_75,k1_relat_1('#skF_11'(A_69,B_70)))
      | ~ v1_funct_1('#skF_11'(A_69,B_70))
      | ~ v1_relat_1('#skF_11'(A_69,B_70))
      | ~ r2_hidden(D_75,A_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_58251])).

tff(c_58261,plain,(
    ! [B_8916,A_8917,D_8918] :
      ( r2_hidden(B_8916,k2_relat_1('#skF_11'(A_8917,B_8916)))
      | ~ r2_hidden(D_8918,A_8917) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_58256])).

tff(c_58311,plain,(
    ! [B_8924,A_8925,C_8926] :
      ( r2_hidden(B_8924,k2_relat_1('#skF_11'(A_8925,B_8924)))
      | ~ r2_hidden(C_8926,k2_relat_1(A_8925)) ) ),
    inference(resolution,[status(thm)],[c_16,c_58261])).

tff(c_58440,plain,(
    ! [B_8942,A_8943,C_8944] :
      ( r2_hidden(B_8942,k2_relat_1('#skF_11'(A_8943,B_8942)))
      | ~ r2_hidden(C_8944,k2_relat_1(k2_relat_1(A_8943))) ) ),
    inference(resolution,[status(thm)],[c_16,c_58311])).

tff(c_58808,plain,(
    ! [B_8994,A_8995,C_8996] :
      ( r2_hidden(B_8994,k2_relat_1('#skF_11'(A_8995,B_8994)))
      | ~ r2_hidden(C_8996,k2_relat_1(k2_relat_1(k2_relat_1(A_8995)))) ) ),
    inference(resolution,[status(thm)],[c_16,c_58440])).

tff(c_59721,plain,(
    ! [B_9096,A_9097,C_9098] :
      ( r2_hidden(B_9096,k2_relat_1('#skF_11'(A_9097,B_9096)))
      | ~ r2_hidden(C_9098,k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(A_9097))))) ) ),
    inference(resolution,[status(thm)],[c_16,c_58808])).

tff(c_59757,plain,(
    ! [B_9096,A_9097] :
      ( r2_hidden(B_9096,k2_relat_1('#skF_11'(A_9097,B_9096)))
      | k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(A_9097)))) = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_58190,c_59721])).

tff(c_14,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_58356,plain,(
    ! [A_8929,C_8930] :
      ( r2_hidden('#skF_10'(A_8929,k2_relat_1(A_8929),C_8930),k1_relat_1(A_8929))
      | ~ r2_hidden(C_8930,k2_relat_1(A_8929))
      | ~ v1_funct_1(A_8929)
      | ~ v1_relat_1(A_8929) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_58363,plain,(
    ! [A_69,B_70,C_8930] :
      ( r2_hidden('#skF_10'('#skF_11'(A_69,B_70),k2_relat_1('#skF_11'(A_69,B_70)),C_8930),A_69)
      | ~ r2_hidden(C_8930,k2_relat_1('#skF_11'(A_69,B_70)))
      | ~ v1_funct_1('#skF_11'(A_69,B_70))
      | ~ v1_relat_1('#skF_11'(A_69,B_70)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_58356])).

tff(c_61626,plain,(
    ! [A_9217,B_9218,C_9219] :
      ( r2_hidden('#skF_10'('#skF_11'(A_9217,B_9218),k2_relat_1('#skF_11'(A_9217,B_9218)),C_9219),A_9217)
      | ~ r2_hidden(C_9219,k2_relat_1('#skF_11'(A_9217,B_9218))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_58363])).

tff(c_58259,plain,(
    ! [B_70,A_69,D_75] :
      ( r2_hidden(B_70,k2_relat_1('#skF_11'(A_69,B_70)))
      | ~ r2_hidden(D_75,A_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_58256])).

tff(c_61664,plain,(
    ! [B_9220,A_9221,C_9222,B_9223] :
      ( r2_hidden(B_9220,k2_relat_1('#skF_11'(A_9221,B_9220)))
      | ~ r2_hidden(C_9222,k2_relat_1('#skF_11'(A_9221,B_9223))) ) ),
    inference(resolution,[status(thm)],[c_61626,c_58259])).

tff(c_61829,plain,(
    ! [B_9224,A_9225,B_9226] :
      ( r2_hidden(B_9224,k2_relat_1('#skF_11'(A_9225,B_9224)))
      | k2_relat_1('#skF_11'(A_9225,B_9226)) = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_58190,c_61664])).

tff(c_58162,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_58169,plain,(
    '#skF_13' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58163,c_58162])).

tff(c_58174,plain,(
    ! [C_77] :
      ( ~ r1_tarski(k2_relat_1(C_77),'#skF_12')
      | k1_relat_1(C_77) != '#skF_12'
      | ~ v1_funct_1(C_77)
      | ~ v1_relat_1(C_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58169,c_54])).

tff(c_62154,plain,(
    ! [A_9225,B_9226,B_9224] :
      ( ~ r1_tarski('#skF_12','#skF_12')
      | k1_relat_1('#skF_11'(A_9225,B_9226)) != '#skF_12'
      | ~ v1_funct_1('#skF_11'(A_9225,B_9226))
      | ~ v1_relat_1('#skF_11'(A_9225,B_9226))
      | r2_hidden(B_9224,k2_relat_1('#skF_11'(A_9225,B_9224))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61829,c_58174])).

tff(c_62176,plain,(
    ! [A_9225,B_9224] :
      ( A_9225 != '#skF_12'
      | r2_hidden(B_9224,k2_relat_1('#skF_11'(A_9225,B_9224))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_14,c_62154])).

tff(c_58275,plain,(
    ! [B_8916,A_10,C_25] :
      ( r2_hidden(B_8916,k2_relat_1('#skF_11'(A_10,B_8916)))
      | ~ r2_hidden(C_25,k2_relat_1(A_10)) ) ),
    inference(resolution,[status(thm)],[c_16,c_58261])).

tff(c_62956,plain,(
    ! [B_9265,A_9266,C_9267,B_9268] :
      ( r2_hidden(B_9265,k2_relat_1('#skF_11'(A_9266,B_9265)))
      | ~ r2_hidden(C_9267,k2_relat_1('#skF_11'(k2_relat_1(A_9266),B_9268))) ) ),
    inference(resolution,[status(thm)],[c_61626,c_58275])).

tff(c_63131,plain,(
    ! [B_9269,A_9270] :
      ( r2_hidden(B_9269,k2_relat_1('#skF_11'(A_9270,B_9269)))
      | k2_relat_1(A_9270) != '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_62176,c_62956])).

tff(c_61661,plain,(
    ! [B_8916,A_10,C_9219,B_9218] :
      ( r2_hidden(B_8916,k2_relat_1('#skF_11'(A_10,B_8916)))
      | ~ r2_hidden(C_9219,k2_relat_1('#skF_11'(k2_relat_1(A_10),B_9218))) ) ),
    inference(resolution,[status(thm)],[c_61626,c_58275])).

tff(c_63162,plain,(
    ! [B_9271,A_9272] :
      ( r2_hidden(B_9271,k2_relat_1('#skF_11'(A_9272,B_9271)))
      | k2_relat_1(k2_relat_1(A_9272)) != '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_63131,c_61661])).

tff(c_63282,plain,(
    ! [B_9279,A_9280] :
      ( r2_hidden(B_9279,k2_relat_1('#skF_11'(A_9280,B_9279)))
      | k2_relat_1(k2_relat_1(k2_relat_1(A_9280))) != '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_63162,c_61661])).

tff(c_63877,plain,(
    ! [B_9299,A_9300] :
      ( r2_hidden(B_9299,k2_relat_1('#skF_11'(A_9300,B_9299)))
      | k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(A_9300)))) != '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_63282,c_61661])).

tff(c_63894,plain,(
    ! [B_9299,A_9097,B_9096] :
      ( r2_hidden(B_9299,k2_relat_1('#skF_11'(A_9097,B_9299)))
      | r2_hidden(B_9096,k2_relat_1('#skF_11'(A_9097,B_9096))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59757,c_63877])).

tff(c_64006,plain,(
    ! [B_9299,A_9097] : r2_hidden(B_9299,k2_relat_1('#skF_11'(A_9097,B_9299))) ),
    inference(factorization,[status(thm),theory(equality)],[c_63894])).

tff(c_58367,plain,(
    ! [A_69,B_70,C_8930] :
      ( r2_hidden('#skF_10'('#skF_11'(A_69,B_70),k2_relat_1('#skF_11'(A_69,B_70)),C_8930),A_69)
      | ~ r2_hidden(C_8930,k2_relat_1('#skF_11'(A_69,B_70))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_58363])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58365,plain,(
    ! [A_8929,C_8930,B_2] :
      ( r2_hidden('#skF_10'(A_8929,k2_relat_1(A_8929),C_8930),B_2)
      | ~ r1_tarski(k1_relat_1(A_8929),B_2)
      | ~ r2_hidden(C_8930,k2_relat_1(A_8929))
      | ~ v1_funct_1(A_8929)
      | ~ v1_relat_1(A_8929) ) ),
    inference(resolution,[status(thm)],[c_58356,c_2])).

tff(c_58416,plain,(
    ! [A_8940,C_8941] :
      ( k1_funct_1(A_8940,'#skF_10'(A_8940,k2_relat_1(A_8940),C_8941)) = C_8941
      | ~ r2_hidden(C_8941,k2_relat_1(A_8940))
      | ~ v1_funct_1(A_8940)
      | ~ v1_relat_1(A_8940) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_58426,plain,(
    ! [C_8941,B_70,A_69] :
      ( C_8941 = B_70
      | ~ r2_hidden('#skF_10'('#skF_11'(A_69,B_70),k2_relat_1('#skF_11'(A_69,B_70)),C_8941),A_69)
      | ~ r2_hidden(C_8941,k2_relat_1('#skF_11'(A_69,B_70)))
      | ~ v1_funct_1('#skF_11'(A_69,B_70))
      | ~ v1_relat_1('#skF_11'(A_69,B_70)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58416,c_46])).

tff(c_64209,plain,(
    ! [C_9323,B_9324,A_9325] :
      ( C_9323 = B_9324
      | ~ r2_hidden('#skF_10'('#skF_11'(A_9325,B_9324),k2_relat_1('#skF_11'(A_9325,B_9324)),C_9323),A_9325)
      | ~ r2_hidden(C_9323,k2_relat_1('#skF_11'(A_9325,B_9324))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_58426])).

tff(c_64213,plain,(
    ! [C_8930,B_9324,B_2] :
      ( C_8930 = B_9324
      | ~ r1_tarski(k1_relat_1('#skF_11'(B_2,B_9324)),B_2)
      | ~ r2_hidden(C_8930,k2_relat_1('#skF_11'(B_2,B_9324)))
      | ~ v1_funct_1('#skF_11'(B_2,B_9324))
      | ~ v1_relat_1('#skF_11'(B_2,B_9324)) ) ),
    inference(resolution,[status(thm)],[c_58365,c_64209])).

tff(c_64221,plain,(
    ! [C_9326,B_9327,B_9328] :
      ( C_9326 = B_9327
      | ~ r2_hidden(C_9326,k2_relat_1('#skF_11'(B_9328,B_9327))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_14,c_48,c_64213])).

tff(c_64343,plain,(
    ! [B_9334,B_9335,B_9336] :
      ( '#skF_1'(k2_relat_1('#skF_11'(B_9334,B_9335)),B_9336) = B_9335
      | r1_tarski(k2_relat_1('#skF_11'(B_9334,B_9335)),B_9336) ) ),
    inference(resolution,[status(thm)],[c_6,c_64221])).

tff(c_64360,plain,(
    ! [B_9334,B_9335] :
      ( k1_relat_1('#skF_11'(B_9334,B_9335)) != '#skF_12'
      | ~ v1_funct_1('#skF_11'(B_9334,B_9335))
      | ~ v1_relat_1('#skF_11'(B_9334,B_9335))
      | '#skF_1'(k2_relat_1('#skF_11'(B_9334,B_9335)),'#skF_12') = B_9335 ) ),
    inference(resolution,[status(thm)],[c_64343,c_58174])).

tff(c_64373,plain,(
    ! [B_9337,B_9338] :
      ( B_9337 != '#skF_12'
      | '#skF_1'(k2_relat_1('#skF_11'(B_9337,B_9338)),'#skF_12') = B_9338 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_64360])).

tff(c_64421,plain,(
    ! [B_9342,B_9343] :
      ( ~ r2_hidden(B_9342,'#skF_12')
      | r1_tarski(k2_relat_1('#skF_11'(B_9343,B_9342)),'#skF_12')
      | B_9343 != '#skF_12' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64373,c_4])).

tff(c_64433,plain,(
    ! [B_9343,B_9342] :
      ( k1_relat_1('#skF_11'(B_9343,B_9342)) != '#skF_12'
      | ~ v1_funct_1('#skF_11'(B_9343,B_9342))
      | ~ v1_relat_1('#skF_11'(B_9343,B_9342))
      | ~ r2_hidden(B_9342,'#skF_12')
      | B_9343 != '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_64421,c_58174])).

tff(c_64442,plain,(
    ! [B_9342,B_9343] :
      ( ~ r2_hidden(B_9342,'#skF_12')
      | B_9343 != '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_48,c_64433])).

tff(c_64444,plain,(
    ! [B_9343] : B_9343 != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_64442])).

tff(c_64452,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64444,c_58169])).

tff(c_64455,plain,(
    ! [B_9344] : ~ r2_hidden(B_9344,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_64442])).

tff(c_64727,plain,(
    ! [C_9353,B_9354] : ~ r2_hidden(C_9353,k2_relat_1('#skF_11'('#skF_12',B_9354))) ),
    inference(resolution,[status(thm)],[c_58367,c_64455])).

tff(c_64809,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_64006,c_64727])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:46:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.38/6.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.67/6.08  
% 15.67/6.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.67/6.08  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_2 > #skF_6 > #skF_3 > #skF_13 > #skF_8 > #skF_7 > #skF_1 > #skF_9 > #skF_5 > #skF_12 > #skF_4 > #skF_10
% 15.67/6.08  
% 15.67/6.08  %Foreground sorts:
% 15.67/6.08  
% 15.67/6.08  
% 15.67/6.08  %Background operators:
% 15.67/6.08  
% 15.67/6.08  
% 15.67/6.08  %Foreground operators:
% 15.67/6.08  tff('#skF_11', type, '#skF_11': ($i * $i) > $i).
% 15.67/6.08  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 15.67/6.08  tff('#skF_2', type, '#skF_2': $i > $i).
% 15.67/6.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.67/6.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.67/6.08  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 15.67/6.08  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 15.67/6.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.67/6.08  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 15.67/6.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.67/6.08  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 15.67/6.08  tff('#skF_13', type, '#skF_13': $i).
% 15.67/6.08  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 15.67/6.08  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 15.67/6.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.67/6.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.67/6.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.67/6.08  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 15.67/6.08  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 15.67/6.08  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 15.67/6.08  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 15.67/6.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 15.67/6.08  tff('#skF_12', type, '#skF_12': $i).
% 15.67/6.08  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 15.67/6.08  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 15.67/6.08  
% 15.67/6.10  tff(f_99, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 15.67/6.10  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 15.67/6.10  tff(f_81, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 15.67/6.10  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 15.67/6.10  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 15.67/6.10  tff(f_54, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 15.67/6.10  tff(f_46, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.67/6.10  tff(c_56, plain, (k1_xboole_0='#skF_13' | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_99])).
% 15.67/6.10  tff(c_59, plain, (k1_xboole_0!='#skF_12'), inference(splitLeft, [status(thm)], [c_56])).
% 15.67/6.10  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 15.67/6.10  tff(c_52, plain, (![A_69, B_70]: (v1_relat_1('#skF_11'(A_69, B_70)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 15.67/6.10  tff(c_50, plain, (![A_69, B_70]: (v1_funct_1('#skF_11'(A_69, B_70)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 15.67/6.10  tff(c_48, plain, (![A_69, B_70]: (k1_relat_1('#skF_11'(A_69, B_70))=A_69)), inference(cnfTransformation, [status(thm)], [f_81])).
% 15.67/6.10  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.67/6.10  tff(c_411, plain, (![A_159, C_160]: (r2_hidden('#skF_10'(A_159, k2_relat_1(A_159), C_160), k1_relat_1(A_159)) | ~r2_hidden(C_160, k2_relat_1(A_159)) | ~v1_funct_1(A_159) | ~v1_relat_1(A_159))), inference(cnfTransformation, [status(thm)], [f_69])).
% 15.67/6.10  tff(c_418, plain, (![A_69, B_70, C_160]: (r2_hidden('#skF_10'('#skF_11'(A_69, B_70), k2_relat_1('#skF_11'(A_69, B_70)), C_160), A_69) | ~r2_hidden(C_160, k2_relat_1('#skF_11'(A_69, B_70))) | ~v1_funct_1('#skF_11'(A_69, B_70)) | ~v1_relat_1('#skF_11'(A_69, B_70)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_411])).
% 15.67/6.10  tff(c_422, plain, (![A_69, B_70, C_160]: (r2_hidden('#skF_10'('#skF_11'(A_69, B_70), k2_relat_1('#skF_11'(A_69, B_70)), C_160), A_69) | ~r2_hidden(C_160, k2_relat_1('#skF_11'(A_69, B_70))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_418])).
% 15.67/6.10  tff(c_284, plain, (![A_141, C_142]: (k1_funct_1(A_141, '#skF_10'(A_141, k2_relat_1(A_141), C_142))=C_142 | ~r2_hidden(C_142, k2_relat_1(A_141)) | ~v1_funct_1(A_141) | ~v1_relat_1(A_141))), inference(cnfTransformation, [status(thm)], [f_69])).
% 15.67/6.10  tff(c_46, plain, (![A_69, B_70, D_75]: (k1_funct_1('#skF_11'(A_69, B_70), D_75)=B_70 | ~r2_hidden(D_75, A_69))), inference(cnfTransformation, [status(thm)], [f_81])).
% 15.67/6.10  tff(c_294, plain, (![C_142, B_70, A_69]: (C_142=B_70 | ~r2_hidden('#skF_10'('#skF_11'(A_69, B_70), k2_relat_1('#skF_11'(A_69, B_70)), C_142), A_69) | ~r2_hidden(C_142, k2_relat_1('#skF_11'(A_69, B_70))) | ~v1_funct_1('#skF_11'(A_69, B_70)) | ~v1_relat_1('#skF_11'(A_69, B_70)))), inference(superposition, [status(thm), theory('equality')], [c_284, c_46])).
% 15.67/6.10  tff(c_55943, plain, (![C_8538, B_8539, A_8540]: (C_8538=B_8539 | ~r2_hidden('#skF_10'('#skF_11'(A_8540, B_8539), k2_relat_1('#skF_11'(A_8540, B_8539)), C_8538), A_8540) | ~r2_hidden(C_8538, k2_relat_1('#skF_11'(A_8540, B_8539))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_294])).
% 15.67/6.10  tff(c_55975, plain, (![C_8599, B_8600, A_8601]: (C_8599=B_8600 | ~r2_hidden(C_8599, k2_relat_1('#skF_11'(A_8601, B_8600))))), inference(resolution, [status(thm)], [c_422, c_55943])).
% 15.67/6.10  tff(c_57970, plain, (![A_8861, B_8862, B_8863]: ('#skF_1'(k2_relat_1('#skF_11'(A_8861, B_8862)), B_8863)=B_8862 | r1_tarski(k2_relat_1('#skF_11'(A_8861, B_8862)), B_8863))), inference(resolution, [status(thm)], [c_6, c_55975])).
% 15.67/6.10  tff(c_54, plain, (![C_77]: (~r1_tarski(k2_relat_1(C_77), '#skF_12') | k1_relat_1(C_77)!='#skF_13' | ~v1_funct_1(C_77) | ~v1_relat_1(C_77))), inference(cnfTransformation, [status(thm)], [f_99])).
% 15.67/6.10  tff(c_57989, plain, (![A_8861, B_8862]: (k1_relat_1('#skF_11'(A_8861, B_8862))!='#skF_13' | ~v1_funct_1('#skF_11'(A_8861, B_8862)) | ~v1_relat_1('#skF_11'(A_8861, B_8862)) | '#skF_1'(k2_relat_1('#skF_11'(A_8861, B_8862)), '#skF_12')=B_8862)), inference(resolution, [status(thm)], [c_57970, c_54])).
% 15.67/6.10  tff(c_58000, plain, (![A_8864, B_8865]: (A_8864!='#skF_13' | '#skF_1'(k2_relat_1('#skF_11'(A_8864, B_8865)), '#skF_12')=B_8865)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_57989])).
% 15.67/6.10  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.67/6.10  tff(c_58048, plain, (![B_8869, A_8870]: (~r2_hidden(B_8869, '#skF_12') | r1_tarski(k2_relat_1('#skF_11'(A_8870, B_8869)), '#skF_12') | A_8870!='#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_58000, c_4])).
% 15.67/6.10  tff(c_58062, plain, (![A_8870, B_8869]: (k1_relat_1('#skF_11'(A_8870, B_8869))!='#skF_13' | ~v1_funct_1('#skF_11'(A_8870, B_8869)) | ~v1_relat_1('#skF_11'(A_8870, B_8869)) | ~r2_hidden(B_8869, '#skF_12') | A_8870!='#skF_13')), inference(resolution, [status(thm)], [c_58048, c_54])).
% 15.67/6.10  tff(c_58070, plain, (![B_8869, A_8870]: (~r2_hidden(B_8869, '#skF_12') | A_8870!='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_58062])).
% 15.67/6.10  tff(c_58071, plain, (![A_8870]: (A_8870!='#skF_13')), inference(splitLeft, [status(thm)], [c_58070])).
% 15.67/6.10  tff(c_58092, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_58071])).
% 15.67/6.10  tff(c_58094, plain, (![B_8874]: (~r2_hidden(B_8874, '#skF_12'))), inference(splitRight, [status(thm)], [c_58070])).
% 15.67/6.10  tff(c_58146, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_8, c_58094])).
% 15.67/6.10  tff(c_58161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_58146])).
% 15.67/6.10  tff(c_58163, plain, (k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_56])).
% 15.67/6.10  tff(c_58190, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_58163, c_8])).
% 15.67/6.10  tff(c_16, plain, (![A_10, C_25]: (r2_hidden(k4_tarski('#skF_6'(A_10, k2_relat_1(A_10), C_25), C_25), A_10) | ~r2_hidden(C_25, k2_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 15.67/6.10  tff(c_58251, plain, (![A_8911, D_8912]: (r2_hidden(k1_funct_1(A_8911, D_8912), k2_relat_1(A_8911)) | ~r2_hidden(D_8912, k1_relat_1(A_8911)) | ~v1_funct_1(A_8911) | ~v1_relat_1(A_8911))), inference(cnfTransformation, [status(thm)], [f_69])).
% 15.67/6.10  tff(c_58256, plain, (![B_70, A_69, D_75]: (r2_hidden(B_70, k2_relat_1('#skF_11'(A_69, B_70))) | ~r2_hidden(D_75, k1_relat_1('#skF_11'(A_69, B_70))) | ~v1_funct_1('#skF_11'(A_69, B_70)) | ~v1_relat_1('#skF_11'(A_69, B_70)) | ~r2_hidden(D_75, A_69))), inference(superposition, [status(thm), theory('equality')], [c_46, c_58251])).
% 15.67/6.10  tff(c_58261, plain, (![B_8916, A_8917, D_8918]: (r2_hidden(B_8916, k2_relat_1('#skF_11'(A_8917, B_8916))) | ~r2_hidden(D_8918, A_8917))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_58256])).
% 15.67/6.10  tff(c_58311, plain, (![B_8924, A_8925, C_8926]: (r2_hidden(B_8924, k2_relat_1('#skF_11'(A_8925, B_8924))) | ~r2_hidden(C_8926, k2_relat_1(A_8925)))), inference(resolution, [status(thm)], [c_16, c_58261])).
% 15.67/6.10  tff(c_58440, plain, (![B_8942, A_8943, C_8944]: (r2_hidden(B_8942, k2_relat_1('#skF_11'(A_8943, B_8942))) | ~r2_hidden(C_8944, k2_relat_1(k2_relat_1(A_8943))))), inference(resolution, [status(thm)], [c_16, c_58311])).
% 15.67/6.10  tff(c_58808, plain, (![B_8994, A_8995, C_8996]: (r2_hidden(B_8994, k2_relat_1('#skF_11'(A_8995, B_8994))) | ~r2_hidden(C_8996, k2_relat_1(k2_relat_1(k2_relat_1(A_8995)))))), inference(resolution, [status(thm)], [c_16, c_58440])).
% 15.67/6.10  tff(c_59721, plain, (![B_9096, A_9097, C_9098]: (r2_hidden(B_9096, k2_relat_1('#skF_11'(A_9097, B_9096))) | ~r2_hidden(C_9098, k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(A_9097))))))), inference(resolution, [status(thm)], [c_16, c_58808])).
% 15.67/6.10  tff(c_59757, plain, (![B_9096, A_9097]: (r2_hidden(B_9096, k2_relat_1('#skF_11'(A_9097, B_9096))) | k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(A_9097))))='#skF_12')), inference(resolution, [status(thm)], [c_58190, c_59721])).
% 15.67/6.10  tff(c_14, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 15.67/6.10  tff(c_58356, plain, (![A_8929, C_8930]: (r2_hidden('#skF_10'(A_8929, k2_relat_1(A_8929), C_8930), k1_relat_1(A_8929)) | ~r2_hidden(C_8930, k2_relat_1(A_8929)) | ~v1_funct_1(A_8929) | ~v1_relat_1(A_8929))), inference(cnfTransformation, [status(thm)], [f_69])).
% 15.67/6.10  tff(c_58363, plain, (![A_69, B_70, C_8930]: (r2_hidden('#skF_10'('#skF_11'(A_69, B_70), k2_relat_1('#skF_11'(A_69, B_70)), C_8930), A_69) | ~r2_hidden(C_8930, k2_relat_1('#skF_11'(A_69, B_70))) | ~v1_funct_1('#skF_11'(A_69, B_70)) | ~v1_relat_1('#skF_11'(A_69, B_70)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_58356])).
% 15.67/6.10  tff(c_61626, plain, (![A_9217, B_9218, C_9219]: (r2_hidden('#skF_10'('#skF_11'(A_9217, B_9218), k2_relat_1('#skF_11'(A_9217, B_9218)), C_9219), A_9217) | ~r2_hidden(C_9219, k2_relat_1('#skF_11'(A_9217, B_9218))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_58363])).
% 15.67/6.10  tff(c_58259, plain, (![B_70, A_69, D_75]: (r2_hidden(B_70, k2_relat_1('#skF_11'(A_69, B_70))) | ~r2_hidden(D_75, A_69))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_58256])).
% 15.67/6.10  tff(c_61664, plain, (![B_9220, A_9221, C_9222, B_9223]: (r2_hidden(B_9220, k2_relat_1('#skF_11'(A_9221, B_9220))) | ~r2_hidden(C_9222, k2_relat_1('#skF_11'(A_9221, B_9223))))), inference(resolution, [status(thm)], [c_61626, c_58259])).
% 15.67/6.10  tff(c_61829, plain, (![B_9224, A_9225, B_9226]: (r2_hidden(B_9224, k2_relat_1('#skF_11'(A_9225, B_9224))) | k2_relat_1('#skF_11'(A_9225, B_9226))='#skF_12')), inference(resolution, [status(thm)], [c_58190, c_61664])).
% 15.67/6.10  tff(c_58162, plain, (k1_xboole_0='#skF_13'), inference(splitRight, [status(thm)], [c_56])).
% 15.67/6.10  tff(c_58169, plain, ('#skF_13'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_58163, c_58162])).
% 15.67/6.10  tff(c_58174, plain, (![C_77]: (~r1_tarski(k2_relat_1(C_77), '#skF_12') | k1_relat_1(C_77)!='#skF_12' | ~v1_funct_1(C_77) | ~v1_relat_1(C_77))), inference(demodulation, [status(thm), theory('equality')], [c_58169, c_54])).
% 15.67/6.10  tff(c_62154, plain, (![A_9225, B_9226, B_9224]: (~r1_tarski('#skF_12', '#skF_12') | k1_relat_1('#skF_11'(A_9225, B_9226))!='#skF_12' | ~v1_funct_1('#skF_11'(A_9225, B_9226)) | ~v1_relat_1('#skF_11'(A_9225, B_9226)) | r2_hidden(B_9224, k2_relat_1('#skF_11'(A_9225, B_9224))))), inference(superposition, [status(thm), theory('equality')], [c_61829, c_58174])).
% 15.67/6.10  tff(c_62176, plain, (![A_9225, B_9224]: (A_9225!='#skF_12' | r2_hidden(B_9224, k2_relat_1('#skF_11'(A_9225, B_9224))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_14, c_62154])).
% 15.67/6.10  tff(c_58275, plain, (![B_8916, A_10, C_25]: (r2_hidden(B_8916, k2_relat_1('#skF_11'(A_10, B_8916))) | ~r2_hidden(C_25, k2_relat_1(A_10)))), inference(resolution, [status(thm)], [c_16, c_58261])).
% 15.67/6.10  tff(c_62956, plain, (![B_9265, A_9266, C_9267, B_9268]: (r2_hidden(B_9265, k2_relat_1('#skF_11'(A_9266, B_9265))) | ~r2_hidden(C_9267, k2_relat_1('#skF_11'(k2_relat_1(A_9266), B_9268))))), inference(resolution, [status(thm)], [c_61626, c_58275])).
% 15.67/6.10  tff(c_63131, plain, (![B_9269, A_9270]: (r2_hidden(B_9269, k2_relat_1('#skF_11'(A_9270, B_9269))) | k2_relat_1(A_9270)!='#skF_12')), inference(resolution, [status(thm)], [c_62176, c_62956])).
% 15.67/6.10  tff(c_61661, plain, (![B_8916, A_10, C_9219, B_9218]: (r2_hidden(B_8916, k2_relat_1('#skF_11'(A_10, B_8916))) | ~r2_hidden(C_9219, k2_relat_1('#skF_11'(k2_relat_1(A_10), B_9218))))), inference(resolution, [status(thm)], [c_61626, c_58275])).
% 15.67/6.10  tff(c_63162, plain, (![B_9271, A_9272]: (r2_hidden(B_9271, k2_relat_1('#skF_11'(A_9272, B_9271))) | k2_relat_1(k2_relat_1(A_9272))!='#skF_12')), inference(resolution, [status(thm)], [c_63131, c_61661])).
% 15.67/6.10  tff(c_63282, plain, (![B_9279, A_9280]: (r2_hidden(B_9279, k2_relat_1('#skF_11'(A_9280, B_9279))) | k2_relat_1(k2_relat_1(k2_relat_1(A_9280)))!='#skF_12')), inference(resolution, [status(thm)], [c_63162, c_61661])).
% 15.67/6.10  tff(c_63877, plain, (![B_9299, A_9300]: (r2_hidden(B_9299, k2_relat_1('#skF_11'(A_9300, B_9299))) | k2_relat_1(k2_relat_1(k2_relat_1(k2_relat_1(A_9300))))!='#skF_12')), inference(resolution, [status(thm)], [c_63282, c_61661])).
% 15.67/6.10  tff(c_63894, plain, (![B_9299, A_9097, B_9096]: (r2_hidden(B_9299, k2_relat_1('#skF_11'(A_9097, B_9299))) | r2_hidden(B_9096, k2_relat_1('#skF_11'(A_9097, B_9096))))), inference(superposition, [status(thm), theory('equality')], [c_59757, c_63877])).
% 15.67/6.10  tff(c_64006, plain, (![B_9299, A_9097]: (r2_hidden(B_9299, k2_relat_1('#skF_11'(A_9097, B_9299))))), inference(factorization, [status(thm), theory('equality')], [c_63894])).
% 15.67/6.10  tff(c_58367, plain, (![A_69, B_70, C_8930]: (r2_hidden('#skF_10'('#skF_11'(A_69, B_70), k2_relat_1('#skF_11'(A_69, B_70)), C_8930), A_69) | ~r2_hidden(C_8930, k2_relat_1('#skF_11'(A_69, B_70))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_58363])).
% 15.67/6.10  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 15.67/6.10  tff(c_58365, plain, (![A_8929, C_8930, B_2]: (r2_hidden('#skF_10'(A_8929, k2_relat_1(A_8929), C_8930), B_2) | ~r1_tarski(k1_relat_1(A_8929), B_2) | ~r2_hidden(C_8930, k2_relat_1(A_8929)) | ~v1_funct_1(A_8929) | ~v1_relat_1(A_8929))), inference(resolution, [status(thm)], [c_58356, c_2])).
% 15.67/6.10  tff(c_58416, plain, (![A_8940, C_8941]: (k1_funct_1(A_8940, '#skF_10'(A_8940, k2_relat_1(A_8940), C_8941))=C_8941 | ~r2_hidden(C_8941, k2_relat_1(A_8940)) | ~v1_funct_1(A_8940) | ~v1_relat_1(A_8940))), inference(cnfTransformation, [status(thm)], [f_69])).
% 15.67/6.10  tff(c_58426, plain, (![C_8941, B_70, A_69]: (C_8941=B_70 | ~r2_hidden('#skF_10'('#skF_11'(A_69, B_70), k2_relat_1('#skF_11'(A_69, B_70)), C_8941), A_69) | ~r2_hidden(C_8941, k2_relat_1('#skF_11'(A_69, B_70))) | ~v1_funct_1('#skF_11'(A_69, B_70)) | ~v1_relat_1('#skF_11'(A_69, B_70)))), inference(superposition, [status(thm), theory('equality')], [c_58416, c_46])).
% 15.67/6.10  tff(c_64209, plain, (![C_9323, B_9324, A_9325]: (C_9323=B_9324 | ~r2_hidden('#skF_10'('#skF_11'(A_9325, B_9324), k2_relat_1('#skF_11'(A_9325, B_9324)), C_9323), A_9325) | ~r2_hidden(C_9323, k2_relat_1('#skF_11'(A_9325, B_9324))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_58426])).
% 15.67/6.10  tff(c_64213, plain, (![C_8930, B_9324, B_2]: (C_8930=B_9324 | ~r1_tarski(k1_relat_1('#skF_11'(B_2, B_9324)), B_2) | ~r2_hidden(C_8930, k2_relat_1('#skF_11'(B_2, B_9324))) | ~v1_funct_1('#skF_11'(B_2, B_9324)) | ~v1_relat_1('#skF_11'(B_2, B_9324)))), inference(resolution, [status(thm)], [c_58365, c_64209])).
% 15.67/6.10  tff(c_64221, plain, (![C_9326, B_9327, B_9328]: (C_9326=B_9327 | ~r2_hidden(C_9326, k2_relat_1('#skF_11'(B_9328, B_9327))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_14, c_48, c_64213])).
% 15.67/6.10  tff(c_64343, plain, (![B_9334, B_9335, B_9336]: ('#skF_1'(k2_relat_1('#skF_11'(B_9334, B_9335)), B_9336)=B_9335 | r1_tarski(k2_relat_1('#skF_11'(B_9334, B_9335)), B_9336))), inference(resolution, [status(thm)], [c_6, c_64221])).
% 15.67/6.10  tff(c_64360, plain, (![B_9334, B_9335]: (k1_relat_1('#skF_11'(B_9334, B_9335))!='#skF_12' | ~v1_funct_1('#skF_11'(B_9334, B_9335)) | ~v1_relat_1('#skF_11'(B_9334, B_9335)) | '#skF_1'(k2_relat_1('#skF_11'(B_9334, B_9335)), '#skF_12')=B_9335)), inference(resolution, [status(thm)], [c_64343, c_58174])).
% 15.67/6.10  tff(c_64373, plain, (![B_9337, B_9338]: (B_9337!='#skF_12' | '#skF_1'(k2_relat_1('#skF_11'(B_9337, B_9338)), '#skF_12')=B_9338)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_64360])).
% 15.67/6.10  tff(c_64421, plain, (![B_9342, B_9343]: (~r2_hidden(B_9342, '#skF_12') | r1_tarski(k2_relat_1('#skF_11'(B_9343, B_9342)), '#skF_12') | B_9343!='#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_64373, c_4])).
% 15.67/6.10  tff(c_64433, plain, (![B_9343, B_9342]: (k1_relat_1('#skF_11'(B_9343, B_9342))!='#skF_12' | ~v1_funct_1('#skF_11'(B_9343, B_9342)) | ~v1_relat_1('#skF_11'(B_9343, B_9342)) | ~r2_hidden(B_9342, '#skF_12') | B_9343!='#skF_12')), inference(resolution, [status(thm)], [c_64421, c_58174])).
% 15.67/6.10  tff(c_64442, plain, (![B_9342, B_9343]: (~r2_hidden(B_9342, '#skF_12') | B_9343!='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_48, c_64433])).
% 15.67/6.10  tff(c_64444, plain, (![B_9343]: (B_9343!='#skF_12')), inference(splitLeft, [status(thm)], [c_64442])).
% 15.67/6.10  tff(c_64452, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64444, c_58169])).
% 15.67/6.10  tff(c_64455, plain, (![B_9344]: (~r2_hidden(B_9344, '#skF_12'))), inference(splitRight, [status(thm)], [c_64442])).
% 15.67/6.10  tff(c_64727, plain, (![C_9353, B_9354]: (~r2_hidden(C_9353, k2_relat_1('#skF_11'('#skF_12', B_9354))))), inference(resolution, [status(thm)], [c_58367, c_64455])).
% 15.67/6.10  tff(c_64809, plain, $false, inference(resolution, [status(thm)], [c_64006, c_64727])).
% 15.67/6.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.67/6.10  
% 15.67/6.10  Inference rules
% 15.67/6.10  ----------------------
% 15.67/6.10  #Ref     : 1
% 15.67/6.10  #Sup     : 12003
% 15.67/6.10  #Fact    : 4
% 15.67/6.10  #Define  : 0
% 15.67/6.10  #Split   : 8
% 15.67/6.10  #Chain   : 0
% 15.67/6.10  #Close   : 0
% 15.67/6.10  
% 15.67/6.10  Ordering : KBO
% 15.67/6.10  
% 15.67/6.10  Simplification rules
% 15.67/6.10  ----------------------
% 15.67/6.10  #Subsume      : 5000
% 15.67/6.10  #Demod        : 422
% 15.67/6.11  #Tautology    : 354
% 15.67/6.11  #SimpNegUnit  : 11
% 15.67/6.11  #BackRed      : 10
% 15.67/6.11  
% 15.67/6.11  #Partial instantiations: 5148
% 15.67/6.11  #Strategies tried      : 1
% 15.67/6.11  
% 15.67/6.11  Timing (in seconds)
% 15.67/6.11  ----------------------
% 15.67/6.11  Preprocessing        : 0.31
% 15.67/6.11  Parsing              : 0.16
% 15.67/6.11  CNF conversion       : 0.03
% 15.67/6.11  Main loop            : 5.02
% 15.67/6.11  Inferencing          : 1.37
% 15.67/6.11  Reduction            : 0.96
% 15.67/6.11  Demodulation         : 0.63
% 15.67/6.11  BG Simplification    : 0.16
% 15.67/6.11  Subsumption          : 2.24
% 15.67/6.11  Abstraction          : 0.21
% 15.67/6.11  MUC search           : 0.00
% 15.67/6.11  Cooper               : 0.00
% 15.67/6.11  Total                : 5.37
% 15.67/6.11  Index Insertion      : 0.00
% 15.67/6.11  Index Deletion       : 0.00
% 15.67/6.11  Index Matching       : 0.00
% 15.67/6.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
