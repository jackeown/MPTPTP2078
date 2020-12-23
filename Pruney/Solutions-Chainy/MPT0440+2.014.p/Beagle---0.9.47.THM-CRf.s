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
% DateTime   : Thu Dec  3 09:58:19 EST 2020

% Result     : Theorem 52.78s
% Output     : CNFRefutation 52.78s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 128 expanded)
%              Number of leaves         :   35 (  60 expanded)
%              Depth                    :    9
%              Number of atoms          :   97 ( 210 expanded)
%              Number of equality atoms :   61 ( 132 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_14 > #skF_13 > #skF_10 > #skF_8 > #skF_11 > #skF_7 > #skF_2 > #skF_1 > #skF_9 > #skF_5 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

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

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( C = k1_tarski(k4_tarski(A,B))
         => ( k1_relat_1(C) = k1_tarski(A)
            & k2_relat_1(C) = k1_tarski(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_77,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] : k2_zfmisc_1(k1_tarski(A),k1_tarski(B)) = k1_tarski(k4_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),k1_tarski(D)))
    <=> ( A = C
        & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_56,plain,(
    k1_tarski(k4_tarski('#skF_12','#skF_13')) = '#skF_14' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_67,plain,(
    r2_hidden(k4_tarski('#skF_12','#skF_13'),'#skF_14') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_4])).

tff(c_133447,plain,(
    ! [C_118573,A_118574,D_118575] :
      ( r2_hidden(C_118573,k2_relat_1(A_118574))
      | ~ r2_hidden(k4_tarski(D_118575,C_118573),A_118574) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_133455,plain,(
    r2_hidden('#skF_13',k2_relat_1('#skF_14')) ),
    inference(resolution,[status(thm)],[c_67,c_133447])).

tff(c_133354,plain,(
    ! [A_118561,B_118562] :
      ( k2_xboole_0(k1_tarski(A_118561),B_118562) = B_118562
      | ~ r2_hidden(A_118561,B_118562) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_28,plain,(
    ! [A_17,B_18] : k2_xboole_0(k1_tarski(A_17),B_18) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_133359,plain,(
    ! [B_118562,A_118561] :
      ( k1_xboole_0 != B_118562
      | ~ r2_hidden(A_118561,B_118562) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133354,c_28])).

tff(c_133460,plain,(
    k2_relat_1('#skF_14') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_133455,c_133359])).

tff(c_24,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_3'(A_12,B_13),A_12)
      | k1_xboole_0 = A_12
      | k1_tarski(B_13) = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_136457,plain,(
    ! [A_122948,C_122949] :
      ( r2_hidden(k4_tarski('#skF_11'(A_122948,k2_relat_1(A_122948),C_122949),C_122949),A_122948)
      | ~ r2_hidden(C_122949,k2_relat_1(A_122948)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_20,plain,(
    ! [A_10,B_11] : k2_zfmisc_1(k1_tarski(A_10),k1_tarski(B_11)) = k1_tarski(k4_tarski(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_16,plain,(
    ! [D_9,B_7,A_6,C_8] :
      ( D_9 = B_7
      | ~ r2_hidden(k4_tarski(A_6,B_7),k2_zfmisc_1(k1_tarski(C_8),k1_tarski(D_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_133611,plain,(
    ! [D_118589,B_118590,A_118591,C_118592] :
      ( D_118589 = B_118590
      | ~ r2_hidden(k4_tarski(A_118591,B_118590),k1_tarski(k4_tarski(C_118592,D_118589))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16])).

tff(c_133620,plain,(
    ! [B_118590,A_118591] :
      ( B_118590 = '#skF_13'
      | ~ r2_hidden(k4_tarski(A_118591,B_118590),'#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_133611])).

tff(c_136513,plain,(
    ! [C_122983] :
      ( C_122983 = '#skF_13'
      | ~ r2_hidden(C_122983,k2_relat_1('#skF_14')) ) ),
    inference(resolution,[status(thm)],[c_136457,c_133620])).

tff(c_136538,plain,(
    ! [B_13] :
      ( '#skF_3'(k2_relat_1('#skF_14'),B_13) = '#skF_13'
      | k2_relat_1('#skF_14') = k1_xboole_0
      | k2_relat_1('#skF_14') = k1_tarski(B_13) ) ),
    inference(resolution,[status(thm)],[c_24,c_136513])).

tff(c_141007,plain,(
    ! [B_125152] :
      ( '#skF_3'(k2_relat_1('#skF_14'),B_125152) = '#skF_13'
      | k2_relat_1('#skF_14') = k1_tarski(B_125152) ) ),
    inference(negUnitSimplification,[status(thm)],[c_133460,c_136538])).

tff(c_22,plain,(
    ! [A_12,B_13] :
      ( '#skF_3'(A_12,B_13) != B_13
      | k1_xboole_0 = A_12
      | k1_tarski(B_13) = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_141015,plain,(
    ! [B_125152] :
      ( B_125152 != '#skF_13'
      | k2_relat_1('#skF_14') = k1_xboole_0
      | k2_relat_1('#skF_14') = k1_tarski(B_125152)
      | k2_relat_1('#skF_14') = k1_tarski(B_125152) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141007,c_22])).

tff(c_278212,plain,(
    k2_relat_1('#skF_14') = k1_tarski('#skF_13') ),
    inference(negUnitSimplification,[status(thm)],[c_133460,c_141015])).

tff(c_118,plain,(
    ! [C_69,A_70,D_71] :
      ( r2_hidden(C_69,k1_relat_1(A_70))
      | ~ r2_hidden(k4_tarski(C_69,D_71),A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_126,plain,(
    r2_hidden('#skF_12',k1_relat_1('#skF_14')) ),
    inference(resolution,[status(thm)],[c_67,c_118])).

tff(c_91,plain,(
    ! [A_64,B_65] :
      ( k2_xboole_0(k1_tarski(A_64),B_65) = B_65
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_96,plain,(
    ! [B_65,A_64] :
      ( k1_xboole_0 != B_65
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_28])).

tff(c_146,plain,(
    k1_relat_1('#skF_14') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_126,c_96])).

tff(c_3382,plain,(
    ! [C_3851,A_3852] :
      ( r2_hidden(k4_tarski(C_3851,'#skF_7'(A_3852,k1_relat_1(A_3852),C_3851)),A_3852)
      | ~ r2_hidden(C_3851,k1_relat_1(A_3852)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_18,plain,(
    ! [C_8,A_6,B_7,D_9] :
      ( C_8 = A_6
      | ~ r2_hidden(k4_tarski(A_6,B_7),k2_zfmisc_1(k1_tarski(C_8),k1_tarski(D_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_509,plain,(
    ! [C_112,A_113,B_114,D_115] :
      ( C_112 = A_113
      | ~ r2_hidden(k4_tarski(A_113,B_114),k1_tarski(k4_tarski(C_112,D_115))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18])).

tff(c_518,plain,(
    ! [A_113,B_114] :
      ( A_113 = '#skF_12'
      | ~ r2_hidden(k4_tarski(A_113,B_114),'#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_509])).

tff(c_3463,plain,(
    ! [C_3886] :
      ( C_3886 = '#skF_12'
      | ~ r2_hidden(C_3886,k1_relat_1('#skF_14')) ) ),
    inference(resolution,[status(thm)],[c_3382,c_518])).

tff(c_3483,plain,(
    ! [B_13] :
      ( '#skF_3'(k1_relat_1('#skF_14'),B_13) = '#skF_12'
      | k1_relat_1('#skF_14') = k1_xboole_0
      | k1_tarski(B_13) = k1_relat_1('#skF_14') ) ),
    inference(resolution,[status(thm)],[c_24,c_3463])).

tff(c_5829,plain,(
    ! [B_4996] :
      ( '#skF_3'(k1_relat_1('#skF_14'),B_4996) = '#skF_12'
      | k1_tarski(B_4996) = k1_relat_1('#skF_14') ) ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_3483])).

tff(c_5837,plain,(
    ! [B_4996] :
      ( B_4996 != '#skF_12'
      | k1_relat_1('#skF_14') = k1_xboole_0
      | k1_tarski(B_4996) = k1_relat_1('#skF_14')
      | k1_tarski(B_4996) = k1_relat_1('#skF_14') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5829,c_22])).

tff(c_133333,plain,(
    k1_tarski('#skF_12') = k1_relat_1('#skF_14') ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_5837])).

tff(c_54,plain,
    ( k2_relat_1('#skF_14') != k1_tarski('#skF_13')
    | k1_tarski('#skF_12') != k1_relat_1('#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_90,plain,(
    k1_tarski('#skF_12') != k1_relat_1('#skF_14') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_133338,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_133333,c_90])).

tff(c_133339,plain,(
    k2_relat_1('#skF_14') != k1_tarski('#skF_13') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_278235,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_278212,c_133339])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:39:25 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 52.78/41.91  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 52.78/41.92  
% 52.78/41.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 52.78/41.92  %$ r2_hidden > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_14 > #skF_13 > #skF_10 > #skF_8 > #skF_11 > #skF_7 > #skF_2 > #skF_1 > #skF_9 > #skF_5 > #skF_12 > #skF_4
% 52.78/41.92  
% 52.78/41.92  %Foreground sorts:
% 52.78/41.92  
% 52.78/41.92  
% 52.78/41.92  %Background operators:
% 52.78/41.92  
% 52.78/41.92  
% 52.78/41.92  %Foreground operators:
% 52.78/41.92  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 52.78/41.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 52.78/41.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 52.78/41.92  tff(k1_tarski, type, k1_tarski: $i > $i).
% 52.78/41.92  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 52.78/41.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 52.78/41.92  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 52.78/41.92  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 52.78/41.92  tff('#skF_14', type, '#skF_14': $i).
% 52.78/41.92  tff('#skF_13', type, '#skF_13': $i).
% 52.78/41.92  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 52.78/41.92  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 52.78/41.92  tff('#skF_11', type, '#skF_11': ($i * $i * $i) > $i).
% 52.78/41.92  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 52.78/41.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 52.78/41.92  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 52.78/41.92  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 52.78/41.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 52.78/41.92  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 52.78/41.92  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 52.78/41.92  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 52.78/41.92  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 52.78/41.92  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 52.78/41.92  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 52.78/41.92  tff('#skF_12', type, '#skF_12': $i).
% 52.78/41.92  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 52.78/41.92  
% 52.78/41.93  tff(f_86, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => ((C = k1_tarski(k4_tarski(A, B))) => ((k1_relat_1(C) = k1_tarski(A)) & (k2_relat_1(C) = k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_relat_1)).
% 52.78/41.93  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 52.78/41.93  tff(f_77, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 52.78/41.93  tff(f_58, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 52.78/41.93  tff(f_61, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 52.78/41.93  tff(f_54, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 52.78/41.93  tff(f_40, axiom, (![A, B]: (k2_zfmisc_1(k1_tarski(A), k1_tarski(B)) = k1_tarski(k4_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 52.78/41.93  tff(f_38, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), k1_tarski(D))) <=> ((A = C) & (B = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_zfmisc_1)).
% 52.78/41.93  tff(f_69, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 52.78/41.93  tff(c_56, plain, (k1_tarski(k4_tarski('#skF_12', '#skF_13'))='#skF_14'), inference(cnfTransformation, [status(thm)], [f_86])).
% 52.78/41.93  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 52.78/41.93  tff(c_67, plain, (r2_hidden(k4_tarski('#skF_12', '#skF_13'), '#skF_14')), inference(superposition, [status(thm), theory('equality')], [c_56, c_4])).
% 52.78/41.93  tff(c_133447, plain, (![C_118573, A_118574, D_118575]: (r2_hidden(C_118573, k2_relat_1(A_118574)) | ~r2_hidden(k4_tarski(D_118575, C_118573), A_118574))), inference(cnfTransformation, [status(thm)], [f_77])).
% 52.78/41.93  tff(c_133455, plain, (r2_hidden('#skF_13', k2_relat_1('#skF_14'))), inference(resolution, [status(thm)], [c_67, c_133447])).
% 52.78/41.93  tff(c_133354, plain, (![A_118561, B_118562]: (k2_xboole_0(k1_tarski(A_118561), B_118562)=B_118562 | ~r2_hidden(A_118561, B_118562))), inference(cnfTransformation, [status(thm)], [f_58])).
% 52.78/41.93  tff(c_28, plain, (![A_17, B_18]: (k2_xboole_0(k1_tarski(A_17), B_18)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 52.78/41.93  tff(c_133359, plain, (![B_118562, A_118561]: (k1_xboole_0!=B_118562 | ~r2_hidden(A_118561, B_118562))), inference(superposition, [status(thm), theory('equality')], [c_133354, c_28])).
% 52.78/41.93  tff(c_133460, plain, (k2_relat_1('#skF_14')!=k1_xboole_0), inference(resolution, [status(thm)], [c_133455, c_133359])).
% 52.78/41.93  tff(c_24, plain, (![A_12, B_13]: (r2_hidden('#skF_3'(A_12, B_13), A_12) | k1_xboole_0=A_12 | k1_tarski(B_13)=A_12)), inference(cnfTransformation, [status(thm)], [f_54])).
% 52.78/41.93  tff(c_136457, plain, (![A_122948, C_122949]: (r2_hidden(k4_tarski('#skF_11'(A_122948, k2_relat_1(A_122948), C_122949), C_122949), A_122948) | ~r2_hidden(C_122949, k2_relat_1(A_122948)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 52.78/41.93  tff(c_20, plain, (![A_10, B_11]: (k2_zfmisc_1(k1_tarski(A_10), k1_tarski(B_11))=k1_tarski(k4_tarski(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 52.78/41.93  tff(c_16, plain, (![D_9, B_7, A_6, C_8]: (D_9=B_7 | ~r2_hidden(k4_tarski(A_6, B_7), k2_zfmisc_1(k1_tarski(C_8), k1_tarski(D_9))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 52.78/41.93  tff(c_133611, plain, (![D_118589, B_118590, A_118591, C_118592]: (D_118589=B_118590 | ~r2_hidden(k4_tarski(A_118591, B_118590), k1_tarski(k4_tarski(C_118592, D_118589))))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16])).
% 52.78/41.93  tff(c_133620, plain, (![B_118590, A_118591]: (B_118590='#skF_13' | ~r2_hidden(k4_tarski(A_118591, B_118590), '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_133611])).
% 52.78/41.93  tff(c_136513, plain, (![C_122983]: (C_122983='#skF_13' | ~r2_hidden(C_122983, k2_relat_1('#skF_14')))), inference(resolution, [status(thm)], [c_136457, c_133620])).
% 52.78/41.93  tff(c_136538, plain, (![B_13]: ('#skF_3'(k2_relat_1('#skF_14'), B_13)='#skF_13' | k2_relat_1('#skF_14')=k1_xboole_0 | k2_relat_1('#skF_14')=k1_tarski(B_13))), inference(resolution, [status(thm)], [c_24, c_136513])).
% 52.78/41.93  tff(c_141007, plain, (![B_125152]: ('#skF_3'(k2_relat_1('#skF_14'), B_125152)='#skF_13' | k2_relat_1('#skF_14')=k1_tarski(B_125152))), inference(negUnitSimplification, [status(thm)], [c_133460, c_136538])).
% 52.78/41.93  tff(c_22, plain, (![A_12, B_13]: ('#skF_3'(A_12, B_13)!=B_13 | k1_xboole_0=A_12 | k1_tarski(B_13)=A_12)), inference(cnfTransformation, [status(thm)], [f_54])).
% 52.78/41.93  tff(c_141015, plain, (![B_125152]: (B_125152!='#skF_13' | k2_relat_1('#skF_14')=k1_xboole_0 | k2_relat_1('#skF_14')=k1_tarski(B_125152) | k2_relat_1('#skF_14')=k1_tarski(B_125152))), inference(superposition, [status(thm), theory('equality')], [c_141007, c_22])).
% 52.78/41.93  tff(c_278212, plain, (k2_relat_1('#skF_14')=k1_tarski('#skF_13')), inference(negUnitSimplification, [status(thm)], [c_133460, c_141015])).
% 52.78/41.93  tff(c_118, plain, (![C_69, A_70, D_71]: (r2_hidden(C_69, k1_relat_1(A_70)) | ~r2_hidden(k4_tarski(C_69, D_71), A_70))), inference(cnfTransformation, [status(thm)], [f_69])).
% 52.78/41.93  tff(c_126, plain, (r2_hidden('#skF_12', k1_relat_1('#skF_14'))), inference(resolution, [status(thm)], [c_67, c_118])).
% 52.78/41.93  tff(c_91, plain, (![A_64, B_65]: (k2_xboole_0(k1_tarski(A_64), B_65)=B_65 | ~r2_hidden(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_58])).
% 52.78/41.93  tff(c_96, plain, (![B_65, A_64]: (k1_xboole_0!=B_65 | ~r2_hidden(A_64, B_65))), inference(superposition, [status(thm), theory('equality')], [c_91, c_28])).
% 52.78/41.93  tff(c_146, plain, (k1_relat_1('#skF_14')!=k1_xboole_0), inference(resolution, [status(thm)], [c_126, c_96])).
% 52.78/41.93  tff(c_3382, plain, (![C_3851, A_3852]: (r2_hidden(k4_tarski(C_3851, '#skF_7'(A_3852, k1_relat_1(A_3852), C_3851)), A_3852) | ~r2_hidden(C_3851, k1_relat_1(A_3852)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 52.78/41.93  tff(c_18, plain, (![C_8, A_6, B_7, D_9]: (C_8=A_6 | ~r2_hidden(k4_tarski(A_6, B_7), k2_zfmisc_1(k1_tarski(C_8), k1_tarski(D_9))))), inference(cnfTransformation, [status(thm)], [f_38])).
% 52.78/41.93  tff(c_509, plain, (![C_112, A_113, B_114, D_115]: (C_112=A_113 | ~r2_hidden(k4_tarski(A_113, B_114), k1_tarski(k4_tarski(C_112, D_115))))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18])).
% 52.78/41.93  tff(c_518, plain, (![A_113, B_114]: (A_113='#skF_12' | ~r2_hidden(k4_tarski(A_113, B_114), '#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_509])).
% 52.78/41.93  tff(c_3463, plain, (![C_3886]: (C_3886='#skF_12' | ~r2_hidden(C_3886, k1_relat_1('#skF_14')))), inference(resolution, [status(thm)], [c_3382, c_518])).
% 52.78/41.93  tff(c_3483, plain, (![B_13]: ('#skF_3'(k1_relat_1('#skF_14'), B_13)='#skF_12' | k1_relat_1('#skF_14')=k1_xboole_0 | k1_tarski(B_13)=k1_relat_1('#skF_14'))), inference(resolution, [status(thm)], [c_24, c_3463])).
% 52.78/41.93  tff(c_5829, plain, (![B_4996]: ('#skF_3'(k1_relat_1('#skF_14'), B_4996)='#skF_12' | k1_tarski(B_4996)=k1_relat_1('#skF_14'))), inference(negUnitSimplification, [status(thm)], [c_146, c_3483])).
% 52.78/41.93  tff(c_5837, plain, (![B_4996]: (B_4996!='#skF_12' | k1_relat_1('#skF_14')=k1_xboole_0 | k1_tarski(B_4996)=k1_relat_1('#skF_14') | k1_tarski(B_4996)=k1_relat_1('#skF_14'))), inference(superposition, [status(thm), theory('equality')], [c_5829, c_22])).
% 52.78/41.93  tff(c_133333, plain, (k1_tarski('#skF_12')=k1_relat_1('#skF_14')), inference(negUnitSimplification, [status(thm)], [c_146, c_5837])).
% 52.78/41.93  tff(c_54, plain, (k2_relat_1('#skF_14')!=k1_tarski('#skF_13') | k1_tarski('#skF_12')!=k1_relat_1('#skF_14')), inference(cnfTransformation, [status(thm)], [f_86])).
% 52.78/41.93  tff(c_90, plain, (k1_tarski('#skF_12')!=k1_relat_1('#skF_14')), inference(splitLeft, [status(thm)], [c_54])).
% 52.78/41.93  tff(c_133338, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_133333, c_90])).
% 52.78/41.93  tff(c_133339, plain, (k2_relat_1('#skF_14')!=k1_tarski('#skF_13')), inference(splitRight, [status(thm)], [c_54])).
% 52.78/41.93  tff(c_278235, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_278212, c_133339])).
% 52.78/41.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 52.78/41.93  
% 52.78/41.93  Inference rules
% 52.78/41.93  ----------------------
% 52.78/41.93  #Ref     : 76
% 52.78/41.93  #Sup     : 57728
% 52.78/41.93  #Fact    : 18
% 52.78/41.93  #Define  : 0
% 52.78/41.93  #Split   : 20
% 52.78/41.93  #Chain   : 0
% 52.78/41.93  #Close   : 0
% 52.78/41.93  
% 52.78/41.93  Ordering : KBO
% 52.78/41.93  
% 52.78/41.93  Simplification rules
% 52.78/41.93  ----------------------
% 52.78/41.93  #Subsume      : 38274
% 52.78/41.93  #Demod        : 12068
% 52.78/41.93  #Tautology    : 5805
% 52.78/41.93  #SimpNegUnit  : 2004
% 52.78/41.93  #BackRed      : 93
% 52.78/41.93  
% 52.78/41.93  #Partial instantiations: 124931
% 52.78/41.93  #Strategies tried      : 1
% 52.78/41.93  
% 52.78/41.93  Timing (in seconds)
% 52.78/41.93  ----------------------
% 52.78/41.94  Preprocessing        : 0.31
% 52.78/41.94  Parsing              : 0.16
% 52.78/41.94  CNF conversion       : 0.03
% 52.78/41.94  Main loop            : 40.86
% 52.78/41.94  Inferencing          : 4.69
% 52.78/41.94  Reduction            : 14.52
% 52.78/41.94  Demodulation         : 10.31
% 52.78/41.94  BG Simplification    : 0.29
% 52.78/41.94  Subsumption          : 20.39
% 52.78/41.94  Abstraction          : 0.63
% 52.78/41.94  MUC search           : 0.00
% 52.78/41.94  Cooper               : 0.00
% 52.78/41.94  Total                : 41.21
% 52.78/41.94  Index Insertion      : 0.00
% 52.78/41.94  Index Deletion       : 0.00
% 52.78/41.94  Index Matching       : 0.00
% 52.78/41.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
