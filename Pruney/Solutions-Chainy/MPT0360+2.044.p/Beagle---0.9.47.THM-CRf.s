%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:24 EST 2020

% Result     : Theorem 19.64s
% Output     : CNFRefutation 19.92s
% Verified   : 
% Statistics : Number of formulae       :  351 (4591 expanded)
%              Number of leaves         :   33 (1513 expanded)
%              Depth                    :   27
%              Number of atoms          :  558 (9295 expanded)
%              Number of equality atoms :  202 (2299 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_10,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,(
    ! [C_21,A_17] :
      ( r2_hidden(C_21,k1_zfmisc_1(A_17))
      | ~ r1_tarski(C_21,A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_17188,plain,(
    ! [B_508,A_509] :
      ( m1_subset_1(B_508,A_509)
      | ~ r2_hidden(B_508,A_509)
      | v1_xboole_0(A_509) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_61350,plain,(
    ! [C_1302,A_1303] :
      ( m1_subset_1(C_1302,k1_zfmisc_1(A_1303))
      | v1_xboole_0(k1_zfmisc_1(A_1303))
      | ~ r1_tarski(C_1302,A_1303) ) ),
    inference(resolution,[status(thm)],[c_24,c_17188])).

tff(c_42,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(A_24,B_25) = k3_subset_1(A_24,B_25)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(A_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_65612,plain,(
    ! [A_1457,C_1458] :
      ( k4_xboole_0(A_1457,C_1458) = k3_subset_1(A_1457,C_1458)
      | v1_xboole_0(k1_zfmisc_1(A_1457))
      | ~ r1_tarski(C_1458,A_1457) ) ),
    inference(resolution,[status(thm)],[c_61350,c_42])).

tff(c_65632,plain,(
    ! [A_6] :
      ( k4_xboole_0(A_6,k1_xboole_0) = k3_subset_1(A_6,k1_xboole_0)
      | v1_xboole_0(k1_zfmisc_1(A_6)) ) ),
    inference(resolution,[status(thm)],[c_8,c_65612])).

tff(c_65649,plain,(
    ! [A_1459] :
      ( k3_subset_1(A_1459,k1_xboole_0) = A_1459
      | v1_xboole_0(k1_zfmisc_1(A_1459)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_65632])).

tff(c_17123,plain,(
    ! [A_498,C_499,B_500] :
      ( r1_xboole_0(A_498,k4_xboole_0(C_499,B_500))
      | ~ r1_tarski(A_498,B_500) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_17135,plain,(
    ! [A_501,A_502] :
      ( r1_xboole_0(A_501,A_502)
      | ~ r1_tarski(A_501,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_17123])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,B_13) = A_12
      | ~ r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_17144,plain,(
    ! [A_503,A_504] :
      ( k4_xboole_0(A_503,A_504) = A_503
      | ~ r1_tarski(A_503,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_17135,c_16])).

tff(c_17149,plain,(
    ! [A_505] : k4_xboole_0(k1_xboole_0,A_505) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_17144])).

tff(c_20,plain,(
    ! [A_14,C_16,B_15] :
      ( r1_xboole_0(A_14,k4_xboole_0(C_16,B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_17169,plain,(
    ! [A_506,A_507] :
      ( r1_xboole_0(A_506,k1_xboole_0)
      | ~ r1_tarski(A_506,A_507) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17149,c_20])).

tff(c_17177,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_17169])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( ~ r1_xboole_0(B_11,A_10)
      | ~ r1_tarski(B_11,A_10)
      | v1_xboole_0(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_17195,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_17177,c_14])).

tff(c_17201,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_17195])).

tff(c_38,plain,(
    ! [B_23,A_22] :
      ( m1_subset_1(B_23,A_22)
      | ~ v1_xboole_0(B_23)
      | ~ v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_60970,plain,(
    ! [A_1281,B_1282] :
      ( k4_xboole_0(A_1281,B_1282) = k3_subset_1(A_1281,B_1282)
      | ~ m1_subset_1(B_1282,k1_zfmisc_1(A_1281)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_61807,plain,(
    ! [A_1328,B_1329] :
      ( k4_xboole_0(A_1328,B_1329) = k3_subset_1(A_1328,B_1329)
      | ~ v1_xboole_0(B_1329)
      | ~ v1_xboole_0(k1_zfmisc_1(A_1328)) ) ),
    inference(resolution,[status(thm)],[c_38,c_60970])).

tff(c_61811,plain,(
    ! [A_1328] :
      ( k4_xboole_0(A_1328,k1_xboole_0) = k3_subset_1(A_1328,k1_xboole_0)
      | ~ v1_xboole_0(k1_zfmisc_1(A_1328)) ) ),
    inference(resolution,[status(thm)],[c_17201,c_61807])).

tff(c_61818,plain,(
    ! [A_1328] :
      ( k3_subset_1(A_1328,k1_xboole_0) = A_1328
      | ~ v1_xboole_0(k1_zfmisc_1(A_1328)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_61811])).

tff(c_65674,plain,(
    ! [A_1459] : k3_subset_1(A_1459,k1_xboole_0) = A_1459 ),
    inference(resolution,[status(thm)],[c_65649,c_61818])).

tff(c_18091,plain,(
    ! [C_570,A_571] :
      ( m1_subset_1(C_570,k1_zfmisc_1(A_571))
      | v1_xboole_0(k1_zfmisc_1(A_571))
      | ~ r1_tarski(C_570,A_571) ) ),
    inference(resolution,[status(thm)],[c_24,c_17188])).

tff(c_58842,plain,(
    ! [A_1221,C_1222] :
      ( k4_xboole_0(A_1221,C_1222) = k3_subset_1(A_1221,C_1222)
      | v1_xboole_0(k1_zfmisc_1(A_1221))
      | ~ r1_tarski(C_1222,A_1221) ) ),
    inference(resolution,[status(thm)],[c_18091,c_42])).

tff(c_58868,plain,(
    ! [A_6] :
      ( k4_xboole_0(A_6,k1_xboole_0) = k3_subset_1(A_6,k1_xboole_0)
      | v1_xboole_0(k1_zfmisc_1(A_6)) ) ),
    inference(resolution,[status(thm)],[c_8,c_58842])).

tff(c_58893,plain,(
    ! [A_1223] :
      ( k3_subset_1(A_1223,k1_xboole_0) = A_1223
      | v1_xboole_0(k1_zfmisc_1(A_1223)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_58868])).

tff(c_17571,plain,(
    ! [A_546,B_547] :
      ( k4_xboole_0(A_546,B_547) = k3_subset_1(A_546,B_547)
      | ~ m1_subset_1(B_547,k1_zfmisc_1(A_546)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_18962,plain,(
    ! [A_616,B_617] :
      ( k4_xboole_0(A_616,B_617) = k3_subset_1(A_616,B_617)
      | ~ v1_xboole_0(B_617)
      | ~ v1_xboole_0(k1_zfmisc_1(A_616)) ) ),
    inference(resolution,[status(thm)],[c_38,c_17571])).

tff(c_18970,plain,(
    ! [A_616] :
      ( k4_xboole_0(A_616,k1_xboole_0) = k3_subset_1(A_616,k1_xboole_0)
      | ~ v1_xboole_0(k1_zfmisc_1(A_616)) ) ),
    inference(resolution,[status(thm)],[c_17201,c_18962])).

tff(c_18979,plain,(
    ! [A_616] :
      ( k3_subset_1(A_616,k1_xboole_0) = A_616
      | ~ v1_xboole_0(k1_zfmisc_1(A_616)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_18970])).

tff(c_58923,plain,(
    ! [A_1224] : k3_subset_1(A_1224,k1_xboole_0) = A_1224 ),
    inference(resolution,[status(thm)],[c_58893,c_18979])).

tff(c_46,plain,(
    ! [A_28,B_29] :
      ( k3_subset_1(A_28,k3_subset_1(A_28,B_29)) = B_29
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_18101,plain,(
    ! [A_571,C_570] :
      ( k3_subset_1(A_571,k3_subset_1(A_571,C_570)) = C_570
      | v1_xboole_0(k1_zfmisc_1(A_571))
      | ~ r1_tarski(C_570,A_571) ) ),
    inference(resolution,[status(thm)],[c_18091,c_46])).

tff(c_58929,plain,(
    ! [A_1224] :
      ( k3_subset_1(A_1224,A_1224) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_1224))
      | ~ r1_tarski(k1_xboole_0,A_1224) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58923,c_18101])).

tff(c_60216,plain,(
    ! [A_1237] :
      ( k3_subset_1(A_1237,A_1237) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_1237)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_58929])).

tff(c_50,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_17176,plain,(
    r1_xboole_0('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_50,c_17169])).

tff(c_17185,plain,
    ( ~ r1_tarski('#skF_4',k1_xboole_0)
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_17176,c_14])).

tff(c_17205,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_17185])).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_433,plain,(
    ! [A_87,B_88] :
      ( k4_xboole_0(A_87,B_88) = k3_subset_1(A_87,B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_446,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_433])).

tff(c_6,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_tarski(A_3,B_4)
      | ~ r1_tarski(A_3,k4_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_707,plain,(
    ! [A_102] :
      ( r1_tarski(A_102,'#skF_3')
      | ~ r1_tarski(A_102,k3_subset_1('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_446,c_6])).

tff(c_715,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_707])).

tff(c_73,plain,(
    ! [B_40,A_41] :
      ( v1_xboole_0(B_40)
      | ~ m1_subset_1(B_40,A_41)
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_81,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_73])).

tff(c_82,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_52,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,C_5)
      | ~ r1_tarski(A_3,k4_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_463,plain,(
    ! [A_89] :
      ( r1_xboole_0(A_89,'#skF_5')
      | ~ r1_tarski(A_89,k3_subset_1('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_446,c_4])).

tff(c_471,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_463])).

tff(c_483,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_471,c_16])).

tff(c_541,plain,(
    ! [A_93] :
      ( r1_xboole_0(A_93,'#skF_4')
      | ~ r1_tarski(A_93,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_20])).

tff(c_594,plain,(
    ! [A_95] :
      ( k4_xboole_0(A_95,'#skF_4') = A_95
      | ~ r1_tarski(A_95,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_541,c_16])).

tff(c_604,plain,(
    k4_xboole_0('#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_52,c_594])).

tff(c_12,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_496,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_12])).

tff(c_605,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_604,c_496])).

tff(c_107,plain,(
    ! [A_50,B_51] : k4_xboole_0(A_50,k4_xboole_0(A_50,B_51)) = k3_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_122,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_107])).

tff(c_531,plain,(
    k3_xboole_0('#skF_4',k1_xboole_0) = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_496,c_122])).

tff(c_630,plain,(
    k3_xboole_0('#skF_4',k1_xboole_0) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_605,c_531])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_657,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_630,c_2])).

tff(c_661,plain,(
    k5_xboole_0('#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_657])).

tff(c_174,plain,(
    ! [A_56,C_57,B_58] :
      ( r1_xboole_0(A_56,k4_xboole_0(C_57,B_58))
      | ~ r1_tarski(A_56,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_852,plain,(
    ! [A_108,C_109,B_110] :
      ( k4_xboole_0(A_108,k4_xboole_0(C_109,B_110)) = A_108
      | ~ r1_tarski(A_108,B_110) ) ),
    inference(resolution,[status(thm)],[c_174,c_16])).

tff(c_940,plain,(
    ! [C_111,B_112] :
      ( k3_xboole_0(C_111,B_112) = C_111
      | ~ r1_tarski(C_111,B_112) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_852,c_12])).

tff(c_957,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_715,c_940])).

tff(c_969,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_957,c_2])).

tff(c_972,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_661,c_969])).

tff(c_275,plain,(
    ! [B_66,A_67] :
      ( r2_hidden(B_66,A_67)
      | ~ m1_subset_1(B_66,A_67)
      | v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    ! [C_21,A_17] :
      ( r1_tarski(C_21,A_17)
      | ~ r2_hidden(C_21,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1566,plain,(
    ! [B_141,A_142] :
      ( r1_tarski(B_141,A_142)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(A_142))
      | v1_xboole_0(k1_zfmisc_1(A_142)) ) ),
    inference(resolution,[status(thm)],[c_275,c_22])).

tff(c_1579,plain,
    ( r1_tarski('#skF_5','#skF_3')
    | v1_xboole_0(k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_1566])).

tff(c_1585,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_1579])).

tff(c_2895,plain,(
    ! [A_219,C_220,B_221,A_222] :
      ( r1_xboole_0(A_219,k4_xboole_0(C_220,B_221))
      | ~ r1_tarski(A_219,A_222)
      | ~ r1_tarski(A_222,B_221) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_852,c_4])).

tff(c_3002,plain,(
    ! [C_225,B_226] :
      ( r1_xboole_0('#skF_5',k4_xboole_0(C_225,B_226))
      | ~ r1_tarski('#skF_3',B_226) ) ),
    inference(resolution,[status(thm)],[c_1585,c_2895])).

tff(c_3044,plain,
    ( r1_xboole_0('#skF_5','#skF_4')
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_972,c_3002])).

tff(c_3078,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3044])).

tff(c_97,plain,(
    ! [B_46,A_47] :
      ( m1_subset_1(B_46,A_47)
      | ~ r2_hidden(B_46,A_47)
      | v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_101,plain,(
    ! [C_21,A_17] :
      ( m1_subset_1(C_21,k1_zfmisc_1(A_17))
      | v1_xboole_0(k1_zfmisc_1(A_17))
      | ~ r1_tarski(C_21,A_17) ) ),
    inference(resolution,[status(thm)],[c_24,c_97])).

tff(c_1225,plain,(
    ! [C_124,A_125] :
      ( m1_subset_1(C_124,k1_zfmisc_1(A_125))
      | v1_xboole_0(k1_zfmisc_1(A_125))
      | ~ r1_tarski(C_124,A_125) ) ),
    inference(resolution,[status(thm)],[c_24,c_97])).

tff(c_9891,plain,(
    ! [A_374,C_375] :
      ( k4_xboole_0(A_374,C_375) = k3_subset_1(A_374,C_375)
      | v1_xboole_0(k1_zfmisc_1(A_374))
      | ~ r1_tarski(C_375,A_374) ) ),
    inference(resolution,[status(thm)],[c_1225,c_42])).

tff(c_9911,plain,(
    ! [A_6] :
      ( k4_xboole_0(A_6,k1_xboole_0) = k3_subset_1(A_6,k1_xboole_0)
      | v1_xboole_0(k1_zfmisc_1(A_6)) ) ),
    inference(resolution,[status(thm)],[c_8,c_9891])).

tff(c_10027,plain,(
    ! [A_376] :
      ( k3_subset_1(A_376,k1_xboole_0) = A_376
      | v1_xboole_0(k1_zfmisc_1(A_376)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_9911])).

tff(c_201,plain,(
    ! [A_61,C_62,B_63] :
      ( r1_xboole_0(A_61,C_62)
      | ~ r1_tarski(A_61,k4_xboole_0(B_63,C_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_216,plain,(
    ! [C_64] : r1_xboole_0(k1_xboole_0,C_64) ),
    inference(resolution,[status(thm)],[c_8,c_201])).

tff(c_219,plain,(
    ! [C_64] :
      ( ~ r1_tarski(k1_xboole_0,C_64)
      | v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_216,c_14])).

tff(c_225,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_219])).

tff(c_1653,plain,(
    ! [A_143,B_144] :
      ( k4_xboole_0(A_143,B_144) = k3_subset_1(A_143,B_144)
      | ~ v1_xboole_0(B_144)
      | ~ v1_xboole_0(k1_zfmisc_1(A_143)) ) ),
    inference(resolution,[status(thm)],[c_38,c_433])).

tff(c_1657,plain,(
    ! [A_143] :
      ( k4_xboole_0(A_143,k1_xboole_0) = k3_subset_1(A_143,k1_xboole_0)
      | ~ v1_xboole_0(k1_zfmisc_1(A_143)) ) ),
    inference(resolution,[status(thm)],[c_225,c_1653])).

tff(c_1660,plain,(
    ! [A_143] :
      ( k3_subset_1(A_143,k1_xboole_0) = A_143
      | ~ v1_xboole_0(k1_zfmisc_1(A_143)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1657])).

tff(c_10048,plain,(
    ! [A_377] : k3_subset_1(A_377,k1_xboole_0) = A_377 ),
    inference(resolution,[status(thm)],[c_10027,c_1660])).

tff(c_44,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(k3_subset_1(A_26,B_27),k1_zfmisc_1(A_26))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_10278,plain,(
    ! [A_381] :
      ( m1_subset_1(A_381,k1_zfmisc_1(A_381))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_381)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10048,c_44])).

tff(c_10281,plain,(
    ! [A_17] :
      ( m1_subset_1(A_17,k1_zfmisc_1(A_17))
      | v1_xboole_0(k1_zfmisc_1(A_17))
      | ~ r1_tarski(k1_xboole_0,A_17) ) ),
    inference(resolution,[status(thm)],[c_101,c_10278])).

tff(c_10472,plain,(
    ! [A_385] :
      ( m1_subset_1(A_385,k1_zfmisc_1(A_385))
      | v1_xboole_0(k1_zfmisc_1(A_385)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10281])).

tff(c_284,plain,(
    ! [B_66,A_17] :
      ( r1_tarski(B_66,A_17)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_17))
      | v1_xboole_0(k1_zfmisc_1(A_17)) ) ),
    inference(resolution,[status(thm)],[c_275,c_22])).

tff(c_10500,plain,(
    ! [A_386] :
      ( r1_tarski(A_386,A_386)
      | v1_xboole_0(k1_zfmisc_1(A_386)) ) ),
    inference(resolution,[status(thm)],[c_10472,c_284])).

tff(c_10712,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_10500,c_82])).

tff(c_10778,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3078,c_10712])).

tff(c_10780,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_3044])).

tff(c_191,plain,(
    ! [A_56,C_57,B_58] :
      ( k4_xboole_0(A_56,k4_xboole_0(C_57,B_58)) = A_56
      | ~ r1_tarski(A_56,B_58) ) ),
    inference(resolution,[status(thm)],[c_174,c_16])).

tff(c_977,plain,(
    ! [A_56] :
      ( k4_xboole_0(A_56,'#skF_4') = A_56
      | ~ r1_tarski(A_56,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_972,c_191])).

tff(c_10892,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_10780,c_977])).

tff(c_16565,plain,(
    ! [A_489,C_490] :
      ( k4_xboole_0(A_489,C_490) = k3_subset_1(A_489,C_490)
      | v1_xboole_0(k1_zfmisc_1(A_489))
      | ~ r1_tarski(C_490,A_489) ) ),
    inference(resolution,[status(thm)],[c_1225,c_42])).

tff(c_16583,plain,
    ( k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4')
    | v1_xboole_0(k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_715,c_16565])).

tff(c_16603,plain,
    ( k3_subset_1('#skF_3','#skF_4') = '#skF_3'
    | v1_xboole_0(k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10892,c_16583])).

tff(c_16604,plain,(
    k3_subset_1('#skF_3','#skF_4') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_16603])).

tff(c_14604,plain,(
    ! [A_446,C_447] :
      ( k3_subset_1(A_446,k3_subset_1(A_446,C_447)) = C_447
      | v1_xboole_0(k1_zfmisc_1(A_446))
      | ~ r1_tarski(C_447,A_446) ) ),
    inference(resolution,[status(thm)],[c_1225,c_46])).

tff(c_14669,plain,(
    ! [C_447] :
      ( k3_subset_1('#skF_3',k3_subset_1('#skF_3',C_447)) = C_447
      | ~ r1_tarski(C_447,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_14604,c_82])).

tff(c_16613,plain,
    ( k3_subset_1('#skF_3','#skF_3') = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16604,c_14669])).

tff(c_16630,plain,(
    k3_subset_1('#skF_3','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_715,c_16613])).

tff(c_16587,plain,(
    ! [A_6] :
      ( k4_xboole_0(A_6,k1_xboole_0) = k3_subset_1(A_6,k1_xboole_0)
      | v1_xboole_0(k1_zfmisc_1(A_6)) ) ),
    inference(resolution,[status(thm)],[c_8,c_16565])).

tff(c_17059,plain,(
    ! [A_492] :
      ( k3_subset_1(A_492,k1_xboole_0) = A_492
      | v1_xboole_0(k1_zfmisc_1(A_492)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_16587])).

tff(c_17080,plain,(
    ! [A_493] : k3_subset_1(A_493,k1_xboole_0) = A_493 ),
    inference(resolution,[status(thm)],[c_17059,c_1660])).

tff(c_17087,plain,
    ( k3_subset_1('#skF_3','#skF_3') = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_17080,c_14669])).

tff(c_17108,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_16630,c_17087])).

tff(c_17110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_17108])).

tff(c_17112,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_18982,plain,(
    ! [A_618] :
      ( k3_subset_1(A_618,k1_xboole_0) = A_618
      | ~ v1_xboole_0(k1_zfmisc_1(A_618)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_18970])).

tff(c_18986,plain,(
    k3_subset_1('#skF_3',k1_xboole_0) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_17112,c_18982])).

tff(c_17382,plain,(
    ! [A_530,B_531] :
      ( k3_subset_1(A_530,k3_subset_1(A_530,B_531)) = B_531
      | ~ m1_subset_1(B_531,k1_zfmisc_1(A_530)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_18705,plain,(
    ! [A_600,B_601] :
      ( k3_subset_1(A_600,k3_subset_1(A_600,B_601)) = B_601
      | ~ v1_xboole_0(B_601)
      | ~ v1_xboole_0(k1_zfmisc_1(A_600)) ) ),
    inference(resolution,[status(thm)],[c_38,c_17382])).

tff(c_18708,plain,(
    ! [B_601] :
      ( k3_subset_1('#skF_3',k3_subset_1('#skF_3',B_601)) = B_601
      | ~ v1_xboole_0(B_601) ) ),
    inference(resolution,[status(thm)],[c_17112,c_18705])).

tff(c_18993,plain,
    ( k3_subset_1('#skF_3','#skF_3') = k1_xboole_0
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18986,c_18708])).

tff(c_19002,plain,(
    k3_subset_1('#skF_3','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_17201,c_18993])).

tff(c_17441,plain,(
    ! [A_535,B_536] :
      ( m1_subset_1(k3_subset_1(A_535,B_536),k1_zfmisc_1(A_535))
      | ~ m1_subset_1(B_536,k1_zfmisc_1(A_535)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_40,plain,(
    ! [B_23,A_22] :
      ( v1_xboole_0(B_23)
      | ~ m1_subset_1(B_23,A_22)
      | ~ v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_18842,plain,(
    ! [A_610,B_611] :
      ( v1_xboole_0(k3_subset_1(A_610,B_611))
      | ~ v1_xboole_0(k1_zfmisc_1(A_610))
      | ~ m1_subset_1(B_611,k1_zfmisc_1(A_610)) ) ),
    inference(resolution,[status(thm)],[c_17441,c_40])).

tff(c_18858,plain,(
    ! [A_610,B_23] :
      ( v1_xboole_0(k3_subset_1(A_610,B_23))
      | ~ v1_xboole_0(B_23)
      | ~ v1_xboole_0(k1_zfmisc_1(A_610)) ) ),
    inference(resolution,[status(thm)],[c_38,c_18842])).

tff(c_18990,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_18986,c_18858])).

tff(c_19000,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17112,c_17201,c_18990])).

tff(c_17584,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_17571])).

tff(c_18003,plain,(
    ! [A_567,C_568,B_569] :
      ( k4_xboole_0(A_567,k4_xboole_0(C_568,B_569)) = A_567
      | ~ r1_tarski(A_567,B_569) ) ),
    inference(resolution,[status(thm)],[c_17123,c_16])).

tff(c_20574,plain,(
    ! [A_663,C_664,B_665,A_666] :
      ( r1_xboole_0(A_663,k4_xboole_0(C_664,B_665))
      | ~ r1_tarski(A_663,A_666)
      | ~ r1_tarski(A_666,B_665) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18003,c_4])).

tff(c_20600,plain,(
    ! [C_667,B_668] :
      ( r1_xboole_0('#skF_4',k4_xboole_0(C_667,B_668))
      | ~ r1_tarski('#skF_5',B_668) ) ),
    inference(resolution,[status(thm)],[c_52,c_20574])).

tff(c_20660,plain,
    ( r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5'))
    | ~ r1_tarski('#skF_5','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_17584,c_20600])).

tff(c_20790,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_20660])).

tff(c_17192,plain,(
    ! [C_21,A_17] :
      ( m1_subset_1(C_21,k1_zfmisc_1(A_17))
      | v1_xboole_0(k1_zfmisc_1(A_17))
      | ~ r1_tarski(C_21,A_17) ) ),
    inference(resolution,[status(thm)],[c_24,c_17188])).

tff(c_26458,plain,(
    ! [A_814,C_815] :
      ( k4_xboole_0(A_814,C_815) = k3_subset_1(A_814,C_815)
      | v1_xboole_0(k1_zfmisc_1(A_814))
      | ~ r1_tarski(C_815,A_814) ) ),
    inference(resolution,[status(thm)],[c_18091,c_42])).

tff(c_26476,plain,(
    ! [A_6] :
      ( k4_xboole_0(A_6,k1_xboole_0) = k3_subset_1(A_6,k1_xboole_0)
      | v1_xboole_0(k1_zfmisc_1(A_6)) ) ),
    inference(resolution,[status(thm)],[c_8,c_26458])).

tff(c_26491,plain,(
    ! [A_816] :
      ( k3_subset_1(A_816,k1_xboole_0) = A_816
      | v1_xboole_0(k1_zfmisc_1(A_816)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_26476])).

tff(c_26521,plain,(
    ! [A_817] : k3_subset_1(A_817,k1_xboole_0) = A_817 ),
    inference(resolution,[status(thm)],[c_26491,c_18979])).

tff(c_48511,plain,(
    ! [A_1067] :
      ( m1_subset_1(A_1067,k1_zfmisc_1(A_1067))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1067)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26521,c_44])).

tff(c_48516,plain,(
    ! [A_17] :
      ( m1_subset_1(A_17,k1_zfmisc_1(A_17))
      | v1_xboole_0(k1_zfmisc_1(A_17))
      | ~ r1_tarski(k1_xboole_0,A_17) ) ),
    inference(resolution,[status(thm)],[c_17192,c_48511])).

tff(c_48528,plain,(
    ! [A_1068] :
      ( m1_subset_1(A_1068,k1_zfmisc_1(A_1068))
      | v1_xboole_0(k1_zfmisc_1(A_1068)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_48516])).

tff(c_17276,plain,(
    ! [B_518,A_519] :
      ( r2_hidden(B_518,A_519)
      | ~ m1_subset_1(B_518,A_519)
      | v1_xboole_0(A_519) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_17285,plain,(
    ! [B_518,A_17] :
      ( r1_tarski(B_518,A_17)
      | ~ m1_subset_1(B_518,k1_zfmisc_1(A_17))
      | v1_xboole_0(k1_zfmisc_1(A_17)) ) ),
    inference(resolution,[status(thm)],[c_17276,c_22])).

tff(c_48556,plain,(
    ! [A_1069] :
      ( r1_tarski(A_1069,A_1069)
      | v1_xboole_0(k1_zfmisc_1(A_1069)) ) ),
    inference(resolution,[status(thm)],[c_48528,c_17285])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( r1_xboole_0(A_12,B_13)
      | k4_xboole_0(A_12,B_13) != A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_17118,plain,(
    ! [B_496,A_497] :
      ( ~ r1_xboole_0(B_496,A_497)
      | ~ r1_tarski(B_496,A_497)
      | v1_xboole_0(B_496) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_17466,plain,(
    ! [A_539,B_540] :
      ( ~ r1_tarski(A_539,B_540)
      | v1_xboole_0(A_539)
      | k4_xboole_0(A_539,B_540) != A_539 ) ),
    inference(resolution,[status(thm)],[c_18,c_17118])).

tff(c_17480,plain,
    ( v1_xboole_0('#skF_4')
    | k4_xboole_0('#skF_4','#skF_5') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_52,c_17466])).

tff(c_17481,plain,(
    k4_xboole_0('#skF_4','#skF_5') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_17480])).

tff(c_17483,plain,(
    ! [A_541,B_542] :
      ( k4_xboole_0(A_541,B_542) = k3_subset_1(A_541,B_542)
      | ~ m1_subset_1(B_542,k1_zfmisc_1(A_541)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_17496,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_17483])).

tff(c_17545,plain,(
    ! [A_545] :
      ( r1_xboole_0(A_545,'#skF_5')
      | ~ r1_tarski(A_545,k3_subset_1('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17496,c_4])).

tff(c_17553,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_17545])).

tff(c_17561,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_17553,c_16])).

tff(c_17568,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17481,c_17561])).

tff(c_17570,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_17480])).

tff(c_17640,plain,(
    ! [A_548] :
      ( r1_xboole_0(A_548,'#skF_4')
      | ~ r1_tarski(A_548,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17570,c_20])).

tff(c_17680,plain,(
    ! [A_552] :
      ( k4_xboole_0(A_552,'#skF_4') = A_552
      | ~ r1_tarski(A_552,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_17640,c_16])).

tff(c_17690,plain,(
    k4_xboole_0('#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_52,c_17680])).

tff(c_17591,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_17570,c_12])).

tff(c_17691,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17690,c_17591])).

tff(c_17722,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_17691,c_2])).

tff(c_17725,plain,(
    k5_xboole_0('#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17570,c_17722])).

tff(c_17240,plain,(
    ! [A_516,B_517] : k4_xboole_0(A_516,k4_xboole_0(A_516,B_517)) = k3_xboole_0(A_516,B_517) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_17272,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_17240])).

tff(c_28180,plain,(
    ! [A_833] :
      ( m1_subset_1(A_833,k1_zfmisc_1(A_833))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_833)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26521,c_44])).

tff(c_28185,plain,(
    ! [A_17] :
      ( m1_subset_1(A_17,k1_zfmisc_1(A_17))
      | v1_xboole_0(k1_zfmisc_1(A_17))
      | ~ r1_tarski(k1_xboole_0,A_17) ) ),
    inference(resolution,[status(thm)],[c_17192,c_28180])).

tff(c_28197,plain,(
    ! [A_834] :
      ( m1_subset_1(A_834,k1_zfmisc_1(A_834))
      | v1_xboole_0(k1_zfmisc_1(A_834)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_28185])).

tff(c_28211,plain,(
    ! [A_834] :
      ( k4_xboole_0(A_834,A_834) = k3_subset_1(A_834,A_834)
      | v1_xboole_0(k1_zfmisc_1(A_834)) ) ),
    inference(resolution,[status(thm)],[c_28197,c_42])).

tff(c_30945,plain,(
    ! [A_877] :
      ( k3_xboole_0(A_877,k1_xboole_0) = k3_subset_1(A_877,A_877)
      | v1_xboole_0(k1_zfmisc_1(A_877)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17272,c_28211])).

tff(c_28188,plain,(
    ! [A_833] :
      ( m1_subset_1(A_833,k1_zfmisc_1(A_833))
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k1_zfmisc_1(A_833)) ) ),
    inference(resolution,[status(thm)],[c_38,c_28180])).

tff(c_29344,plain,(
    ! [A_848] :
      ( m1_subset_1(A_848,k1_zfmisc_1(A_848))
      | ~ v1_xboole_0(k1_zfmisc_1(A_848)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17201,c_28188])).

tff(c_29358,plain,(
    ! [A_848] :
      ( k4_xboole_0(A_848,A_848) = k3_subset_1(A_848,A_848)
      | ~ v1_xboole_0(k1_zfmisc_1(A_848)) ) ),
    inference(resolution,[status(thm)],[c_29344,c_42])).

tff(c_29369,plain,(
    ! [A_848] :
      ( k3_xboole_0(A_848,k1_xboole_0) = k3_subset_1(A_848,A_848)
      | ~ v1_xboole_0(k1_zfmisc_1(A_848)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17272,c_29358])).

tff(c_31142,plain,(
    ! [A_878] : k3_xboole_0(A_878,k1_xboole_0) = k3_subset_1(A_878,A_878) ),
    inference(resolution,[status(thm)],[c_30945,c_29369])).

tff(c_17695,plain,(
    k3_xboole_0('#skF_4',k1_xboole_0) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_17690,c_17272])).

tff(c_31280,plain,(
    k3_subset_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_31142,c_17695])).

tff(c_26530,plain,(
    ! [A_817] :
      ( k3_subset_1(A_817,A_817) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_817))
      | ~ r1_tarski(k1_xboole_0,A_817) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26521,c_18101])).

tff(c_27009,plain,(
    ! [A_819] :
      ( k3_subset_1(A_819,A_819) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_819)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_26530])).

tff(c_17111,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_18981,plain,(
    ! [A_616] :
      ( k4_xboole_0(A_616,'#skF_5') = k3_subset_1(A_616,'#skF_5')
      | ~ v1_xboole_0(k1_zfmisc_1(A_616)) ) ),
    inference(resolution,[status(thm)],[c_17111,c_18962])).

tff(c_46308,plain,(
    ! [A_1058] :
      ( k4_xboole_0(A_1058,'#skF_5') = k3_subset_1(A_1058,'#skF_5')
      | k3_subset_1(A_1058,A_1058) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_27009,c_18981])).

tff(c_46480,plain,
    ( k3_subset_1('#skF_4','#skF_5') = '#skF_4'
    | k3_subset_1('#skF_4','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_46308,c_17570])).

tff(c_46684,plain,
    ( k3_subset_1('#skF_4','#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31280,c_46480])).

tff(c_46685,plain,(
    k3_subset_1('#skF_4','#skF_5') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_46684])).

tff(c_26549,plain,(
    ! [A_817] :
      ( k3_subset_1(A_817,A_817) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_817)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_26530])).

tff(c_31321,plain,(
    ! [A_817] :
      ( k3_xboole_0(A_817,k1_xboole_0) = k1_xboole_0
      | v1_xboole_0(k1_zfmisc_1(A_817)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26549,c_31142])).

tff(c_46743,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_46685,c_44])).

tff(c_46754,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_46743])).

tff(c_46760,plain,
    ( ~ v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_38,c_46754])).

tff(c_46764,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17111,c_46760])).

tff(c_46779,plain,(
    k3_xboole_0('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_31321,c_46764])).

tff(c_46807,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17695,c_46779])).

tff(c_46809,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_46807])).

tff(c_46811,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_46743])).

tff(c_47823,plain,(
    k3_subset_1('#skF_4',k3_subset_1('#skF_4','#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46811,c_46])).

tff(c_47837,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31280,c_46685,c_47823])).

tff(c_26515,plain,(
    ! [A_816] : k3_subset_1(A_816,k1_xboole_0) = A_816 ),
    inference(resolution,[status(thm)],[c_26491,c_18979])).

tff(c_26490,plain,
    ( k4_xboole_0('#skF_5','#skF_4') = k3_subset_1('#skF_5','#skF_4')
    | v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_52,c_26458])).

tff(c_26566,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_26490])).

tff(c_17388,plain,(
    ! [A_530,B_23] :
      ( k3_subset_1(A_530,k3_subset_1(A_530,B_23)) = B_23
      | ~ v1_xboole_0(B_23)
      | ~ v1_xboole_0(k1_zfmisc_1(A_530)) ) ),
    inference(resolution,[status(thm)],[c_38,c_17382])).

tff(c_27261,plain,(
    ! [B_821] :
      ( k3_subset_1('#skF_5',k3_subset_1('#skF_5',B_821)) = B_821
      | ~ v1_xboole_0(B_821) ) ),
    inference(resolution,[status(thm)],[c_26566,c_17388])).

tff(c_27306,plain,
    ( k3_subset_1('#skF_5','#skF_5') = k1_xboole_0
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26515,c_27261])).

tff(c_27338,plain,(
    k3_subset_1('#skF_5','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_17201,c_27306])).

tff(c_26591,plain,(
    k4_xboole_0('#skF_5','#skF_5') = k3_subset_1('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_26566,c_18981])).

tff(c_26791,plain,(
    k3_xboole_0('#skF_5',k1_xboole_0) = k3_subset_1('#skF_5','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_26591,c_17272])).

tff(c_27346,plain,(
    k3_xboole_0('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_27338,c_26791])).

tff(c_17319,plain,(
    ! [A_524] : k4_xboole_0(A_524,A_524) = k3_xboole_0(A_524,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_17240])).

tff(c_17328,plain,(
    ! [A_524] : k4_xboole_0(A_524,k3_xboole_0(A_524,k1_xboole_0)) = k3_xboole_0(A_524,A_524) ),
    inference(superposition,[status(thm),theory(equality)],[c_17319,c_12])).

tff(c_27578,plain,(
    k4_xboole_0('#skF_5',k1_xboole_0) = k3_xboole_0('#skF_5','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_27346,c_17328])).

tff(c_27602,plain,(
    k3_xboole_0('#skF_5','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_27578])).

tff(c_27645,plain,(
    k5_xboole_0('#skF_5','#skF_5') = k4_xboole_0('#skF_5','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_27602,c_2])).

tff(c_27659,plain,(
    k5_xboole_0('#skF_5','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_27346,c_17272,c_27645])).

tff(c_47915,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_47837,c_47837,c_27659])).

tff(c_48031,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17725,c_47915])).

tff(c_48033,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_48031])).

tff(c_48035,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_26490])).

tff(c_48754,plain,(
    r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_48556,c_48035])).

tff(c_48837,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20790,c_48754])).

tff(c_48839,plain,(
    r1_tarski('#skF_5','#skF_5') ),
    inference(splitRight,[status(thm)],[c_20660])).

tff(c_17648,plain,(
    ! [A_548] :
      ( k4_xboole_0(A_548,'#skF_4') = A_548
      | ~ r1_tarski(A_548,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_17640,c_16])).

tff(c_48863,plain,(
    k4_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_48839,c_17648])).

tff(c_58870,plain,
    ( k4_xboole_0('#skF_5','#skF_4') = k3_subset_1('#skF_5','#skF_4')
    | v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_52,c_58842])).

tff(c_58892,plain,
    ( k3_subset_1('#skF_5','#skF_4') = '#skF_5'
    | v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48863,c_58870])).

tff(c_58968,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_58892])).

tff(c_17569,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_17480])).

tff(c_18977,plain,(
    ! [A_616] :
      ( k4_xboole_0(A_616,'#skF_4') = k3_subset_1(A_616,'#skF_4')
      | ~ v1_xboole_0(k1_zfmisc_1(A_616)) ) ),
    inference(resolution,[status(thm)],[c_17569,c_18962])).

tff(c_58980,plain,(
    k4_xboole_0('#skF_5','#skF_4') = k3_subset_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_58968,c_18977])).

tff(c_58993,plain,(
    k3_subset_1('#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48863,c_58980])).

tff(c_17583,plain,(
    ! [A_546,B_23] :
      ( k4_xboole_0(A_546,B_23) = k3_subset_1(A_546,B_23)
      | ~ v1_xboole_0(B_23)
      | ~ v1_xboole_0(k1_zfmisc_1(A_546)) ) ),
    inference(resolution,[status(thm)],[c_38,c_17571])).

tff(c_19006,plain,(
    ! [A_546] :
      ( k4_xboole_0(A_546,'#skF_3') = k3_subset_1(A_546,'#skF_3')
      | ~ v1_xboole_0(k1_zfmisc_1(A_546)) ) ),
    inference(resolution,[status(thm)],[c_19000,c_17583])).

tff(c_58990,plain,(
    k4_xboole_0('#skF_5','#skF_3') = k3_subset_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_58968,c_19006])).

tff(c_58994,plain,(
    k4_xboole_0('#skF_5','#skF_5') = k3_subset_1('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_58968,c_18981])).

tff(c_49020,plain,(
    k4_xboole_0('#skF_5','#skF_5') = k3_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_48863,c_12])).

tff(c_59018,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k3_subset_1('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58994,c_49020])).

tff(c_18019,plain,(
    ! [A_567,C_568,B_569] :
      ( k4_xboole_0(A_567,A_567) = k3_xboole_0(A_567,k4_xboole_0(C_568,B_569))
      | ~ r1_tarski(A_567,B_569) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18003,c_12])).

tff(c_20069,plain,(
    ! [A_653,C_654,B_655] :
      ( k3_xboole_0(A_653,k4_xboole_0(C_654,B_655)) = k3_xboole_0(A_653,k1_xboole_0)
      | ~ r1_tarski(A_653,B_655) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17272,c_18019])).

tff(c_20162,plain,(
    ! [A_653] :
      ( k3_xboole_0(A_653,k1_xboole_0) = k3_xboole_0(A_653,'#skF_4')
      | ~ r1_tarski(A_653,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17570,c_20069])).

tff(c_48860,plain,(
    k3_xboole_0('#skF_5',k1_xboole_0) = k3_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_48839,c_20162])).

tff(c_18023,plain,(
    ! [C_568,B_569] :
      ( k3_xboole_0(C_568,B_569) = C_568
      | ~ r1_tarski(C_568,B_569) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18003,c_12])).

tff(c_48862,plain,(
    k3_xboole_0('#skF_5','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_48839,c_18023])).

tff(c_49056,plain,(
    k5_xboole_0('#skF_5','#skF_5') = k4_xboole_0('#skF_5','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_48862,c_2])).

tff(c_49063,plain,(
    k5_xboole_0('#skF_5','#skF_5') = k3_xboole_0('#skF_5',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17272,c_49056])).

tff(c_57088,plain,(
    k5_xboole_0('#skF_5','#skF_5') = k3_xboole_0('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48860,c_49063])).

tff(c_17389,plain,(
    k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_54,c_17382])).

tff(c_17607,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_5')) = k3_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_17584,c_12])).

tff(c_19270,plain,(
    ! [A_622,B_623] :
      ( k4_xboole_0(A_622,k3_subset_1(A_622,B_623)) = k3_subset_1(A_622,k3_subset_1(A_622,B_623))
      | ~ m1_subset_1(B_623,k1_zfmisc_1(A_622)) ) ),
    inference(resolution,[status(thm)],[c_44,c_17571])).

tff(c_19283,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_5')) = k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_54,c_19270])).

tff(c_19292,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17389,c_17607,c_19283])).

tff(c_17299,plain,(
    ! [A_521,B_522,C_523] :
      ( r1_tarski(A_521,B_522)
      | ~ r1_tarski(A_521,k4_xboole_0(B_522,C_523)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_17302,plain,(
    ! [A_521,A_8,B_9] :
      ( r1_tarski(A_521,A_8)
      | ~ r1_tarski(A_521,k3_xboole_0(A_8,B_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_17299])).

tff(c_19307,plain,(
    ! [A_521] :
      ( r1_tarski(A_521,'#skF_3')
      | ~ r1_tarski(A_521,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19292,c_17302])).

tff(c_48861,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_48839,c_19307])).

tff(c_48886,plain,(
    k3_xboole_0('#skF_5','#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_48861,c_18023])).

tff(c_49080,plain,(
    k5_xboole_0('#skF_5','#skF_5') = k4_xboole_0('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_48886,c_2])).

tff(c_57147,plain,(
    k4_xboole_0('#skF_5','#skF_3') = k3_xboole_0('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57088,c_49080])).

tff(c_59092,plain,(
    k4_xboole_0('#skF_5','#skF_3') = k3_subset_1('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59018,c_57147])).

tff(c_59304,plain,(
    k3_subset_1('#skF_5','#skF_5') = k3_subset_1('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58990,c_59092])).

tff(c_59927,plain,(
    ! [B_1232] :
      ( k3_subset_1('#skF_5',k3_subset_1('#skF_5',B_1232)) = B_1232
      | ~ v1_xboole_0(B_1232) ) ),
    inference(resolution,[status(thm)],[c_58968,c_17388])).

tff(c_59974,plain,
    ( k3_subset_1('#skF_5','#skF_5') = '#skF_4'
    | ~ v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_58993,c_59927])).

tff(c_60012,plain,(
    k3_subset_1('#skF_5','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17569,c_59304,c_59974])).

tff(c_58996,plain,(
    ! [B_23] :
      ( k3_subset_1('#skF_5',k3_subset_1('#skF_5',B_23)) = B_23
      | ~ v1_xboole_0(B_23) ) ),
    inference(resolution,[status(thm)],[c_58968,c_17388])).

tff(c_60089,plain,
    ( k3_subset_1('#skF_5','#skF_4') = '#skF_3'
    | ~ v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_60012,c_58996])).

tff(c_60106,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19000,c_58993,c_60089])).

tff(c_60154,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60106,c_50])).

tff(c_60184,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19002,c_60154])).

tff(c_60186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17205,c_60184])).

tff(c_60188,plain,(
    ~ v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_58892])).

tff(c_60272,plain,(
    k3_subset_1('#skF_5','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60216,c_60188])).

tff(c_60187,plain,(
    k3_subset_1('#skF_5','#skF_4') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_58892])).

tff(c_60207,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_60187,c_44])).

tff(c_60360,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_60207])).

tff(c_60363,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_5'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_17192,c_60360])).

tff(c_60369,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_60363])).

tff(c_60371,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60188,c_60369])).

tff(c_60373,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_60207])).

tff(c_60415,plain,(
    k3_subset_1('#skF_5',k3_subset_1('#skF_5','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_60373,c_46])).

tff(c_60429,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60272,c_60187,c_60415])).

tff(c_60431,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_60429])).

tff(c_60432,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_17185])).

tff(c_17148,plain,(
    ! [A_504] : k4_xboole_0(k1_xboole_0,A_504) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_17144])).

tff(c_60433,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_17185])).

tff(c_65628,plain,
    ( k4_xboole_0(k1_xboole_0,'#skF_4') = k3_subset_1(k1_xboole_0,'#skF_4')
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_60433,c_65612])).

tff(c_65644,plain,
    ( k3_subset_1(k1_xboole_0,'#skF_4') = k1_xboole_0
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17148,c_65628])).

tff(c_65734,plain,(
    v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_65644])).

tff(c_61816,plain,(
    ! [A_1328] :
      ( k4_xboole_0(A_1328,'#skF_4') = k3_subset_1(A_1328,'#skF_4')
      | ~ v1_xboole_0(k1_zfmisc_1(A_1328)) ) ),
    inference(resolution,[status(thm)],[c_60432,c_61807])).

tff(c_65746,plain,(
    k4_xboole_0(k1_xboole_0,'#skF_4') = k3_subset_1(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_65734,c_61816])).

tff(c_65761,plain,(
    k3_subset_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_17148,c_65746])).

tff(c_60725,plain,(
    ! [A_1265,B_1266] :
      ( k3_subset_1(A_1265,k3_subset_1(A_1265,B_1266)) = B_1266
      | ~ m1_subset_1(B_1266,k1_zfmisc_1(A_1265)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_60731,plain,(
    ! [A_1265,B_23] :
      ( k3_subset_1(A_1265,k3_subset_1(A_1265,B_23)) = B_23
      | ~ v1_xboole_0(B_23)
      | ~ v1_xboole_0(k1_zfmisc_1(A_1265)) ) ),
    inference(resolution,[status(thm)],[c_38,c_60725])).

tff(c_67380,plain,(
    ! [B_1481] :
      ( k3_subset_1(k1_xboole_0,k3_subset_1(k1_xboole_0,B_1481)) = B_1481
      | ~ v1_xboole_0(B_1481) ) ),
    inference(resolution,[status(thm)],[c_65734,c_60731])).

tff(c_67436,plain,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = '#skF_4'
    | ~ v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_65761,c_67380])).

tff(c_67483,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60432,c_65674,c_67436])).

tff(c_67485,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_67483])).

tff(c_67486,plain,(
    k3_subset_1(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_65644])).

tff(c_67487,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_65644])).

tff(c_67505,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_67486,c_44])).

tff(c_67716,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_67505])).

tff(c_67719,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_17192,c_67716])).

tff(c_67725,plain,(
    v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60433,c_67719])).

tff(c_67727,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67487,c_67725])).

tff(c_67729,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_67505])).

tff(c_67799,plain,(
    k3_subset_1(k1_xboole_0,k3_subset_1(k1_xboole_0,'#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_67729,c_46])).

tff(c_67813,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_65674,c_67486,c_67799])).

tff(c_67815,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_67813])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:20:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 19.64/10.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.92/10.41  
% 19.92/10.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.92/10.41  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 19.92/10.41  
% 19.92/10.41  %Foreground sorts:
% 19.92/10.41  
% 19.92/10.41  
% 19.92/10.41  %Background operators:
% 19.92/10.41  
% 19.92/10.41  
% 19.92/10.41  %Foreground operators:
% 19.92/10.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 19.92/10.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 19.92/10.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 19.92/10.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 19.92/10.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 19.92/10.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 19.92/10.41  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 19.92/10.41  tff('#skF_5', type, '#skF_5': $i).
% 19.92/10.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 19.92/10.41  tff('#skF_3', type, '#skF_3': $i).
% 19.92/10.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 19.92/10.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 19.92/10.41  tff('#skF_4', type, '#skF_4': $i).
% 19.92/10.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 19.92/10.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 19.92/10.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 19.92/10.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 19.92/10.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 19.92/10.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 19.92/10.41  
% 19.92/10.45  tff(f_96, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 19.92/10.45  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 19.92/10.45  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 19.92/10.45  tff(f_62, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 19.92/10.45  tff(f_75, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 19.92/10.45  tff(f_79, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 19.92/10.45  tff(f_55, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 19.92/10.45  tff(f_51, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 19.92/10.45  tff(f_47, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 19.92/10.45  tff(f_87, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 19.92/10.45  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 19.92/10.45  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 19.92/10.45  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 19.92/10.45  tff(f_83, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 19.92/10.45  tff(c_48, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_96])).
% 19.92/10.45  tff(c_10, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 19.92/10.45  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 19.92/10.45  tff(c_24, plain, (![C_21, A_17]: (r2_hidden(C_21, k1_zfmisc_1(A_17)) | ~r1_tarski(C_21, A_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 19.92/10.45  tff(c_17188, plain, (![B_508, A_509]: (m1_subset_1(B_508, A_509) | ~r2_hidden(B_508, A_509) | v1_xboole_0(A_509))), inference(cnfTransformation, [status(thm)], [f_75])).
% 19.92/10.45  tff(c_61350, plain, (![C_1302, A_1303]: (m1_subset_1(C_1302, k1_zfmisc_1(A_1303)) | v1_xboole_0(k1_zfmisc_1(A_1303)) | ~r1_tarski(C_1302, A_1303))), inference(resolution, [status(thm)], [c_24, c_17188])).
% 19.92/10.45  tff(c_42, plain, (![A_24, B_25]: (k4_xboole_0(A_24, B_25)=k3_subset_1(A_24, B_25) | ~m1_subset_1(B_25, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 19.92/10.45  tff(c_65612, plain, (![A_1457, C_1458]: (k4_xboole_0(A_1457, C_1458)=k3_subset_1(A_1457, C_1458) | v1_xboole_0(k1_zfmisc_1(A_1457)) | ~r1_tarski(C_1458, A_1457))), inference(resolution, [status(thm)], [c_61350, c_42])).
% 19.92/10.45  tff(c_65632, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=k3_subset_1(A_6, k1_xboole_0) | v1_xboole_0(k1_zfmisc_1(A_6)))), inference(resolution, [status(thm)], [c_8, c_65612])).
% 19.92/10.45  tff(c_65649, plain, (![A_1459]: (k3_subset_1(A_1459, k1_xboole_0)=A_1459 | v1_xboole_0(k1_zfmisc_1(A_1459)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_65632])).
% 19.92/10.45  tff(c_17123, plain, (![A_498, C_499, B_500]: (r1_xboole_0(A_498, k4_xboole_0(C_499, B_500)) | ~r1_tarski(A_498, B_500))), inference(cnfTransformation, [status(thm)], [f_55])).
% 19.92/10.45  tff(c_17135, plain, (![A_501, A_502]: (r1_xboole_0(A_501, A_502) | ~r1_tarski(A_501, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_17123])).
% 19.92/10.45  tff(c_16, plain, (![A_12, B_13]: (k4_xboole_0(A_12, B_13)=A_12 | ~r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 19.92/10.45  tff(c_17144, plain, (![A_503, A_504]: (k4_xboole_0(A_503, A_504)=A_503 | ~r1_tarski(A_503, k1_xboole_0))), inference(resolution, [status(thm)], [c_17135, c_16])).
% 19.92/10.45  tff(c_17149, plain, (![A_505]: (k4_xboole_0(k1_xboole_0, A_505)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_17144])).
% 19.92/10.45  tff(c_20, plain, (![A_14, C_16, B_15]: (r1_xboole_0(A_14, k4_xboole_0(C_16, B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 19.92/10.45  tff(c_17169, plain, (![A_506, A_507]: (r1_xboole_0(A_506, k1_xboole_0) | ~r1_tarski(A_506, A_507))), inference(superposition, [status(thm), theory('equality')], [c_17149, c_20])).
% 19.92/10.45  tff(c_17177, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_17169])).
% 19.92/10.45  tff(c_14, plain, (![B_11, A_10]: (~r1_xboole_0(B_11, A_10) | ~r1_tarski(B_11, A_10) | v1_xboole_0(B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 19.92/10.45  tff(c_17195, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0) | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_17177, c_14])).
% 19.92/10.45  tff(c_17201, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_17195])).
% 19.92/10.45  tff(c_38, plain, (![B_23, A_22]: (m1_subset_1(B_23, A_22) | ~v1_xboole_0(B_23) | ~v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_75])).
% 19.92/10.45  tff(c_60970, plain, (![A_1281, B_1282]: (k4_xboole_0(A_1281, B_1282)=k3_subset_1(A_1281, B_1282) | ~m1_subset_1(B_1282, k1_zfmisc_1(A_1281)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 19.92/10.45  tff(c_61807, plain, (![A_1328, B_1329]: (k4_xboole_0(A_1328, B_1329)=k3_subset_1(A_1328, B_1329) | ~v1_xboole_0(B_1329) | ~v1_xboole_0(k1_zfmisc_1(A_1328)))), inference(resolution, [status(thm)], [c_38, c_60970])).
% 19.92/10.45  tff(c_61811, plain, (![A_1328]: (k4_xboole_0(A_1328, k1_xboole_0)=k3_subset_1(A_1328, k1_xboole_0) | ~v1_xboole_0(k1_zfmisc_1(A_1328)))), inference(resolution, [status(thm)], [c_17201, c_61807])).
% 19.92/10.45  tff(c_61818, plain, (![A_1328]: (k3_subset_1(A_1328, k1_xboole_0)=A_1328 | ~v1_xboole_0(k1_zfmisc_1(A_1328)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_61811])).
% 19.92/10.45  tff(c_65674, plain, (![A_1459]: (k3_subset_1(A_1459, k1_xboole_0)=A_1459)), inference(resolution, [status(thm)], [c_65649, c_61818])).
% 19.92/10.45  tff(c_18091, plain, (![C_570, A_571]: (m1_subset_1(C_570, k1_zfmisc_1(A_571)) | v1_xboole_0(k1_zfmisc_1(A_571)) | ~r1_tarski(C_570, A_571))), inference(resolution, [status(thm)], [c_24, c_17188])).
% 19.92/10.45  tff(c_58842, plain, (![A_1221, C_1222]: (k4_xboole_0(A_1221, C_1222)=k3_subset_1(A_1221, C_1222) | v1_xboole_0(k1_zfmisc_1(A_1221)) | ~r1_tarski(C_1222, A_1221))), inference(resolution, [status(thm)], [c_18091, c_42])).
% 19.92/10.45  tff(c_58868, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=k3_subset_1(A_6, k1_xboole_0) | v1_xboole_0(k1_zfmisc_1(A_6)))), inference(resolution, [status(thm)], [c_8, c_58842])).
% 19.92/10.45  tff(c_58893, plain, (![A_1223]: (k3_subset_1(A_1223, k1_xboole_0)=A_1223 | v1_xboole_0(k1_zfmisc_1(A_1223)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_58868])).
% 19.92/10.45  tff(c_17571, plain, (![A_546, B_547]: (k4_xboole_0(A_546, B_547)=k3_subset_1(A_546, B_547) | ~m1_subset_1(B_547, k1_zfmisc_1(A_546)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 19.92/10.45  tff(c_18962, plain, (![A_616, B_617]: (k4_xboole_0(A_616, B_617)=k3_subset_1(A_616, B_617) | ~v1_xboole_0(B_617) | ~v1_xboole_0(k1_zfmisc_1(A_616)))), inference(resolution, [status(thm)], [c_38, c_17571])).
% 19.92/10.45  tff(c_18970, plain, (![A_616]: (k4_xboole_0(A_616, k1_xboole_0)=k3_subset_1(A_616, k1_xboole_0) | ~v1_xboole_0(k1_zfmisc_1(A_616)))), inference(resolution, [status(thm)], [c_17201, c_18962])).
% 19.92/10.45  tff(c_18979, plain, (![A_616]: (k3_subset_1(A_616, k1_xboole_0)=A_616 | ~v1_xboole_0(k1_zfmisc_1(A_616)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_18970])).
% 19.92/10.45  tff(c_58923, plain, (![A_1224]: (k3_subset_1(A_1224, k1_xboole_0)=A_1224)), inference(resolution, [status(thm)], [c_58893, c_18979])).
% 19.92/10.45  tff(c_46, plain, (![A_28, B_29]: (k3_subset_1(A_28, k3_subset_1(A_28, B_29))=B_29 | ~m1_subset_1(B_29, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 19.92/10.45  tff(c_18101, plain, (![A_571, C_570]: (k3_subset_1(A_571, k3_subset_1(A_571, C_570))=C_570 | v1_xboole_0(k1_zfmisc_1(A_571)) | ~r1_tarski(C_570, A_571))), inference(resolution, [status(thm)], [c_18091, c_46])).
% 19.92/10.45  tff(c_58929, plain, (![A_1224]: (k3_subset_1(A_1224, A_1224)=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_1224)) | ~r1_tarski(k1_xboole_0, A_1224))), inference(superposition, [status(thm), theory('equality')], [c_58923, c_18101])).
% 19.92/10.45  tff(c_60216, plain, (![A_1237]: (k3_subset_1(A_1237, A_1237)=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_1237)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_58929])).
% 19.92/10.45  tff(c_50, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 19.92/10.45  tff(c_17176, plain, (r1_xboole_0('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_50, c_17169])).
% 19.92/10.45  tff(c_17185, plain, (~r1_tarski('#skF_4', k1_xboole_0) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_17176, c_14])).
% 19.92/10.45  tff(c_17205, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_17185])).
% 19.92/10.45  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 19.92/10.45  tff(c_433, plain, (![A_87, B_88]: (k4_xboole_0(A_87, B_88)=k3_subset_1(A_87, B_88) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 19.92/10.45  tff(c_446, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_433])).
% 19.92/10.45  tff(c_6, plain, (![A_3, B_4, C_5]: (r1_tarski(A_3, B_4) | ~r1_tarski(A_3, k4_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 19.92/10.45  tff(c_707, plain, (![A_102]: (r1_tarski(A_102, '#skF_3') | ~r1_tarski(A_102, k3_subset_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_446, c_6])).
% 19.92/10.45  tff(c_715, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_707])).
% 19.92/10.45  tff(c_73, plain, (![B_40, A_41]: (v1_xboole_0(B_40) | ~m1_subset_1(B_40, A_41) | ~v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_75])).
% 19.92/10.45  tff(c_81, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_54, c_73])).
% 19.92/10.45  tff(c_82, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_81])).
% 19.92/10.45  tff(c_52, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_96])).
% 19.92/10.45  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, C_5) | ~r1_tarski(A_3, k4_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 19.92/10.45  tff(c_463, plain, (![A_89]: (r1_xboole_0(A_89, '#skF_5') | ~r1_tarski(A_89, k3_subset_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_446, c_4])).
% 19.92/10.45  tff(c_471, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_463])).
% 19.92/10.45  tff(c_483, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_471, c_16])).
% 19.92/10.45  tff(c_541, plain, (![A_93]: (r1_xboole_0(A_93, '#skF_4') | ~r1_tarski(A_93, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_483, c_20])).
% 19.92/10.45  tff(c_594, plain, (![A_95]: (k4_xboole_0(A_95, '#skF_4')=A_95 | ~r1_tarski(A_95, '#skF_5'))), inference(resolution, [status(thm)], [c_541, c_16])).
% 19.92/10.45  tff(c_604, plain, (k4_xboole_0('#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_52, c_594])).
% 19.92/10.45  tff(c_12, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 19.92/10.45  tff(c_496, plain, (k4_xboole_0('#skF_4', '#skF_4')=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_483, c_12])).
% 19.92/10.45  tff(c_605, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_604, c_496])).
% 19.92/10.45  tff(c_107, plain, (![A_50, B_51]: (k4_xboole_0(A_50, k4_xboole_0(A_50, B_51))=k3_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_39])).
% 19.92/10.45  tff(c_122, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_107])).
% 19.92/10.45  tff(c_531, plain, (k3_xboole_0('#skF_4', k1_xboole_0)=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_496, c_122])).
% 19.92/10.45  tff(c_630, plain, (k3_xboole_0('#skF_4', k1_xboole_0)='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_605, c_531])).
% 19.92/10.45  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 19.92/10.45  tff(c_657, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_630, c_2])).
% 19.92/10.45  tff(c_661, plain, (k5_xboole_0('#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_657])).
% 19.92/10.45  tff(c_174, plain, (![A_56, C_57, B_58]: (r1_xboole_0(A_56, k4_xboole_0(C_57, B_58)) | ~r1_tarski(A_56, B_58))), inference(cnfTransformation, [status(thm)], [f_55])).
% 19.92/10.45  tff(c_852, plain, (![A_108, C_109, B_110]: (k4_xboole_0(A_108, k4_xboole_0(C_109, B_110))=A_108 | ~r1_tarski(A_108, B_110))), inference(resolution, [status(thm)], [c_174, c_16])).
% 19.92/10.45  tff(c_940, plain, (![C_111, B_112]: (k3_xboole_0(C_111, B_112)=C_111 | ~r1_tarski(C_111, B_112))), inference(superposition, [status(thm), theory('equality')], [c_852, c_12])).
% 19.92/10.45  tff(c_957, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_715, c_940])).
% 19.92/10.45  tff(c_969, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_957, c_2])).
% 19.92/10.45  tff(c_972, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_661, c_969])).
% 19.92/10.45  tff(c_275, plain, (![B_66, A_67]: (r2_hidden(B_66, A_67) | ~m1_subset_1(B_66, A_67) | v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_75])).
% 19.92/10.45  tff(c_22, plain, (![C_21, A_17]: (r1_tarski(C_21, A_17) | ~r2_hidden(C_21, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 19.92/10.45  tff(c_1566, plain, (![B_141, A_142]: (r1_tarski(B_141, A_142) | ~m1_subset_1(B_141, k1_zfmisc_1(A_142)) | v1_xboole_0(k1_zfmisc_1(A_142)))), inference(resolution, [status(thm)], [c_275, c_22])).
% 19.92/10.45  tff(c_1579, plain, (r1_tarski('#skF_5', '#skF_3') | v1_xboole_0(k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_54, c_1566])).
% 19.92/10.45  tff(c_1585, plain, (r1_tarski('#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_82, c_1579])).
% 19.92/10.45  tff(c_2895, plain, (![A_219, C_220, B_221, A_222]: (r1_xboole_0(A_219, k4_xboole_0(C_220, B_221)) | ~r1_tarski(A_219, A_222) | ~r1_tarski(A_222, B_221))), inference(superposition, [status(thm), theory('equality')], [c_852, c_4])).
% 19.92/10.45  tff(c_3002, plain, (![C_225, B_226]: (r1_xboole_0('#skF_5', k4_xboole_0(C_225, B_226)) | ~r1_tarski('#skF_3', B_226))), inference(resolution, [status(thm)], [c_1585, c_2895])).
% 19.92/10.45  tff(c_3044, plain, (r1_xboole_0('#skF_5', '#skF_4') | ~r1_tarski('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_972, c_3002])).
% 19.92/10.45  tff(c_3078, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_3044])).
% 19.92/10.45  tff(c_97, plain, (![B_46, A_47]: (m1_subset_1(B_46, A_47) | ~r2_hidden(B_46, A_47) | v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_75])).
% 19.92/10.45  tff(c_101, plain, (![C_21, A_17]: (m1_subset_1(C_21, k1_zfmisc_1(A_17)) | v1_xboole_0(k1_zfmisc_1(A_17)) | ~r1_tarski(C_21, A_17))), inference(resolution, [status(thm)], [c_24, c_97])).
% 19.92/10.45  tff(c_1225, plain, (![C_124, A_125]: (m1_subset_1(C_124, k1_zfmisc_1(A_125)) | v1_xboole_0(k1_zfmisc_1(A_125)) | ~r1_tarski(C_124, A_125))), inference(resolution, [status(thm)], [c_24, c_97])).
% 19.92/10.45  tff(c_9891, plain, (![A_374, C_375]: (k4_xboole_0(A_374, C_375)=k3_subset_1(A_374, C_375) | v1_xboole_0(k1_zfmisc_1(A_374)) | ~r1_tarski(C_375, A_374))), inference(resolution, [status(thm)], [c_1225, c_42])).
% 19.92/10.45  tff(c_9911, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=k3_subset_1(A_6, k1_xboole_0) | v1_xboole_0(k1_zfmisc_1(A_6)))), inference(resolution, [status(thm)], [c_8, c_9891])).
% 19.92/10.45  tff(c_10027, plain, (![A_376]: (k3_subset_1(A_376, k1_xboole_0)=A_376 | v1_xboole_0(k1_zfmisc_1(A_376)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_9911])).
% 19.92/10.45  tff(c_201, plain, (![A_61, C_62, B_63]: (r1_xboole_0(A_61, C_62) | ~r1_tarski(A_61, k4_xboole_0(B_63, C_62)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 19.92/10.45  tff(c_216, plain, (![C_64]: (r1_xboole_0(k1_xboole_0, C_64))), inference(resolution, [status(thm)], [c_8, c_201])).
% 19.92/10.45  tff(c_219, plain, (![C_64]: (~r1_tarski(k1_xboole_0, C_64) | v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_216, c_14])).
% 19.92/10.45  tff(c_225, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_219])).
% 19.92/10.45  tff(c_1653, plain, (![A_143, B_144]: (k4_xboole_0(A_143, B_144)=k3_subset_1(A_143, B_144) | ~v1_xboole_0(B_144) | ~v1_xboole_0(k1_zfmisc_1(A_143)))), inference(resolution, [status(thm)], [c_38, c_433])).
% 19.92/10.45  tff(c_1657, plain, (![A_143]: (k4_xboole_0(A_143, k1_xboole_0)=k3_subset_1(A_143, k1_xboole_0) | ~v1_xboole_0(k1_zfmisc_1(A_143)))), inference(resolution, [status(thm)], [c_225, c_1653])).
% 19.92/10.45  tff(c_1660, plain, (![A_143]: (k3_subset_1(A_143, k1_xboole_0)=A_143 | ~v1_xboole_0(k1_zfmisc_1(A_143)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1657])).
% 19.92/10.45  tff(c_10048, plain, (![A_377]: (k3_subset_1(A_377, k1_xboole_0)=A_377)), inference(resolution, [status(thm)], [c_10027, c_1660])).
% 19.92/10.45  tff(c_44, plain, (![A_26, B_27]: (m1_subset_1(k3_subset_1(A_26, B_27), k1_zfmisc_1(A_26)) | ~m1_subset_1(B_27, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 19.92/10.45  tff(c_10278, plain, (![A_381]: (m1_subset_1(A_381, k1_zfmisc_1(A_381)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_381)))), inference(superposition, [status(thm), theory('equality')], [c_10048, c_44])).
% 19.92/10.45  tff(c_10281, plain, (![A_17]: (m1_subset_1(A_17, k1_zfmisc_1(A_17)) | v1_xboole_0(k1_zfmisc_1(A_17)) | ~r1_tarski(k1_xboole_0, A_17))), inference(resolution, [status(thm)], [c_101, c_10278])).
% 19.92/10.45  tff(c_10472, plain, (![A_385]: (m1_subset_1(A_385, k1_zfmisc_1(A_385)) | v1_xboole_0(k1_zfmisc_1(A_385)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10281])).
% 19.92/10.45  tff(c_284, plain, (![B_66, A_17]: (r1_tarski(B_66, A_17) | ~m1_subset_1(B_66, k1_zfmisc_1(A_17)) | v1_xboole_0(k1_zfmisc_1(A_17)))), inference(resolution, [status(thm)], [c_275, c_22])).
% 19.92/10.45  tff(c_10500, plain, (![A_386]: (r1_tarski(A_386, A_386) | v1_xboole_0(k1_zfmisc_1(A_386)))), inference(resolution, [status(thm)], [c_10472, c_284])).
% 19.92/10.45  tff(c_10712, plain, (r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_10500, c_82])).
% 19.92/10.45  tff(c_10778, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3078, c_10712])).
% 19.92/10.45  tff(c_10780, plain, (r1_tarski('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_3044])).
% 19.92/10.45  tff(c_191, plain, (![A_56, C_57, B_58]: (k4_xboole_0(A_56, k4_xboole_0(C_57, B_58))=A_56 | ~r1_tarski(A_56, B_58))), inference(resolution, [status(thm)], [c_174, c_16])).
% 19.92/10.45  tff(c_977, plain, (![A_56]: (k4_xboole_0(A_56, '#skF_4')=A_56 | ~r1_tarski(A_56, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_972, c_191])).
% 19.92/10.45  tff(c_10892, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_10780, c_977])).
% 19.92/10.45  tff(c_16565, plain, (![A_489, C_490]: (k4_xboole_0(A_489, C_490)=k3_subset_1(A_489, C_490) | v1_xboole_0(k1_zfmisc_1(A_489)) | ~r1_tarski(C_490, A_489))), inference(resolution, [status(thm)], [c_1225, c_42])).
% 19.92/10.45  tff(c_16583, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4') | v1_xboole_0(k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_715, c_16565])).
% 19.92/10.45  tff(c_16603, plain, (k3_subset_1('#skF_3', '#skF_4')='#skF_3' | v1_xboole_0(k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_10892, c_16583])).
% 19.92/10.45  tff(c_16604, plain, (k3_subset_1('#skF_3', '#skF_4')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_82, c_16603])).
% 19.92/10.45  tff(c_14604, plain, (![A_446, C_447]: (k3_subset_1(A_446, k3_subset_1(A_446, C_447))=C_447 | v1_xboole_0(k1_zfmisc_1(A_446)) | ~r1_tarski(C_447, A_446))), inference(resolution, [status(thm)], [c_1225, c_46])).
% 19.92/10.45  tff(c_14669, plain, (![C_447]: (k3_subset_1('#skF_3', k3_subset_1('#skF_3', C_447))=C_447 | ~r1_tarski(C_447, '#skF_3'))), inference(resolution, [status(thm)], [c_14604, c_82])).
% 19.92/10.45  tff(c_16613, plain, (k3_subset_1('#skF_3', '#skF_3')='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16604, c_14669])).
% 19.92/10.45  tff(c_16630, plain, (k3_subset_1('#skF_3', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_715, c_16613])).
% 19.92/10.45  tff(c_16587, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=k3_subset_1(A_6, k1_xboole_0) | v1_xboole_0(k1_zfmisc_1(A_6)))), inference(resolution, [status(thm)], [c_8, c_16565])).
% 19.92/10.45  tff(c_17059, plain, (![A_492]: (k3_subset_1(A_492, k1_xboole_0)=A_492 | v1_xboole_0(k1_zfmisc_1(A_492)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_16587])).
% 19.92/10.45  tff(c_17080, plain, (![A_493]: (k3_subset_1(A_493, k1_xboole_0)=A_493)), inference(resolution, [status(thm)], [c_17059, c_1660])).
% 19.92/10.45  tff(c_17087, plain, (k3_subset_1('#skF_3', '#skF_3')=k1_xboole_0 | ~r1_tarski(k1_xboole_0, '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_17080, c_14669])).
% 19.92/10.45  tff(c_17108, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_16630, c_17087])).
% 19.92/10.45  tff(c_17110, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_17108])).
% 19.92/10.45  tff(c_17112, plain, (v1_xboole_0(k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_81])).
% 19.92/10.45  tff(c_18982, plain, (![A_618]: (k3_subset_1(A_618, k1_xboole_0)=A_618 | ~v1_xboole_0(k1_zfmisc_1(A_618)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_18970])).
% 19.92/10.45  tff(c_18986, plain, (k3_subset_1('#skF_3', k1_xboole_0)='#skF_3'), inference(resolution, [status(thm)], [c_17112, c_18982])).
% 19.92/10.45  tff(c_17382, plain, (![A_530, B_531]: (k3_subset_1(A_530, k3_subset_1(A_530, B_531))=B_531 | ~m1_subset_1(B_531, k1_zfmisc_1(A_530)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 19.92/10.45  tff(c_18705, plain, (![A_600, B_601]: (k3_subset_1(A_600, k3_subset_1(A_600, B_601))=B_601 | ~v1_xboole_0(B_601) | ~v1_xboole_0(k1_zfmisc_1(A_600)))), inference(resolution, [status(thm)], [c_38, c_17382])).
% 19.92/10.45  tff(c_18708, plain, (![B_601]: (k3_subset_1('#skF_3', k3_subset_1('#skF_3', B_601))=B_601 | ~v1_xboole_0(B_601))), inference(resolution, [status(thm)], [c_17112, c_18705])).
% 19.92/10.45  tff(c_18993, plain, (k3_subset_1('#skF_3', '#skF_3')=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18986, c_18708])).
% 19.92/10.45  tff(c_19002, plain, (k3_subset_1('#skF_3', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_17201, c_18993])).
% 19.92/10.45  tff(c_17441, plain, (![A_535, B_536]: (m1_subset_1(k3_subset_1(A_535, B_536), k1_zfmisc_1(A_535)) | ~m1_subset_1(B_536, k1_zfmisc_1(A_535)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 19.92/10.45  tff(c_40, plain, (![B_23, A_22]: (v1_xboole_0(B_23) | ~m1_subset_1(B_23, A_22) | ~v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_75])).
% 19.92/10.45  tff(c_18842, plain, (![A_610, B_611]: (v1_xboole_0(k3_subset_1(A_610, B_611)) | ~v1_xboole_0(k1_zfmisc_1(A_610)) | ~m1_subset_1(B_611, k1_zfmisc_1(A_610)))), inference(resolution, [status(thm)], [c_17441, c_40])).
% 19.92/10.45  tff(c_18858, plain, (![A_610, B_23]: (v1_xboole_0(k3_subset_1(A_610, B_23)) | ~v1_xboole_0(B_23) | ~v1_xboole_0(k1_zfmisc_1(A_610)))), inference(resolution, [status(thm)], [c_38, c_18842])).
% 19.92/10.45  tff(c_18990, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k1_zfmisc_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_18986, c_18858])).
% 19.92/10.45  tff(c_19000, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_17112, c_17201, c_18990])).
% 19.92/10.45  tff(c_17584, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_17571])).
% 19.92/10.45  tff(c_18003, plain, (![A_567, C_568, B_569]: (k4_xboole_0(A_567, k4_xboole_0(C_568, B_569))=A_567 | ~r1_tarski(A_567, B_569))), inference(resolution, [status(thm)], [c_17123, c_16])).
% 19.92/10.45  tff(c_20574, plain, (![A_663, C_664, B_665, A_666]: (r1_xboole_0(A_663, k4_xboole_0(C_664, B_665)) | ~r1_tarski(A_663, A_666) | ~r1_tarski(A_666, B_665))), inference(superposition, [status(thm), theory('equality')], [c_18003, c_4])).
% 19.92/10.45  tff(c_20600, plain, (![C_667, B_668]: (r1_xboole_0('#skF_4', k4_xboole_0(C_667, B_668)) | ~r1_tarski('#skF_5', B_668))), inference(resolution, [status(thm)], [c_52, c_20574])).
% 19.92/10.45  tff(c_20660, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5')) | ~r1_tarski('#skF_5', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_17584, c_20600])).
% 19.92/10.45  tff(c_20790, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(splitLeft, [status(thm)], [c_20660])).
% 19.92/10.45  tff(c_17192, plain, (![C_21, A_17]: (m1_subset_1(C_21, k1_zfmisc_1(A_17)) | v1_xboole_0(k1_zfmisc_1(A_17)) | ~r1_tarski(C_21, A_17))), inference(resolution, [status(thm)], [c_24, c_17188])).
% 19.92/10.45  tff(c_26458, plain, (![A_814, C_815]: (k4_xboole_0(A_814, C_815)=k3_subset_1(A_814, C_815) | v1_xboole_0(k1_zfmisc_1(A_814)) | ~r1_tarski(C_815, A_814))), inference(resolution, [status(thm)], [c_18091, c_42])).
% 19.92/10.45  tff(c_26476, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=k3_subset_1(A_6, k1_xboole_0) | v1_xboole_0(k1_zfmisc_1(A_6)))), inference(resolution, [status(thm)], [c_8, c_26458])).
% 19.92/10.45  tff(c_26491, plain, (![A_816]: (k3_subset_1(A_816, k1_xboole_0)=A_816 | v1_xboole_0(k1_zfmisc_1(A_816)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_26476])).
% 19.92/10.45  tff(c_26521, plain, (![A_817]: (k3_subset_1(A_817, k1_xboole_0)=A_817)), inference(resolution, [status(thm)], [c_26491, c_18979])).
% 19.92/10.45  tff(c_48511, plain, (![A_1067]: (m1_subset_1(A_1067, k1_zfmisc_1(A_1067)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1067)))), inference(superposition, [status(thm), theory('equality')], [c_26521, c_44])).
% 19.92/10.45  tff(c_48516, plain, (![A_17]: (m1_subset_1(A_17, k1_zfmisc_1(A_17)) | v1_xboole_0(k1_zfmisc_1(A_17)) | ~r1_tarski(k1_xboole_0, A_17))), inference(resolution, [status(thm)], [c_17192, c_48511])).
% 19.92/10.45  tff(c_48528, plain, (![A_1068]: (m1_subset_1(A_1068, k1_zfmisc_1(A_1068)) | v1_xboole_0(k1_zfmisc_1(A_1068)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_48516])).
% 19.92/10.45  tff(c_17276, plain, (![B_518, A_519]: (r2_hidden(B_518, A_519) | ~m1_subset_1(B_518, A_519) | v1_xboole_0(A_519))), inference(cnfTransformation, [status(thm)], [f_75])).
% 19.92/10.45  tff(c_17285, plain, (![B_518, A_17]: (r1_tarski(B_518, A_17) | ~m1_subset_1(B_518, k1_zfmisc_1(A_17)) | v1_xboole_0(k1_zfmisc_1(A_17)))), inference(resolution, [status(thm)], [c_17276, c_22])).
% 19.92/10.45  tff(c_48556, plain, (![A_1069]: (r1_tarski(A_1069, A_1069) | v1_xboole_0(k1_zfmisc_1(A_1069)))), inference(resolution, [status(thm)], [c_48528, c_17285])).
% 19.92/10.45  tff(c_18, plain, (![A_12, B_13]: (r1_xboole_0(A_12, B_13) | k4_xboole_0(A_12, B_13)!=A_12)), inference(cnfTransformation, [status(thm)], [f_51])).
% 19.92/10.45  tff(c_17118, plain, (![B_496, A_497]: (~r1_xboole_0(B_496, A_497) | ~r1_tarski(B_496, A_497) | v1_xboole_0(B_496))), inference(cnfTransformation, [status(thm)], [f_47])).
% 19.92/10.45  tff(c_17466, plain, (![A_539, B_540]: (~r1_tarski(A_539, B_540) | v1_xboole_0(A_539) | k4_xboole_0(A_539, B_540)!=A_539)), inference(resolution, [status(thm)], [c_18, c_17118])).
% 19.92/10.45  tff(c_17480, plain, (v1_xboole_0('#skF_4') | k4_xboole_0('#skF_4', '#skF_5')!='#skF_4'), inference(resolution, [status(thm)], [c_52, c_17466])).
% 19.92/10.45  tff(c_17481, plain, (k4_xboole_0('#skF_4', '#skF_5')!='#skF_4'), inference(splitLeft, [status(thm)], [c_17480])).
% 19.92/10.45  tff(c_17483, plain, (![A_541, B_542]: (k4_xboole_0(A_541, B_542)=k3_subset_1(A_541, B_542) | ~m1_subset_1(B_542, k1_zfmisc_1(A_541)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 19.92/10.45  tff(c_17496, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_17483])).
% 19.92/10.45  tff(c_17545, plain, (![A_545]: (r1_xboole_0(A_545, '#skF_5') | ~r1_tarski(A_545, k3_subset_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_17496, c_4])).
% 19.92/10.45  tff(c_17553, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_50, c_17545])).
% 19.92/10.45  tff(c_17561, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_17553, c_16])).
% 19.92/10.45  tff(c_17568, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17481, c_17561])).
% 19.92/10.45  tff(c_17570, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_17480])).
% 19.92/10.45  tff(c_17640, plain, (![A_548]: (r1_xboole_0(A_548, '#skF_4') | ~r1_tarski(A_548, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_17570, c_20])).
% 19.92/10.45  tff(c_17680, plain, (![A_552]: (k4_xboole_0(A_552, '#skF_4')=A_552 | ~r1_tarski(A_552, '#skF_5'))), inference(resolution, [status(thm)], [c_17640, c_16])).
% 19.92/10.45  tff(c_17690, plain, (k4_xboole_0('#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_52, c_17680])).
% 19.92/10.45  tff(c_17591, plain, (k4_xboole_0('#skF_4', '#skF_4')=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_17570, c_12])).
% 19.92/10.45  tff(c_17691, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_17690, c_17591])).
% 19.92/10.45  tff(c_17722, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_17691, c_2])).
% 19.92/10.45  tff(c_17725, plain, (k5_xboole_0('#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_17570, c_17722])).
% 19.92/10.45  tff(c_17240, plain, (![A_516, B_517]: (k4_xboole_0(A_516, k4_xboole_0(A_516, B_517))=k3_xboole_0(A_516, B_517))), inference(cnfTransformation, [status(thm)], [f_39])).
% 19.92/10.45  tff(c_17272, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_17240])).
% 19.92/10.45  tff(c_28180, plain, (![A_833]: (m1_subset_1(A_833, k1_zfmisc_1(A_833)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_833)))), inference(superposition, [status(thm), theory('equality')], [c_26521, c_44])).
% 19.92/10.45  tff(c_28185, plain, (![A_17]: (m1_subset_1(A_17, k1_zfmisc_1(A_17)) | v1_xboole_0(k1_zfmisc_1(A_17)) | ~r1_tarski(k1_xboole_0, A_17))), inference(resolution, [status(thm)], [c_17192, c_28180])).
% 19.92/10.45  tff(c_28197, plain, (![A_834]: (m1_subset_1(A_834, k1_zfmisc_1(A_834)) | v1_xboole_0(k1_zfmisc_1(A_834)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_28185])).
% 19.92/10.45  tff(c_28211, plain, (![A_834]: (k4_xboole_0(A_834, A_834)=k3_subset_1(A_834, A_834) | v1_xboole_0(k1_zfmisc_1(A_834)))), inference(resolution, [status(thm)], [c_28197, c_42])).
% 19.92/10.45  tff(c_30945, plain, (![A_877]: (k3_xboole_0(A_877, k1_xboole_0)=k3_subset_1(A_877, A_877) | v1_xboole_0(k1_zfmisc_1(A_877)))), inference(demodulation, [status(thm), theory('equality')], [c_17272, c_28211])).
% 19.92/10.45  tff(c_28188, plain, (![A_833]: (m1_subset_1(A_833, k1_zfmisc_1(A_833)) | ~v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k1_zfmisc_1(A_833)))), inference(resolution, [status(thm)], [c_38, c_28180])).
% 19.92/10.45  tff(c_29344, plain, (![A_848]: (m1_subset_1(A_848, k1_zfmisc_1(A_848)) | ~v1_xboole_0(k1_zfmisc_1(A_848)))), inference(demodulation, [status(thm), theory('equality')], [c_17201, c_28188])).
% 19.92/10.45  tff(c_29358, plain, (![A_848]: (k4_xboole_0(A_848, A_848)=k3_subset_1(A_848, A_848) | ~v1_xboole_0(k1_zfmisc_1(A_848)))), inference(resolution, [status(thm)], [c_29344, c_42])).
% 19.92/10.45  tff(c_29369, plain, (![A_848]: (k3_xboole_0(A_848, k1_xboole_0)=k3_subset_1(A_848, A_848) | ~v1_xboole_0(k1_zfmisc_1(A_848)))), inference(demodulation, [status(thm), theory('equality')], [c_17272, c_29358])).
% 19.92/10.45  tff(c_31142, plain, (![A_878]: (k3_xboole_0(A_878, k1_xboole_0)=k3_subset_1(A_878, A_878))), inference(resolution, [status(thm)], [c_30945, c_29369])).
% 19.92/10.45  tff(c_17695, plain, (k3_xboole_0('#skF_4', k1_xboole_0)='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_17690, c_17272])).
% 19.92/10.45  tff(c_31280, plain, (k3_subset_1('#skF_4', '#skF_4')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_31142, c_17695])).
% 19.92/10.45  tff(c_26530, plain, (![A_817]: (k3_subset_1(A_817, A_817)=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_817)) | ~r1_tarski(k1_xboole_0, A_817))), inference(superposition, [status(thm), theory('equality')], [c_26521, c_18101])).
% 19.92/10.45  tff(c_27009, plain, (![A_819]: (k3_subset_1(A_819, A_819)=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_819)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_26530])).
% 19.92/10.45  tff(c_17111, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_81])).
% 19.92/10.45  tff(c_18981, plain, (![A_616]: (k4_xboole_0(A_616, '#skF_5')=k3_subset_1(A_616, '#skF_5') | ~v1_xboole_0(k1_zfmisc_1(A_616)))), inference(resolution, [status(thm)], [c_17111, c_18962])).
% 19.92/10.45  tff(c_46308, plain, (![A_1058]: (k4_xboole_0(A_1058, '#skF_5')=k3_subset_1(A_1058, '#skF_5') | k3_subset_1(A_1058, A_1058)=k1_xboole_0)), inference(resolution, [status(thm)], [c_27009, c_18981])).
% 19.92/10.45  tff(c_46480, plain, (k3_subset_1('#skF_4', '#skF_5')='#skF_4' | k3_subset_1('#skF_4', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_46308, c_17570])).
% 19.92/10.45  tff(c_46684, plain, (k3_subset_1('#skF_4', '#skF_5')='#skF_4' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_31280, c_46480])).
% 19.92/10.45  tff(c_46685, plain, (k3_subset_1('#skF_4', '#skF_5')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_48, c_46684])).
% 19.92/10.45  tff(c_26549, plain, (![A_817]: (k3_subset_1(A_817, A_817)=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_817)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_26530])).
% 19.92/10.45  tff(c_31321, plain, (![A_817]: (k3_xboole_0(A_817, k1_xboole_0)=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(A_817)))), inference(superposition, [status(thm), theory('equality')], [c_26549, c_31142])).
% 19.92/10.45  tff(c_46743, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_46685, c_44])).
% 19.92/10.45  tff(c_46754, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_46743])).
% 19.92/10.45  tff(c_46760, plain, (~v1_xboole_0('#skF_5') | ~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_38, c_46754])).
% 19.92/10.45  tff(c_46764, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_17111, c_46760])).
% 19.92/10.45  tff(c_46779, plain, (k3_xboole_0('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_31321, c_46764])).
% 19.92/10.45  tff(c_46807, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_17695, c_46779])).
% 19.92/10.45  tff(c_46809, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_46807])).
% 19.92/10.45  tff(c_46811, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_46743])).
% 19.92/10.45  tff(c_47823, plain, (k3_subset_1('#skF_4', k3_subset_1('#skF_4', '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_46811, c_46])).
% 19.92/10.45  tff(c_47837, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_31280, c_46685, c_47823])).
% 19.92/10.45  tff(c_26515, plain, (![A_816]: (k3_subset_1(A_816, k1_xboole_0)=A_816)), inference(resolution, [status(thm)], [c_26491, c_18979])).
% 19.92/10.45  tff(c_26490, plain, (k4_xboole_0('#skF_5', '#skF_4')=k3_subset_1('#skF_5', '#skF_4') | v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_52, c_26458])).
% 19.92/10.45  tff(c_26566, plain, (v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_26490])).
% 19.92/10.45  tff(c_17388, plain, (![A_530, B_23]: (k3_subset_1(A_530, k3_subset_1(A_530, B_23))=B_23 | ~v1_xboole_0(B_23) | ~v1_xboole_0(k1_zfmisc_1(A_530)))), inference(resolution, [status(thm)], [c_38, c_17382])).
% 19.92/10.45  tff(c_27261, plain, (![B_821]: (k3_subset_1('#skF_5', k3_subset_1('#skF_5', B_821))=B_821 | ~v1_xboole_0(B_821))), inference(resolution, [status(thm)], [c_26566, c_17388])).
% 19.92/10.45  tff(c_27306, plain, (k3_subset_1('#skF_5', '#skF_5')=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26515, c_27261])).
% 19.92/10.45  tff(c_27338, plain, (k3_subset_1('#skF_5', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_17201, c_27306])).
% 19.92/10.45  tff(c_26591, plain, (k4_xboole_0('#skF_5', '#skF_5')=k3_subset_1('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_26566, c_18981])).
% 19.92/10.45  tff(c_26791, plain, (k3_xboole_0('#skF_5', k1_xboole_0)=k3_subset_1('#skF_5', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_26591, c_17272])).
% 19.92/10.45  tff(c_27346, plain, (k3_xboole_0('#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_27338, c_26791])).
% 19.92/10.45  tff(c_17319, plain, (![A_524]: (k4_xboole_0(A_524, A_524)=k3_xboole_0(A_524, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_17240])).
% 19.92/10.45  tff(c_17328, plain, (![A_524]: (k4_xboole_0(A_524, k3_xboole_0(A_524, k1_xboole_0))=k3_xboole_0(A_524, A_524))), inference(superposition, [status(thm), theory('equality')], [c_17319, c_12])).
% 19.92/10.45  tff(c_27578, plain, (k4_xboole_0('#skF_5', k1_xboole_0)=k3_xboole_0('#skF_5', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_27346, c_17328])).
% 19.92/10.45  tff(c_27602, plain, (k3_xboole_0('#skF_5', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_27578])).
% 19.92/10.45  tff(c_27645, plain, (k5_xboole_0('#skF_5', '#skF_5')=k4_xboole_0('#skF_5', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_27602, c_2])).
% 19.92/10.45  tff(c_27659, plain, (k5_xboole_0('#skF_5', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_27346, c_17272, c_27645])).
% 19.92/10.45  tff(c_47915, plain, (k5_xboole_0('#skF_4', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_47837, c_47837, c_27659])).
% 19.92/10.45  tff(c_48031, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_17725, c_47915])).
% 19.92/10.45  tff(c_48033, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_48031])).
% 19.92/10.45  tff(c_48035, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(splitRight, [status(thm)], [c_26490])).
% 19.92/10.45  tff(c_48754, plain, (r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_48556, c_48035])).
% 19.92/10.45  tff(c_48837, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20790, c_48754])).
% 19.92/10.45  tff(c_48839, plain, (r1_tarski('#skF_5', '#skF_5')), inference(splitRight, [status(thm)], [c_20660])).
% 19.92/10.45  tff(c_17648, plain, (![A_548]: (k4_xboole_0(A_548, '#skF_4')=A_548 | ~r1_tarski(A_548, '#skF_5'))), inference(resolution, [status(thm)], [c_17640, c_16])).
% 19.92/10.45  tff(c_48863, plain, (k4_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_48839, c_17648])).
% 19.92/10.45  tff(c_58870, plain, (k4_xboole_0('#skF_5', '#skF_4')=k3_subset_1('#skF_5', '#skF_4') | v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_52, c_58842])).
% 19.92/10.45  tff(c_58892, plain, (k3_subset_1('#skF_5', '#skF_4')='#skF_5' | v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48863, c_58870])).
% 19.92/10.45  tff(c_58968, plain, (v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_58892])).
% 19.92/10.45  tff(c_17569, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_17480])).
% 19.92/10.45  tff(c_18977, plain, (![A_616]: (k4_xboole_0(A_616, '#skF_4')=k3_subset_1(A_616, '#skF_4') | ~v1_xboole_0(k1_zfmisc_1(A_616)))), inference(resolution, [status(thm)], [c_17569, c_18962])).
% 19.92/10.45  tff(c_58980, plain, (k4_xboole_0('#skF_5', '#skF_4')=k3_subset_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_58968, c_18977])).
% 19.92/10.45  tff(c_58993, plain, (k3_subset_1('#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_48863, c_58980])).
% 19.92/10.45  tff(c_17583, plain, (![A_546, B_23]: (k4_xboole_0(A_546, B_23)=k3_subset_1(A_546, B_23) | ~v1_xboole_0(B_23) | ~v1_xboole_0(k1_zfmisc_1(A_546)))), inference(resolution, [status(thm)], [c_38, c_17571])).
% 19.92/10.45  tff(c_19006, plain, (![A_546]: (k4_xboole_0(A_546, '#skF_3')=k3_subset_1(A_546, '#skF_3') | ~v1_xboole_0(k1_zfmisc_1(A_546)))), inference(resolution, [status(thm)], [c_19000, c_17583])).
% 19.92/10.45  tff(c_58990, plain, (k4_xboole_0('#skF_5', '#skF_3')=k3_subset_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_58968, c_19006])).
% 19.92/10.45  tff(c_58994, plain, (k4_xboole_0('#skF_5', '#skF_5')=k3_subset_1('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_58968, c_18981])).
% 19.92/10.45  tff(c_49020, plain, (k4_xboole_0('#skF_5', '#skF_5')=k3_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_48863, c_12])).
% 19.92/10.45  tff(c_59018, plain, (k3_xboole_0('#skF_5', '#skF_4')=k3_subset_1('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58994, c_49020])).
% 19.92/10.45  tff(c_18019, plain, (![A_567, C_568, B_569]: (k4_xboole_0(A_567, A_567)=k3_xboole_0(A_567, k4_xboole_0(C_568, B_569)) | ~r1_tarski(A_567, B_569))), inference(superposition, [status(thm), theory('equality')], [c_18003, c_12])).
% 19.92/10.45  tff(c_20069, plain, (![A_653, C_654, B_655]: (k3_xboole_0(A_653, k4_xboole_0(C_654, B_655))=k3_xboole_0(A_653, k1_xboole_0) | ~r1_tarski(A_653, B_655))), inference(demodulation, [status(thm), theory('equality')], [c_17272, c_18019])).
% 19.92/10.45  tff(c_20162, plain, (![A_653]: (k3_xboole_0(A_653, k1_xboole_0)=k3_xboole_0(A_653, '#skF_4') | ~r1_tarski(A_653, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_17570, c_20069])).
% 19.92/10.45  tff(c_48860, plain, (k3_xboole_0('#skF_5', k1_xboole_0)=k3_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_48839, c_20162])).
% 19.92/10.45  tff(c_18023, plain, (![C_568, B_569]: (k3_xboole_0(C_568, B_569)=C_568 | ~r1_tarski(C_568, B_569))), inference(superposition, [status(thm), theory('equality')], [c_18003, c_12])).
% 19.92/10.45  tff(c_48862, plain, (k3_xboole_0('#skF_5', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_48839, c_18023])).
% 19.92/10.45  tff(c_49056, plain, (k5_xboole_0('#skF_5', '#skF_5')=k4_xboole_0('#skF_5', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_48862, c_2])).
% 19.92/10.45  tff(c_49063, plain, (k5_xboole_0('#skF_5', '#skF_5')=k3_xboole_0('#skF_5', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_17272, c_49056])).
% 19.92/10.45  tff(c_57088, plain, (k5_xboole_0('#skF_5', '#skF_5')=k3_xboole_0('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48860, c_49063])).
% 19.92/10.45  tff(c_17389, plain, (k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_54, c_17382])).
% 19.92/10.45  tff(c_17607, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_5'))=k3_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_17584, c_12])).
% 19.92/10.45  tff(c_19270, plain, (![A_622, B_623]: (k4_xboole_0(A_622, k3_subset_1(A_622, B_623))=k3_subset_1(A_622, k3_subset_1(A_622, B_623)) | ~m1_subset_1(B_623, k1_zfmisc_1(A_622)))), inference(resolution, [status(thm)], [c_44, c_17571])).
% 19.92/10.45  tff(c_19283, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_5'))=k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_54, c_19270])).
% 19.92/10.45  tff(c_19292, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_17389, c_17607, c_19283])).
% 19.92/10.45  tff(c_17299, plain, (![A_521, B_522, C_523]: (r1_tarski(A_521, B_522) | ~r1_tarski(A_521, k4_xboole_0(B_522, C_523)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 19.92/10.45  tff(c_17302, plain, (![A_521, A_8, B_9]: (r1_tarski(A_521, A_8) | ~r1_tarski(A_521, k3_xboole_0(A_8, B_9)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_17299])).
% 19.92/10.45  tff(c_19307, plain, (![A_521]: (r1_tarski(A_521, '#skF_3') | ~r1_tarski(A_521, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_19292, c_17302])).
% 19.92/10.45  tff(c_48861, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_48839, c_19307])).
% 19.92/10.45  tff(c_48886, plain, (k3_xboole_0('#skF_5', '#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_48861, c_18023])).
% 19.92/10.45  tff(c_49080, plain, (k5_xboole_0('#skF_5', '#skF_5')=k4_xboole_0('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_48886, c_2])).
% 19.92/10.45  tff(c_57147, plain, (k4_xboole_0('#skF_5', '#skF_3')=k3_xboole_0('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_57088, c_49080])).
% 19.92/10.45  tff(c_59092, plain, (k4_xboole_0('#skF_5', '#skF_3')=k3_subset_1('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_59018, c_57147])).
% 19.92/10.45  tff(c_59304, plain, (k3_subset_1('#skF_5', '#skF_5')=k3_subset_1('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_58990, c_59092])).
% 19.92/10.45  tff(c_59927, plain, (![B_1232]: (k3_subset_1('#skF_5', k3_subset_1('#skF_5', B_1232))=B_1232 | ~v1_xboole_0(B_1232))), inference(resolution, [status(thm)], [c_58968, c_17388])).
% 19.92/10.45  tff(c_59974, plain, (k3_subset_1('#skF_5', '#skF_5')='#skF_4' | ~v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_58993, c_59927])).
% 19.92/10.45  tff(c_60012, plain, (k3_subset_1('#skF_5', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_17569, c_59304, c_59974])).
% 19.92/10.45  tff(c_58996, plain, (![B_23]: (k3_subset_1('#skF_5', k3_subset_1('#skF_5', B_23))=B_23 | ~v1_xboole_0(B_23))), inference(resolution, [status(thm)], [c_58968, c_17388])).
% 19.92/10.45  tff(c_60089, plain, (k3_subset_1('#skF_5', '#skF_4')='#skF_3' | ~v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_60012, c_58996])).
% 19.92/10.45  tff(c_60106, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_19000, c_58993, c_60089])).
% 19.92/10.45  tff(c_60154, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60106, c_50])).
% 19.92/10.45  tff(c_60184, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_19002, c_60154])).
% 19.92/10.45  tff(c_60186, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17205, c_60184])).
% 19.92/10.45  tff(c_60188, plain, (~v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(splitRight, [status(thm)], [c_58892])).
% 19.92/10.45  tff(c_60272, plain, (k3_subset_1('#skF_5', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_60216, c_60188])).
% 19.92/10.45  tff(c_60187, plain, (k3_subset_1('#skF_5', '#skF_4')='#skF_5'), inference(splitRight, [status(thm)], [c_58892])).
% 19.92/10.45  tff(c_60207, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_60187, c_44])).
% 19.92/10.45  tff(c_60360, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_60207])).
% 19.92/10.45  tff(c_60363, plain, (v1_xboole_0(k1_zfmisc_1('#skF_5')) | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_17192, c_60360])).
% 19.92/10.45  tff(c_60369, plain, (v1_xboole_0(k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_60363])).
% 19.92/10.45  tff(c_60371, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60188, c_60369])).
% 19.92/10.45  tff(c_60373, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_5'))), inference(splitRight, [status(thm)], [c_60207])).
% 19.92/10.45  tff(c_60415, plain, (k3_subset_1('#skF_5', k3_subset_1('#skF_5', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_60373, c_46])).
% 19.92/10.45  tff(c_60429, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_60272, c_60187, c_60415])).
% 19.92/10.45  tff(c_60431, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_60429])).
% 19.92/10.45  tff(c_60432, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_17185])).
% 19.92/10.45  tff(c_17148, plain, (![A_504]: (k4_xboole_0(k1_xboole_0, A_504)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_17144])).
% 19.92/10.45  tff(c_60433, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(splitRight, [status(thm)], [c_17185])).
% 19.92/10.45  tff(c_65628, plain, (k4_xboole_0(k1_xboole_0, '#skF_4')=k3_subset_1(k1_xboole_0, '#skF_4') | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_60433, c_65612])).
% 19.92/10.45  tff(c_65644, plain, (k3_subset_1(k1_xboole_0, '#skF_4')=k1_xboole_0 | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_17148, c_65628])).
% 19.92/10.45  tff(c_65734, plain, (v1_xboole_0(k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_65644])).
% 19.92/10.45  tff(c_61816, plain, (![A_1328]: (k4_xboole_0(A_1328, '#skF_4')=k3_subset_1(A_1328, '#skF_4') | ~v1_xboole_0(k1_zfmisc_1(A_1328)))), inference(resolution, [status(thm)], [c_60432, c_61807])).
% 19.92/10.45  tff(c_65746, plain, (k4_xboole_0(k1_xboole_0, '#skF_4')=k3_subset_1(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_65734, c_61816])).
% 19.92/10.45  tff(c_65761, plain, (k3_subset_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_17148, c_65746])).
% 19.92/10.45  tff(c_60725, plain, (![A_1265, B_1266]: (k3_subset_1(A_1265, k3_subset_1(A_1265, B_1266))=B_1266 | ~m1_subset_1(B_1266, k1_zfmisc_1(A_1265)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 19.92/10.45  tff(c_60731, plain, (![A_1265, B_23]: (k3_subset_1(A_1265, k3_subset_1(A_1265, B_23))=B_23 | ~v1_xboole_0(B_23) | ~v1_xboole_0(k1_zfmisc_1(A_1265)))), inference(resolution, [status(thm)], [c_38, c_60725])).
% 19.92/10.45  tff(c_67380, plain, (![B_1481]: (k3_subset_1(k1_xboole_0, k3_subset_1(k1_xboole_0, B_1481))=B_1481 | ~v1_xboole_0(B_1481))), inference(resolution, [status(thm)], [c_65734, c_60731])).
% 19.92/10.45  tff(c_67436, plain, (k3_subset_1(k1_xboole_0, k1_xboole_0)='#skF_4' | ~v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_65761, c_67380])).
% 19.92/10.45  tff(c_67483, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_60432, c_65674, c_67436])).
% 19.92/10.45  tff(c_67485, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_67483])).
% 19.92/10.45  tff(c_67486, plain, (k3_subset_1(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_65644])).
% 19.92/10.45  tff(c_67487, plain, (~v1_xboole_0(k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_65644])).
% 19.92/10.45  tff(c_67505, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_67486, c_44])).
% 19.92/10.45  tff(c_67716, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_67505])).
% 19.92/10.45  tff(c_67719, plain, (v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_17192, c_67716])).
% 19.92/10.45  tff(c_67725, plain, (v1_xboole_0(k1_zfmisc_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_60433, c_67719])).
% 19.92/10.45  tff(c_67727, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67487, c_67725])).
% 19.92/10.45  tff(c_67729, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_67505])).
% 19.92/10.45  tff(c_67799, plain, (k3_subset_1(k1_xboole_0, k3_subset_1(k1_xboole_0, '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_67729, c_46])).
% 19.92/10.45  tff(c_67813, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_65674, c_67486, c_67799])).
% 19.92/10.45  tff(c_67815, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_67813])).
% 19.92/10.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.92/10.45  
% 19.92/10.45  Inference rules
% 19.92/10.45  ----------------------
% 19.92/10.45  #Ref     : 0
% 19.92/10.45  #Sup     : 17087
% 19.92/10.45  #Fact    : 2
% 19.92/10.45  #Define  : 0
% 19.92/10.45  #Split   : 106
% 19.92/10.45  #Chain   : 0
% 19.92/10.45  #Close   : 0
% 19.92/10.45  
% 19.92/10.45  Ordering : KBO
% 19.92/10.45  
% 19.92/10.45  Simplification rules
% 19.92/10.45  ----------------------
% 19.92/10.45  #Subsume      : 3609
% 19.92/10.45  #Demod        : 10744
% 19.92/10.45  #Tautology    : 4504
% 19.92/10.45  #SimpNegUnit  : 98
% 19.92/10.45  #BackRed      : 510
% 19.92/10.45  
% 19.92/10.45  #Partial instantiations: 0
% 19.92/10.45  #Strategies tried      : 1
% 19.92/10.45  
% 19.92/10.45  Timing (in seconds)
% 19.92/10.45  ----------------------
% 19.92/10.46  Preprocessing        : 0.33
% 19.92/10.46  Parsing              : 0.17
% 19.92/10.46  CNF conversion       : 0.02
% 19.92/10.46  Main loop            : 9.28
% 19.92/10.46  Inferencing          : 1.86
% 19.92/10.46  Reduction            : 3.44
% 19.92/10.46  Demodulation         : 2.56
% 19.92/10.46  BG Simplification    : 0.24
% 19.92/10.46  Subsumption          : 3.09
% 19.92/10.46  Abstraction          : 0.28
% 19.92/10.46  MUC search           : 0.00
% 19.92/10.46  Cooper               : 0.00
% 19.92/10.46  Total                : 9.72
% 19.92/10.46  Index Insertion      : 0.00
% 19.92/10.46  Index Deletion       : 0.00
% 19.92/10.46  Index Matching       : 0.00
% 19.92/10.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
