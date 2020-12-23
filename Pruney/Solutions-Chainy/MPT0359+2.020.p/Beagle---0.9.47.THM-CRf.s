%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:11 EST 2020

% Result     : Theorem 4.08s
% Output     : CNFRefutation 4.12s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 187 expanded)
%              Number of leaves         :   35 (  74 expanded)
%              Depth                    :   11
%              Number of atoms          :  110 ( 258 expanded)
%              Number of equality atoms :   54 ( 132 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_71,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_78,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_45,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_14,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_44,plain,(
    ! [A_26] : k2_subset_1(A_26) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_52,plain,
    ( k2_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_60,plain,
    ( '#skF_3' != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_52])).

tff(c_179,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_58,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | k2_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_59,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_58])).

tff(c_231,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_59])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_233,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_50])).

tff(c_722,plain,(
    ! [A_81,B_82] :
      ( k4_xboole_0(A_81,B_82) = k3_subset_1(A_81,B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_735,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k3_subset_1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_233,c_722])).

tff(c_22,plain,(
    ! [A_18] : k5_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_48,plain,(
    ! [A_29] : ~ v1_xboole_0(k1_zfmisc_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_443,plain,(
    ! [B_69,A_70] :
      ( r2_hidden(B_69,A_70)
      | ~ m1_subset_1(B_69,A_70)
      | v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_24,plain,(
    ! [C_23,A_19] :
      ( r1_tarski(C_23,A_19)
      | ~ r2_hidden(C_23,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_450,plain,(
    ! [B_69,A_19] :
      ( r1_tarski(B_69,A_19)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_19))
      | v1_xboole_0(k1_zfmisc_1(A_19)) ) ),
    inference(resolution,[status(thm)],[c_443,c_24])).

tff(c_1107,plain,(
    ! [B_95,A_96] :
      ( r1_tarski(B_95,A_96)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_96)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_450])).

tff(c_1120,plain,(
    r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_233,c_1107])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1124,plain,(
    k3_xboole_0('#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1120,c_12])).

tff(c_10,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1143,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1124,c_10])).

tff(c_1146,plain,(
    k3_subset_1('#skF_4','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_735,c_22,c_1143])).

tff(c_232,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_179])).

tff(c_1154,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1146,c_232])).

tff(c_1162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1154])).

tff(c_1163,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_132,plain,(
    ! [B_39,A_40] : k5_xboole_0(B_39,A_40) = k5_xboole_0(A_40,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_148,plain,(
    ! [A_40] : k5_xboole_0(k1_xboole_0,A_40) = A_40 ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_16])).

tff(c_1887,plain,(
    ! [A_143,B_144] :
      ( k4_xboole_0(A_143,B_144) = k3_subset_1(A_143,B_144)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(A_143)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1900,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1887])).

tff(c_18,plain,(
    ! [A_13,B_14] : r1_xboole_0(k4_xboole_0(A_13,B_14),B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1311,plain,(
    ! [A_112,B_113] :
      ( k3_xboole_0(A_112,B_113) = k1_xboole_0
      | ~ r1_xboole_0(A_112,B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1319,plain,(
    ! [A_13,B_14] : k3_xboole_0(k4_xboole_0(A_13,B_14),B_14) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_1311])).

tff(c_1907,plain,(
    k3_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1900,c_1319])).

tff(c_1165,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1163,c_59])).

tff(c_1224,plain,(
    ! [A_106,B_107] :
      ( k3_xboole_0(A_106,B_107) = A_106
      | ~ r1_tarski(A_106,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1231,plain,(
    k3_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_1165,c_1224])).

tff(c_1918,plain,(
    k3_subset_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1907,c_1231])).

tff(c_1951,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1918,c_1900])).

tff(c_1383,plain,(
    ! [B_122,A_123] :
      ( r2_hidden(B_122,A_123)
      | ~ m1_subset_1(B_122,A_123)
      | v1_xboole_0(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1390,plain,(
    ! [B_122,A_19] :
      ( r1_tarski(B_122,A_19)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(A_19))
      | v1_xboole_0(k1_zfmisc_1(A_19)) ) ),
    inference(resolution,[status(thm)],[c_1383,c_24])).

tff(c_1400,plain,(
    ! [B_126,A_127] :
      ( r1_tarski(B_126,A_127)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(A_127)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1390])).

tff(c_1413,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_1400])).

tff(c_1417,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1413,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1422,plain,(
    ! [A_128,B_129] : k5_xboole_0(A_128,k3_xboole_0(A_128,B_129)) = k4_xboole_0(A_128,B_129) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2210,plain,(
    ! [A_155,B_156] : k5_xboole_0(A_155,k3_xboole_0(B_156,A_155)) = k4_xboole_0(A_155,B_156) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1422])).

tff(c_2254,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1417,c_2210])).

tff(c_2282,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1951,c_2254])).

tff(c_1500,plain,(
    ! [A_132,B_133,C_134] : k5_xboole_0(k5_xboole_0(A_132,B_133),C_134) = k5_xboole_0(A_132,k5_xboole_0(B_133,C_134)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1564,plain,(
    ! [A_18,C_134] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_134)) = k5_xboole_0(k1_xboole_0,C_134) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1500])).

tff(c_1577,plain,(
    ! [A_18,C_134] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_134)) = C_134 ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_1564])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1631,plain,(
    ! [A_137,C_138] : k5_xboole_0(A_137,k5_xboole_0(A_137,C_138)) = C_138 ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_1564])).

tff(c_1712,plain,(
    ! [A_139,B_140] : k5_xboole_0(A_139,k5_xboole_0(B_140,A_139)) = B_140 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1631])).

tff(c_1745,plain,(
    ! [A_18,C_134] : k5_xboole_0(k5_xboole_0(A_18,C_134),C_134) = A_18 ),
    inference(superposition,[status(thm),theory(equality)],[c_1577,c_1712])).

tff(c_2293,plain,(
    k5_xboole_0(k1_xboole_0,'#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2282,c_1745])).

tff(c_2320,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_2293])).

tff(c_2322,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1163,c_2320])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:47:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.08/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.12/1.75  
% 4.12/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.12/1.75  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.12/1.75  
% 4.12/1.75  %Foreground sorts:
% 4.12/1.75  
% 4.12/1.75  
% 4.12/1.75  %Background operators:
% 4.12/1.75  
% 4.12/1.75  
% 4.12/1.75  %Foreground operators:
% 4.12/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.12/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.12/1.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.12/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.12/1.75  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.12/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.12/1.75  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.12/1.75  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.12/1.75  tff('#skF_3', type, '#skF_3': $i).
% 4.12/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.12/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.12/1.75  tff('#skF_4', type, '#skF_4': $i).
% 4.12/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.12/1.75  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.12/1.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.12/1.75  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.12/1.75  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.12/1.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.12/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.12/1.75  
% 4.12/1.78  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.12/1.78  tff(f_71, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.12/1.78  tff(f_85, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 4.12/1.78  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.12/1.78  tff(f_49, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.12/1.78  tff(f_78, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.12/1.78  tff(f_69, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 4.12/1.78  tff(f_56, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.12/1.78  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.12/1.78  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.12/1.78  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 4.12/1.78  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.12/1.78  tff(f_45, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.12/1.78  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.12/1.78  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.12/1.78  tff(f_47, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.12/1.78  tff(c_14, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.12/1.78  tff(c_44, plain, (![A_26]: (k2_subset_1(A_26)=A_26)), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.12/1.78  tff(c_52, plain, (k2_subset_1('#skF_3')!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.12/1.78  tff(c_60, plain, ('#skF_3'!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_52])).
% 4.12/1.78  tff(c_179, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_60])).
% 4.12/1.78  tff(c_58, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | k2_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.12/1.78  tff(c_59, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_58])).
% 4.12/1.78  tff(c_231, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_179, c_59])).
% 4.12/1.78  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.12/1.78  tff(c_233, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_50])).
% 4.12/1.78  tff(c_722, plain, (![A_81, B_82]: (k4_xboole_0(A_81, B_82)=k3_subset_1(A_81, B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.12/1.78  tff(c_735, plain, (k4_xboole_0('#skF_4', '#skF_4')=k3_subset_1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_233, c_722])).
% 4.12/1.78  tff(c_22, plain, (![A_18]: (k5_xboole_0(A_18, A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.12/1.78  tff(c_48, plain, (![A_29]: (~v1_xboole_0(k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.12/1.78  tff(c_443, plain, (![B_69, A_70]: (r2_hidden(B_69, A_70) | ~m1_subset_1(B_69, A_70) | v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.12/1.78  tff(c_24, plain, (![C_23, A_19]: (r1_tarski(C_23, A_19) | ~r2_hidden(C_23, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.12/1.78  tff(c_450, plain, (![B_69, A_19]: (r1_tarski(B_69, A_19) | ~m1_subset_1(B_69, k1_zfmisc_1(A_19)) | v1_xboole_0(k1_zfmisc_1(A_19)))), inference(resolution, [status(thm)], [c_443, c_24])).
% 4.12/1.78  tff(c_1107, plain, (![B_95, A_96]: (r1_tarski(B_95, A_96) | ~m1_subset_1(B_95, k1_zfmisc_1(A_96)))), inference(negUnitSimplification, [status(thm)], [c_48, c_450])).
% 4.12/1.78  tff(c_1120, plain, (r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_233, c_1107])).
% 4.12/1.78  tff(c_12, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.12/1.78  tff(c_1124, plain, (k3_xboole_0('#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_1120, c_12])).
% 4.12/1.78  tff(c_10, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.12/1.78  tff(c_1143, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1124, c_10])).
% 4.12/1.78  tff(c_1146, plain, (k3_subset_1('#skF_4', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_735, c_22, c_1143])).
% 4.12/1.78  tff(c_232, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_231, c_179])).
% 4.12/1.78  tff(c_1154, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1146, c_232])).
% 4.12/1.78  tff(c_1162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_1154])).
% 4.12/1.78  tff(c_1163, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_60])).
% 4.12/1.78  tff(c_132, plain, (![B_39, A_40]: (k5_xboole_0(B_39, A_40)=k5_xboole_0(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.12/1.78  tff(c_16, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.12/1.78  tff(c_148, plain, (![A_40]: (k5_xboole_0(k1_xboole_0, A_40)=A_40)), inference(superposition, [status(thm), theory('equality')], [c_132, c_16])).
% 4.12/1.78  tff(c_1887, plain, (![A_143, B_144]: (k4_xboole_0(A_143, B_144)=k3_subset_1(A_143, B_144) | ~m1_subset_1(B_144, k1_zfmisc_1(A_143)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.12/1.78  tff(c_1900, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_1887])).
% 4.12/1.78  tff(c_18, plain, (![A_13, B_14]: (r1_xboole_0(k4_xboole_0(A_13, B_14), B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.12/1.78  tff(c_1311, plain, (![A_112, B_113]: (k3_xboole_0(A_112, B_113)=k1_xboole_0 | ~r1_xboole_0(A_112, B_113))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.12/1.78  tff(c_1319, plain, (![A_13, B_14]: (k3_xboole_0(k4_xboole_0(A_13, B_14), B_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_1311])).
% 4.12/1.78  tff(c_1907, plain, (k3_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1900, c_1319])).
% 4.12/1.78  tff(c_1165, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1163, c_59])).
% 4.12/1.78  tff(c_1224, plain, (![A_106, B_107]: (k3_xboole_0(A_106, B_107)=A_106 | ~r1_tarski(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.12/1.78  tff(c_1231, plain, (k3_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_1165, c_1224])).
% 4.12/1.78  tff(c_1918, plain, (k3_subset_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1907, c_1231])).
% 4.12/1.78  tff(c_1951, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1918, c_1900])).
% 4.12/1.78  tff(c_1383, plain, (![B_122, A_123]: (r2_hidden(B_122, A_123) | ~m1_subset_1(B_122, A_123) | v1_xboole_0(A_123))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.12/1.78  tff(c_1390, plain, (![B_122, A_19]: (r1_tarski(B_122, A_19) | ~m1_subset_1(B_122, k1_zfmisc_1(A_19)) | v1_xboole_0(k1_zfmisc_1(A_19)))), inference(resolution, [status(thm)], [c_1383, c_24])).
% 4.12/1.78  tff(c_1400, plain, (![B_126, A_127]: (r1_tarski(B_126, A_127) | ~m1_subset_1(B_126, k1_zfmisc_1(A_127)))), inference(negUnitSimplification, [status(thm)], [c_48, c_1390])).
% 4.12/1.78  tff(c_1413, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_1400])).
% 4.12/1.78  tff(c_1417, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_1413, c_12])).
% 4.12/1.78  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.12/1.78  tff(c_1422, plain, (![A_128, B_129]: (k5_xboole_0(A_128, k3_xboole_0(A_128, B_129))=k4_xboole_0(A_128, B_129))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.12/1.78  tff(c_2210, plain, (![A_155, B_156]: (k5_xboole_0(A_155, k3_xboole_0(B_156, A_155))=k4_xboole_0(A_155, B_156))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1422])).
% 4.12/1.78  tff(c_2254, plain, (k5_xboole_0('#skF_3', '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1417, c_2210])).
% 4.12/1.78  tff(c_2282, plain, (k5_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1951, c_2254])).
% 4.12/1.78  tff(c_1500, plain, (![A_132, B_133, C_134]: (k5_xboole_0(k5_xboole_0(A_132, B_133), C_134)=k5_xboole_0(A_132, k5_xboole_0(B_133, C_134)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.12/1.78  tff(c_1564, plain, (![A_18, C_134]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_134))=k5_xboole_0(k1_xboole_0, C_134))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1500])).
% 4.12/1.78  tff(c_1577, plain, (![A_18, C_134]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_134))=C_134)), inference(demodulation, [status(thm), theory('equality')], [c_148, c_1564])).
% 4.12/1.78  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.12/1.78  tff(c_1631, plain, (![A_137, C_138]: (k5_xboole_0(A_137, k5_xboole_0(A_137, C_138))=C_138)), inference(demodulation, [status(thm), theory('equality')], [c_148, c_1564])).
% 4.12/1.78  tff(c_1712, plain, (![A_139, B_140]: (k5_xboole_0(A_139, k5_xboole_0(B_140, A_139))=B_140)), inference(superposition, [status(thm), theory('equality')], [c_4, c_1631])).
% 4.12/1.78  tff(c_1745, plain, (![A_18, C_134]: (k5_xboole_0(k5_xboole_0(A_18, C_134), C_134)=A_18)), inference(superposition, [status(thm), theory('equality')], [c_1577, c_1712])).
% 4.12/1.78  tff(c_2293, plain, (k5_xboole_0(k1_xboole_0, '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2282, c_1745])).
% 4.12/1.78  tff(c_2320, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_148, c_2293])).
% 4.12/1.78  tff(c_2322, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1163, c_2320])).
% 4.12/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.12/1.78  
% 4.12/1.78  Inference rules
% 4.12/1.78  ----------------------
% 4.12/1.78  #Ref     : 0
% 4.12/1.78  #Sup     : 551
% 4.12/1.78  #Fact    : 0
% 4.12/1.78  #Define  : 0
% 4.12/1.78  #Split   : 1
% 4.12/1.78  #Chain   : 0
% 4.12/1.78  #Close   : 0
% 4.12/1.78  
% 4.12/1.78  Ordering : KBO
% 4.12/1.78  
% 4.12/1.78  Simplification rules
% 4.12/1.78  ----------------------
% 4.12/1.78  #Subsume      : 16
% 4.12/1.78  #Demod        : 308
% 4.12/1.78  #Tautology    : 403
% 4.12/1.78  #SimpNegUnit  : 7
% 4.12/1.78  #BackRed      : 17
% 4.12/1.78  
% 4.12/1.78  #Partial instantiations: 0
% 4.12/1.78  #Strategies tried      : 1
% 4.12/1.78  
% 4.12/1.78  Timing (in seconds)
% 4.12/1.78  ----------------------
% 4.12/1.78  Preprocessing        : 0.42
% 4.12/1.78  Parsing              : 0.23
% 4.12/1.78  CNF conversion       : 0.03
% 4.12/1.78  Main loop            : 0.57
% 4.12/1.78  Inferencing          : 0.20
% 4.12/1.78  Reduction            : 0.22
% 4.12/1.78  Demodulation         : 0.18
% 4.12/1.78  BG Simplification    : 0.03
% 4.12/1.78  Subsumption          : 0.08
% 4.12/1.78  Abstraction          : 0.03
% 4.12/1.78  MUC search           : 0.00
% 4.12/1.78  Cooper               : 0.00
% 4.12/1.78  Total                : 1.04
% 4.12/1.78  Index Insertion      : 0.00
% 4.12/1.78  Index Deletion       : 0.00
% 4.12/1.78  Index Matching       : 0.00
% 4.12/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
