%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:12 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 150 expanded)
%              Number of leaves         :   31 (  61 expanded)
%              Depth                    :   11
%              Number of atoms          :  107 ( 230 expanded)
%              Number of equality atoms :   46 (  98 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_75,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_51,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_82,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1455,plain,(
    ! [A_145,B_146] :
      ( k4_xboole_0(A_145,B_146) = k3_subset_1(A_145,B_146)
      | ~ m1_subset_1(B_146,k1_zfmisc_1(A_145)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1468,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_1455])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_46,plain,(
    ! [A_23] : k2_subset_1(A_23) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_60,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | k2_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_61,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_60])).

tff(c_123,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_61])).

tff(c_22,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_149,plain,(
    ! [A_40,B_41] :
      ( k4_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_156,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_149])).

tff(c_257,plain,(
    ! [A_53,B_54,C_55] :
      ( r1_tarski(A_53,B_54)
      | ~ r1_tarski(A_53,k4_xboole_0(B_54,C_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_311,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(A_58,B_59)
      | ~ r1_tarski(A_58,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_257])).

tff(c_317,plain,(
    ! [A_5,B_59] :
      ( r1_tarski(A_5,B_59)
      | k4_xboole_0(A_5,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_311])).

tff(c_334,plain,(
    ! [A_60,B_61] :
      ( r1_tarski(A_60,B_61)
      | k1_xboole_0 != A_60 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_317])).

tff(c_54,plain,
    ( k2_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_62,plain,
    ( '#skF_3' != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_54])).

tff(c_124,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_134,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_124])).

tff(c_361,plain,(
    k3_subset_1('#skF_4','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_334,c_134])).

tff(c_125,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_52])).

tff(c_797,plain,(
    ! [A_92,B_93] :
      ( k4_xboole_0(A_92,B_93) = k3_subset_1(A_92,B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(A_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_807,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k3_subset_1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_125,c_797])).

tff(c_811,plain,(
    k3_subset_1('#skF_4','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_807])).

tff(c_813,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_361,c_811])).

tff(c_814,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_822,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_814])).

tff(c_824,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_50,plain,(
    ! [A_26] : ~ v1_xboole_0(k1_zfmisc_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_948,plain,(
    ! [B_109,A_110] :
      ( r2_hidden(B_109,A_110)
      | ~ m1_subset_1(B_109,A_110)
      | v1_xboole_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_26,plain,(
    ! [C_20,A_16] :
      ( r1_tarski(C_20,A_16)
      | ~ r2_hidden(C_20,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_952,plain,(
    ! [B_109,A_16] :
      ( r1_tarski(B_109,A_16)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(A_16))
      | v1_xboole_0(k1_zfmisc_1(A_16)) ) ),
    inference(resolution,[status(thm)],[c_948,c_26])).

tff(c_956,plain,(
    ! [B_111,A_112] :
      ( r1_tarski(B_111,A_112)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(A_112)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_952])).

tff(c_965,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_956])).

tff(c_1160,plain,(
    ! [B_131,A_132] :
      ( B_131 = A_132
      | ~ r1_tarski(B_131,A_132)
      | ~ r1_tarski(A_132,B_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1162,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_965,c_1160])).

tff(c_1173,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_824,c_1162])).

tff(c_1184,plain,(
    k4_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_1173])).

tff(c_1469,plain,(
    k3_subset_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1468,c_1184])).

tff(c_823,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_969,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_965,c_12])).

tff(c_1053,plain,(
    ! [A_127,B_128] : k4_xboole_0(A_127,k4_xboole_0(A_127,B_128)) = k3_xboole_0(A_127,B_128) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1081,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_969,c_1053])).

tff(c_1100,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1081])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1479,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1468,c_24])).

tff(c_1491,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1100,c_2,c_1479])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( k1_xboole_0 = A_11
      | ~ r1_tarski(A_11,k4_xboole_0(B_12,A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1784,plain,
    ( k3_subset_1('#skF_3','#skF_4') = k1_xboole_0
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1491,c_20])).

tff(c_1791,plain,(
    k3_subset_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_823,c_1784])).

tff(c_1793,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1469,c_1791])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:12:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.48  
% 3.02/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.48  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.02/1.48  
% 3.02/1.48  %Foreground sorts:
% 3.02/1.48  
% 3.02/1.48  
% 3.02/1.48  %Background operators:
% 3.02/1.48  
% 3.02/1.48  
% 3.02/1.48  %Foreground operators:
% 3.02/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.02/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.02/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.02/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.02/1.48  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.02/1.48  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.02/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.02/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.02/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.02/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.02/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.02/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.02/1.48  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.02/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.02/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.02/1.48  
% 3.16/1.50  tff(f_89, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 3.16/1.50  tff(f_79, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.16/1.50  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.16/1.50  tff(f_75, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.16/1.50  tff(f_51, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.16/1.50  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.16/1.50  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.16/1.50  tff(f_82, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.16/1.50  tff(f_73, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.16/1.50  tff(f_60, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.16/1.50  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.16/1.50  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.16/1.50  tff(f_49, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 3.16/1.50  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.16/1.50  tff(c_1455, plain, (![A_145, B_146]: (k4_xboole_0(A_145, B_146)=k3_subset_1(A_145, B_146) | ~m1_subset_1(B_146, k1_zfmisc_1(A_145)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.16/1.50  tff(c_1468, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_1455])).
% 3.16/1.50  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.16/1.50  tff(c_46, plain, (![A_23]: (k2_subset_1(A_23)=A_23)), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.16/1.50  tff(c_60, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | k2_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.16/1.50  tff(c_61, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_60])).
% 3.16/1.50  tff(c_123, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_61])).
% 3.16/1.50  tff(c_22, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.16/1.50  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.16/1.50  tff(c_149, plain, (![A_40, B_41]: (k4_xboole_0(A_40, B_41)=k1_xboole_0 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.16/1.50  tff(c_156, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_149])).
% 3.16/1.50  tff(c_257, plain, (![A_53, B_54, C_55]: (r1_tarski(A_53, B_54) | ~r1_tarski(A_53, k4_xboole_0(B_54, C_55)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.16/1.50  tff(c_311, plain, (![A_58, B_59]: (r1_tarski(A_58, B_59) | ~r1_tarski(A_58, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_156, c_257])).
% 3.16/1.50  tff(c_317, plain, (![A_5, B_59]: (r1_tarski(A_5, B_59) | k4_xboole_0(A_5, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_311])).
% 3.16/1.50  tff(c_334, plain, (![A_60, B_61]: (r1_tarski(A_60, B_61) | k1_xboole_0!=A_60)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_317])).
% 3.16/1.50  tff(c_54, plain, (k2_subset_1('#skF_3')!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.16/1.50  tff(c_62, plain, ('#skF_3'!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_54])).
% 3.16/1.50  tff(c_124, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_62])).
% 3.16/1.50  tff(c_134, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_123, c_124])).
% 3.16/1.50  tff(c_361, plain, (k3_subset_1('#skF_4', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_334, c_134])).
% 3.16/1.50  tff(c_125, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_52])).
% 3.16/1.50  tff(c_797, plain, (![A_92, B_93]: (k4_xboole_0(A_92, B_93)=k3_subset_1(A_92, B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(A_92)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.16/1.50  tff(c_807, plain, (k4_xboole_0('#skF_4', '#skF_4')=k3_subset_1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_125, c_797])).
% 3.16/1.50  tff(c_811, plain, (k3_subset_1('#skF_4', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_156, c_807])).
% 3.16/1.50  tff(c_813, plain, $false, inference(negUnitSimplification, [status(thm)], [c_361, c_811])).
% 3.16/1.50  tff(c_814, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_62])).
% 3.16/1.50  tff(c_822, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_123, c_814])).
% 3.16/1.50  tff(c_824, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_61])).
% 3.16/1.50  tff(c_50, plain, (![A_26]: (~v1_xboole_0(k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.16/1.50  tff(c_948, plain, (![B_109, A_110]: (r2_hidden(B_109, A_110) | ~m1_subset_1(B_109, A_110) | v1_xboole_0(A_110))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.16/1.50  tff(c_26, plain, (![C_20, A_16]: (r1_tarski(C_20, A_16) | ~r2_hidden(C_20, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.16/1.50  tff(c_952, plain, (![B_109, A_16]: (r1_tarski(B_109, A_16) | ~m1_subset_1(B_109, k1_zfmisc_1(A_16)) | v1_xboole_0(k1_zfmisc_1(A_16)))), inference(resolution, [status(thm)], [c_948, c_26])).
% 3.16/1.50  tff(c_956, plain, (![B_111, A_112]: (r1_tarski(B_111, A_112) | ~m1_subset_1(B_111, k1_zfmisc_1(A_112)))), inference(negUnitSimplification, [status(thm)], [c_50, c_952])).
% 3.16/1.50  tff(c_965, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_956])).
% 3.16/1.50  tff(c_1160, plain, (![B_131, A_132]: (B_131=A_132 | ~r1_tarski(B_131, A_132) | ~r1_tarski(A_132, B_131))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.16/1.50  tff(c_1162, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_965, c_1160])).
% 3.16/1.50  tff(c_1173, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_824, c_1162])).
% 3.16/1.50  tff(c_1184, plain, (k4_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_1173])).
% 3.16/1.50  tff(c_1469, plain, (k3_subset_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1468, c_1184])).
% 3.16/1.50  tff(c_823, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_61])).
% 3.16/1.50  tff(c_12, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.16/1.50  tff(c_969, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_965, c_12])).
% 3.16/1.50  tff(c_1053, plain, (![A_127, B_128]: (k4_xboole_0(A_127, k4_xboole_0(A_127, B_128))=k3_xboole_0(A_127, B_128))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.16/1.50  tff(c_1081, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_969, c_1053])).
% 3.16/1.50  tff(c_1100, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1081])).
% 3.16/1.50  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.16/1.50  tff(c_24, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.16/1.50  tff(c_1479, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1468, c_24])).
% 3.16/1.50  tff(c_1491, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1100, c_2, c_1479])).
% 3.16/1.50  tff(c_20, plain, (![A_11, B_12]: (k1_xboole_0=A_11 | ~r1_tarski(A_11, k4_xboole_0(B_12, A_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.16/1.50  tff(c_1784, plain, (k3_subset_1('#skF_3', '#skF_4')=k1_xboole_0 | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1491, c_20])).
% 3.16/1.50  tff(c_1791, plain, (k3_subset_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_823, c_1784])).
% 3.16/1.50  tff(c_1793, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1469, c_1791])).
% 3.16/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.50  
% 3.16/1.50  Inference rules
% 3.16/1.50  ----------------------
% 3.16/1.50  #Ref     : 1
% 3.16/1.50  #Sup     : 403
% 3.16/1.50  #Fact    : 0
% 3.16/1.50  #Define  : 0
% 3.16/1.50  #Split   : 3
% 3.16/1.50  #Chain   : 0
% 3.16/1.50  #Close   : 0
% 3.16/1.50  
% 3.16/1.50  Ordering : KBO
% 3.16/1.50  
% 3.16/1.50  Simplification rules
% 3.16/1.50  ----------------------
% 3.16/1.50  #Subsume      : 39
% 3.16/1.50  #Demod        : 163
% 3.16/1.50  #Tautology    : 236
% 3.16/1.50  #SimpNegUnit  : 8
% 3.16/1.50  #BackRed      : 3
% 3.16/1.50  
% 3.16/1.50  #Partial instantiations: 0
% 3.16/1.50  #Strategies tried      : 1
% 3.16/1.50  
% 3.16/1.50  Timing (in seconds)
% 3.16/1.50  ----------------------
% 3.16/1.50  Preprocessing        : 0.31
% 3.16/1.50  Parsing              : 0.16
% 3.16/1.50  CNF conversion       : 0.02
% 3.16/1.50  Main loop            : 0.43
% 3.16/1.50  Inferencing          : 0.15
% 3.16/1.50  Reduction            : 0.14
% 3.16/1.50  Demodulation         : 0.11
% 3.16/1.50  BG Simplification    : 0.02
% 3.16/1.50  Subsumption          : 0.07
% 3.16/1.50  Abstraction          : 0.02
% 3.16/1.50  MUC search           : 0.00
% 3.16/1.50  Cooper               : 0.00
% 3.16/1.50  Total                : 0.77
% 3.16/1.50  Index Insertion      : 0.00
% 3.16/1.50  Index Deletion       : 0.00
% 3.16/1.50  Index Matching       : 0.00
% 3.16/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
