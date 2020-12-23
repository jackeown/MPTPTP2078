%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:01 EST 2020

% Result     : Theorem 3.45s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 137 expanded)
%              Number of leaves         :   31 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :  103 ( 229 expanded)
%              Number of equality atoms :   34 (  68 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_73,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_95,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_84,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_42,plain,(
    ! [A_22] : k1_subset_1(A_22) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_60,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_61,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_60])).

tff(c_116,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_61])).

tff(c_16,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_119,plain,(
    ! [A_10] : r1_tarski('#skF_4',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_16])).

tff(c_54,plain,
    ( k1_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_62,plain,
    ( k1_xboole_0 != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_54])).

tff(c_125,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_62])).

tff(c_135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_125])).

tff(c_137,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_11] : k4_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_48,plain,(
    ! [A_27] : ~ v1_xboole_0(k1_zfmisc_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_24,plain,(
    ! [C_19,A_15] :
      ( r2_hidden(C_19,k1_zfmisc_1(A_15))
      | ~ r1_tarski(C_19,A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_177,plain,(
    ! [B_53,A_54] :
      ( m1_subset_1(B_53,A_54)
      | ~ r2_hidden(B_53,A_54)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_180,plain,(
    ! [C_19,A_15] :
      ( m1_subset_1(C_19,k1_zfmisc_1(A_15))
      | v1_xboole_0(k1_zfmisc_1(A_15))
      | ~ r1_tarski(C_19,A_15) ) ),
    inference(resolution,[status(thm)],[c_24,c_177])).

tff(c_183,plain,(
    ! [C_19,A_15] :
      ( m1_subset_1(C_19,k1_zfmisc_1(A_15))
      | ~ r1_tarski(C_19,A_15) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_180])).

tff(c_330,plain,(
    ! [A_72,B_73] :
      ( k4_xboole_0(A_72,B_73) = k3_subset_1(A_72,B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_552,plain,(
    ! [A_92,C_93] :
      ( k4_xboole_0(A_92,C_93) = k3_subset_1(A_92,C_93)
      | ~ r1_tarski(C_93,A_92) ) ),
    inference(resolution,[status(thm)],[c_183,c_330])).

tff(c_576,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = k3_subset_1(A_10,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_552])).

tff(c_587,plain,(
    ! [A_10] : k3_subset_1(A_10,k1_xboole_0) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_576])).

tff(c_400,plain,(
    ! [A_79,B_80] :
      ( k3_subset_1(A_79,k3_subset_1(A_79,B_80)) = B_80
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1266,plain,(
    ! [A_130,C_131] :
      ( k3_subset_1(A_130,k3_subset_1(A_130,C_131)) = C_131
      | ~ r1_tarski(C_131,A_130) ) ),
    inference(resolution,[status(thm)],[c_183,c_400])).

tff(c_1300,plain,(
    ! [A_10] :
      ( k3_subset_1(A_10,A_10) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_587,c_1266])).

tff(c_1324,plain,(
    ! [A_10] : k3_subset_1(A_10,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1300])).

tff(c_585,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k3_subset_1(B_4,B_4) ),
    inference(resolution,[status(thm)],[c_8,c_552])).

tff(c_1340,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1324,c_585])).

tff(c_136,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_343,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_330])).

tff(c_12,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_xboole_0(A_7,C_9)
      | ~ r1_tarski(A_7,k4_xboole_0(B_8,C_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_475,plain,(
    ! [A_88] :
      ( r1_xboole_0(A_88,'#skF_4')
      | ~ r1_tarski(A_88,k3_subset_1('#skF_3','#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_12])).

tff(c_498,plain,(
    r1_xboole_0('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_136,c_475])).

tff(c_20,plain,(
    ! [A_12,B_13,C_14] :
      ( r1_tarski(A_12,k4_xboole_0(B_13,C_14))
      | ~ r1_xboole_0(A_12,C_14)
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_261,plain,(
    ! [A_66,B_67,C_68] :
      ( r1_tarski(A_66,B_67)
      | ~ r1_tarski(A_66,k4_xboole_0(B_67,C_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_276,plain,(
    ! [B_69,C_70] : r1_tarski(k4_xboole_0(B_69,C_70),B_69) ),
    inference(resolution,[status(thm)],[c_8,c_261])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1537,plain,(
    ! [B_139,C_140] :
      ( k4_xboole_0(B_139,C_140) = B_139
      | ~ r1_tarski(B_139,k4_xboole_0(B_139,C_140)) ) ),
    inference(resolution,[status(thm)],[c_276,c_4])).

tff(c_1544,plain,(
    ! [B_13,C_14] :
      ( k4_xboole_0(B_13,C_14) = B_13
      | ~ r1_xboole_0(B_13,C_14)
      | ~ r1_tarski(B_13,B_13) ) ),
    inference(resolution,[status(thm)],[c_20,c_1537])).

tff(c_1573,plain,(
    ! [B_141,C_142] :
      ( k4_xboole_0(B_141,C_142) = B_141
      | ~ r1_xboole_0(B_141,C_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1544])).

tff(c_1614,plain,(
    k4_xboole_0('#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_498,c_1573])).

tff(c_296,plain,(
    ! [B_69,C_70] :
      ( k4_xboole_0(B_69,C_70) = B_69
      | ~ r1_tarski(B_69,k4_xboole_0(B_69,C_70)) ) ),
    inference(resolution,[status(thm)],[c_276,c_4])).

tff(c_1673,plain,
    ( k4_xboole_0('#skF_4','#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1614,c_296])).

tff(c_1706,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1340,c_1673])).

tff(c_1708,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_1706])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:24:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.45/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.58  
% 3.45/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.58  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.45/1.58  
% 3.45/1.58  %Foreground sorts:
% 3.45/1.58  
% 3.45/1.58  
% 3.45/1.58  %Background operators:
% 3.45/1.58  
% 3.45/1.58  
% 3.45/1.58  %Foreground operators:
% 3.45/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.45/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.45/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.45/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.45/1.58  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.45/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.45/1.58  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.45/1.58  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.45/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.45/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.45/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.45/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.45/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.45/1.58  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.45/1.58  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.45/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.45/1.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.45/1.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.45/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.45/1.58  
% 3.45/1.59  tff(f_73, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 3.45/1.59  tff(f_95, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 3.45/1.59  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.45/1.59  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.45/1.59  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.45/1.59  tff(f_84, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.45/1.59  tff(f_58, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.45/1.59  tff(f_71, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.45/1.59  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.45/1.59  tff(f_88, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.45/1.59  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.45/1.59  tff(f_51, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 3.45/1.59  tff(c_42, plain, (![A_22]: (k1_subset_1(A_22)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.45/1.59  tff(c_60, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.45/1.59  tff(c_61, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_60])).
% 3.45/1.59  tff(c_116, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_61])).
% 3.45/1.59  tff(c_16, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.45/1.59  tff(c_119, plain, (![A_10]: (r1_tarski('#skF_4', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_16])).
% 3.45/1.59  tff(c_54, plain, (k1_subset_1('#skF_3')!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.45/1.59  tff(c_62, plain, (k1_xboole_0!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_54])).
% 3.45/1.59  tff(c_125, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_62])).
% 3.45/1.59  tff(c_135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_119, c_125])).
% 3.45/1.59  tff(c_137, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_61])).
% 3.45/1.59  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.45/1.59  tff(c_18, plain, (![A_11]: (k4_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.45/1.59  tff(c_48, plain, (![A_27]: (~v1_xboole_0(k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.45/1.59  tff(c_24, plain, (![C_19, A_15]: (r2_hidden(C_19, k1_zfmisc_1(A_15)) | ~r1_tarski(C_19, A_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.45/1.59  tff(c_177, plain, (![B_53, A_54]: (m1_subset_1(B_53, A_54) | ~r2_hidden(B_53, A_54) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.45/1.59  tff(c_180, plain, (![C_19, A_15]: (m1_subset_1(C_19, k1_zfmisc_1(A_15)) | v1_xboole_0(k1_zfmisc_1(A_15)) | ~r1_tarski(C_19, A_15))), inference(resolution, [status(thm)], [c_24, c_177])).
% 3.45/1.59  tff(c_183, plain, (![C_19, A_15]: (m1_subset_1(C_19, k1_zfmisc_1(A_15)) | ~r1_tarski(C_19, A_15))), inference(negUnitSimplification, [status(thm)], [c_48, c_180])).
% 3.45/1.59  tff(c_330, plain, (![A_72, B_73]: (k4_xboole_0(A_72, B_73)=k3_subset_1(A_72, B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.45/1.59  tff(c_552, plain, (![A_92, C_93]: (k4_xboole_0(A_92, C_93)=k3_subset_1(A_92, C_93) | ~r1_tarski(C_93, A_92))), inference(resolution, [status(thm)], [c_183, c_330])).
% 3.45/1.59  tff(c_576, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=k3_subset_1(A_10, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_552])).
% 3.45/1.59  tff(c_587, plain, (![A_10]: (k3_subset_1(A_10, k1_xboole_0)=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_576])).
% 3.45/1.59  tff(c_400, plain, (![A_79, B_80]: (k3_subset_1(A_79, k3_subset_1(A_79, B_80))=B_80 | ~m1_subset_1(B_80, k1_zfmisc_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.45/1.59  tff(c_1266, plain, (![A_130, C_131]: (k3_subset_1(A_130, k3_subset_1(A_130, C_131))=C_131 | ~r1_tarski(C_131, A_130))), inference(resolution, [status(thm)], [c_183, c_400])).
% 3.45/1.59  tff(c_1300, plain, (![A_10]: (k3_subset_1(A_10, A_10)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_10))), inference(superposition, [status(thm), theory('equality')], [c_587, c_1266])).
% 3.45/1.59  tff(c_1324, plain, (![A_10]: (k3_subset_1(A_10, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1300])).
% 3.45/1.59  tff(c_585, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k3_subset_1(B_4, B_4))), inference(resolution, [status(thm)], [c_8, c_552])).
% 3.45/1.59  tff(c_1340, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1324, c_585])).
% 3.45/1.59  tff(c_136, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_61])).
% 3.45/1.59  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.45/1.59  tff(c_343, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_330])).
% 3.45/1.59  tff(c_12, plain, (![A_7, C_9, B_8]: (r1_xboole_0(A_7, C_9) | ~r1_tarski(A_7, k4_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.45/1.59  tff(c_475, plain, (![A_88]: (r1_xboole_0(A_88, '#skF_4') | ~r1_tarski(A_88, k3_subset_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_343, c_12])).
% 3.45/1.59  tff(c_498, plain, (r1_xboole_0('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_136, c_475])).
% 3.45/1.59  tff(c_20, plain, (![A_12, B_13, C_14]: (r1_tarski(A_12, k4_xboole_0(B_13, C_14)) | ~r1_xboole_0(A_12, C_14) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.45/1.59  tff(c_261, plain, (![A_66, B_67, C_68]: (r1_tarski(A_66, B_67) | ~r1_tarski(A_66, k4_xboole_0(B_67, C_68)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.45/1.59  tff(c_276, plain, (![B_69, C_70]: (r1_tarski(k4_xboole_0(B_69, C_70), B_69))), inference(resolution, [status(thm)], [c_8, c_261])).
% 3.45/1.59  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.45/1.59  tff(c_1537, plain, (![B_139, C_140]: (k4_xboole_0(B_139, C_140)=B_139 | ~r1_tarski(B_139, k4_xboole_0(B_139, C_140)))), inference(resolution, [status(thm)], [c_276, c_4])).
% 3.45/1.59  tff(c_1544, plain, (![B_13, C_14]: (k4_xboole_0(B_13, C_14)=B_13 | ~r1_xboole_0(B_13, C_14) | ~r1_tarski(B_13, B_13))), inference(resolution, [status(thm)], [c_20, c_1537])).
% 3.45/1.59  tff(c_1573, plain, (![B_141, C_142]: (k4_xboole_0(B_141, C_142)=B_141 | ~r1_xboole_0(B_141, C_142))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1544])).
% 3.45/1.59  tff(c_1614, plain, (k4_xboole_0('#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_498, c_1573])).
% 3.45/1.59  tff(c_296, plain, (![B_69, C_70]: (k4_xboole_0(B_69, C_70)=B_69 | ~r1_tarski(B_69, k4_xboole_0(B_69, C_70)))), inference(resolution, [status(thm)], [c_276, c_4])).
% 3.45/1.59  tff(c_1673, plain, (k4_xboole_0('#skF_4', '#skF_4')='#skF_4' | ~r1_tarski('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1614, c_296])).
% 3.45/1.59  tff(c_1706, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1340, c_1673])).
% 3.45/1.59  tff(c_1708, plain, $false, inference(negUnitSimplification, [status(thm)], [c_137, c_1706])).
% 3.45/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.59  
% 3.45/1.59  Inference rules
% 3.45/1.59  ----------------------
% 3.45/1.59  #Ref     : 0
% 3.45/1.59  #Sup     : 365
% 3.45/1.59  #Fact    : 0
% 3.45/1.59  #Define  : 0
% 3.45/1.59  #Split   : 4
% 3.45/1.59  #Chain   : 0
% 3.45/1.59  #Close   : 0
% 3.45/1.59  
% 3.45/1.59  Ordering : KBO
% 3.45/1.59  
% 3.45/1.59  Simplification rules
% 3.45/1.59  ----------------------
% 3.45/1.59  #Subsume      : 22
% 3.45/1.59  #Demod        : 177
% 3.45/1.59  #Tautology    : 195
% 3.45/1.59  #SimpNegUnit  : 3
% 3.45/1.59  #BackRed      : 14
% 3.45/1.59  
% 3.45/1.59  #Partial instantiations: 0
% 3.45/1.59  #Strategies tried      : 1
% 3.45/1.59  
% 3.45/1.59  Timing (in seconds)
% 3.45/1.59  ----------------------
% 3.45/1.60  Preprocessing        : 0.31
% 3.45/1.60  Parsing              : 0.16
% 3.45/1.60  CNF conversion       : 0.02
% 3.45/1.60  Main loop            : 0.47
% 3.45/1.60  Inferencing          : 0.16
% 3.45/1.60  Reduction            : 0.16
% 3.45/1.60  Demodulation         : 0.12
% 3.45/1.60  BG Simplification    : 0.02
% 3.45/1.60  Subsumption          : 0.09
% 3.45/1.60  Abstraction          : 0.03
% 3.45/1.60  MUC search           : 0.00
% 3.45/1.60  Cooper               : 0.00
% 3.45/1.60  Total                : 0.82
% 3.45/1.60  Index Insertion      : 0.00
% 3.45/1.60  Index Deletion       : 0.00
% 3.45/1.60  Index Matching       : 0.00
% 3.45/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
