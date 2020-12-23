%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:03 EST 2020

% Result     : Theorem 3.30s
% Output     : CNFRefutation 3.45s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 186 expanded)
%              Number of leaves         :   36 (  76 expanded)
%              Depth                    :   12
%              Number of atoms          :  107 ( 289 expanded)
%              Number of equality atoms :   47 ( 121 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_4 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_95,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_88,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_92,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_66,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_54,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_78,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_76,plain,(
    ! [A_35] : ~ v1_xboole_0(k1_zfmisc_1(A_35)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_226,plain,(
    ! [B_65,A_66] :
      ( r2_hidden(B_65,A_66)
      | ~ m1_subset_1(B_65,A_66)
      | v1_xboole_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_52,plain,(
    ! [C_29,A_25] :
      ( r1_tarski(C_29,A_25)
      | ~ r2_hidden(C_29,k1_zfmisc_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_230,plain,(
    ! [B_65,A_25] :
      ( r1_tarski(B_65,A_25)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_25))
      | v1_xboole_0(k1_zfmisc_1(A_25)) ) ),
    inference(resolution,[status(thm)],[c_226,c_52])).

tff(c_234,plain,(
    ! [B_67,A_68] :
      ( r1_tarski(B_67,A_68)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_68)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_230])).

tff(c_243,plain,(
    r1_tarski('#skF_9','#skF_8') ),
    inference(resolution,[status(thm)],[c_78,c_234])).

tff(c_72,plain,(
    ! [A_32] : k1_subset_1(A_32) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_80,plain,
    ( k1_subset_1('#skF_8') != '#skF_9'
    | ~ r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_88,plain,
    ( k1_xboole_0 != '#skF_9'
    | ~ r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_80])).

tff(c_139,plain,(
    ~ r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_86,plain,
    ( r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9'))
    | k1_subset_1('#skF_8') = '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_87,plain,
    ( r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9'))
    | k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_86])).

tff(c_144,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_87])).

tff(c_44,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = k1_xboole_0
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_146,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = '#skF_9'
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_44])).

tff(c_264,plain,(
    k4_xboole_0('#skF_9','#skF_8') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_243,c_146])).

tff(c_48,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = A_21
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_265,plain,(
    k3_xboole_0('#skF_9','#skF_8') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_243,c_48])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_272,plain,(
    k3_xboole_0('#skF_8','#skF_9') = '#skF_9' ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_2])).

tff(c_496,plain,(
    ! [A_91,B_92] :
      ( k4_xboole_0(A_91,B_92) = k3_subset_1(A_91,B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_509,plain,(
    k4_xboole_0('#skF_8','#skF_9') = k3_subset_1('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_78,c_496])).

tff(c_50,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_520,plain,(
    k4_xboole_0('#skF_8',k3_subset_1('#skF_8','#skF_9')) = k3_xboole_0('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_509,c_50])).

tff(c_523,plain,(
    k4_xboole_0('#skF_8',k3_subset_1('#skF_8','#skF_9')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_520])).

tff(c_42,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | k4_xboole_0(A_17,B_18) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_197,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(A_59,B_60)
      | k4_xboole_0(A_59,B_60) != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_42])).

tff(c_604,plain,(
    ! [A_97,B_98] :
      ( k3_xboole_0(A_97,B_98) = A_97
      | k4_xboole_0(A_97,B_98) != '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_197,c_48])).

tff(c_620,plain,(
    k3_xboole_0('#skF_8',k3_subset_1('#skF_8','#skF_9')) = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_604])).

tff(c_534,plain,(
    k3_xboole_0('#skF_8',k3_subset_1('#skF_8','#skF_9')) = k4_xboole_0('#skF_8','#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_50])).

tff(c_537,plain,(
    k3_xboole_0('#skF_8',k3_subset_1('#skF_8','#skF_9')) = k3_subset_1('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_509,c_534])).

tff(c_723,plain,(
    k3_subset_1('#skF_8','#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_620,c_537])).

tff(c_143,plain,(
    k4_xboole_0('#skF_9',k3_subset_1('#skF_8','#skF_9')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_139])).

tff(c_145,plain,(
    k4_xboole_0('#skF_9',k3_subset_1('#skF_8','#skF_9')) != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_143])).

tff(c_732,plain,(
    k4_xboole_0('#skF_9','#skF_8') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_723,c_145])).

tff(c_736,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_732])).

tff(c_737,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_40,plain,(
    ! [A_15] :
      ( r2_hidden('#skF_5'(A_15),A_15)
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_738,plain,(
    r1_tarski('#skF_9',k3_subset_1('#skF_8','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_768,plain,(
    ! [A_108,B_109] :
      ( k3_xboole_0(A_108,B_109) = A_108
      | ~ r1_tarski(A_108,B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_775,plain,(
    k3_xboole_0('#skF_9',k3_subset_1('#skF_8','#skF_9')) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_738,c_768])).

tff(c_1014,plain,(
    ! [D_130,B_131,A_132] :
      ( r2_hidden(D_130,B_131)
      | ~ r2_hidden(D_130,k3_xboole_0(A_132,B_131)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1302,plain,(
    ! [D_152] :
      ( r2_hidden(D_152,k3_subset_1('#skF_8','#skF_9'))
      | ~ r2_hidden(D_152,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_775,c_1014])).

tff(c_1092,plain,(
    ! [A_138,B_139] :
      ( k4_xboole_0(A_138,B_139) = k3_subset_1(A_138,B_139)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(A_138)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1105,plain,(
    k4_xboole_0('#skF_8','#skF_9') = k3_subset_1('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_78,c_1092])).

tff(c_24,plain,(
    ! [D_14,B_10,A_9] :
      ( ~ r2_hidden(D_14,B_10)
      | ~ r2_hidden(D_14,k4_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1110,plain,(
    ! [D_14] :
      ( ~ r2_hidden(D_14,'#skF_9')
      | ~ r2_hidden(D_14,k3_subset_1('#skF_8','#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1105,c_24])).

tff(c_1320,plain,(
    ! [D_153] : ~ r2_hidden(D_153,'#skF_9') ),
    inference(resolution,[status(thm)],[c_1302,c_1110])).

tff(c_1328,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_40,c_1320])).

tff(c_1333,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_737,c_1328])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:23:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.30/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.51  
% 3.30/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.52  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_1 > #skF_4 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_7
% 3.30/1.52  
% 3.30/1.52  %Foreground sorts:
% 3.30/1.52  
% 3.30/1.52  
% 3.30/1.52  %Background operators:
% 3.30/1.52  
% 3.30/1.52  
% 3.30/1.52  %Foreground operators:
% 3.30/1.52  tff('#skF_5', type, '#skF_5': $i > $i).
% 3.30/1.52  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.30/1.52  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.30/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.30/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.30/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.30/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.30/1.52  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.30/1.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.30/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.30/1.52  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.30/1.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.30/1.52  tff('#skF_9', type, '#skF_9': $i).
% 3.30/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.30/1.52  tff('#skF_8', type, '#skF_8': $i).
% 3.30/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.30/1.52  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.30/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.30/1.52  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.30/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.30/1.52  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.30/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.30/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.30/1.52  
% 3.45/1.53  tff(f_102, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 3.45/1.53  tff(f_95, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.45/1.53  tff(f_86, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.45/1.53  tff(f_73, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.45/1.53  tff(f_88, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 3.45/1.53  tff(f_58, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.45/1.53  tff(f_64, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.45/1.53  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.45/1.53  tff(f_92, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.45/1.53  tff(f_66, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.45/1.53  tff(f_54, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.45/1.53  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 3.45/1.53  tff(f_46, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.45/1.53  tff(c_78, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.45/1.53  tff(c_76, plain, (![A_35]: (~v1_xboole_0(k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.45/1.53  tff(c_226, plain, (![B_65, A_66]: (r2_hidden(B_65, A_66) | ~m1_subset_1(B_65, A_66) | v1_xboole_0(A_66))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.45/1.53  tff(c_52, plain, (![C_29, A_25]: (r1_tarski(C_29, A_25) | ~r2_hidden(C_29, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.45/1.53  tff(c_230, plain, (![B_65, A_25]: (r1_tarski(B_65, A_25) | ~m1_subset_1(B_65, k1_zfmisc_1(A_25)) | v1_xboole_0(k1_zfmisc_1(A_25)))), inference(resolution, [status(thm)], [c_226, c_52])).
% 3.45/1.53  tff(c_234, plain, (![B_67, A_68]: (r1_tarski(B_67, A_68) | ~m1_subset_1(B_67, k1_zfmisc_1(A_68)))), inference(negUnitSimplification, [status(thm)], [c_76, c_230])).
% 3.45/1.53  tff(c_243, plain, (r1_tarski('#skF_9', '#skF_8')), inference(resolution, [status(thm)], [c_78, c_234])).
% 3.45/1.53  tff(c_72, plain, (![A_32]: (k1_subset_1(A_32)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.45/1.53  tff(c_80, plain, (k1_subset_1('#skF_8')!='#skF_9' | ~r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.45/1.53  tff(c_88, plain, (k1_xboole_0!='#skF_9' | ~r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_80])).
% 3.45/1.53  tff(c_139, plain, (~r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(splitLeft, [status(thm)], [c_88])).
% 3.45/1.53  tff(c_86, plain, (r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9')) | k1_subset_1('#skF_8')='#skF_9'), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.45/1.53  tff(c_87, plain, (r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9')) | k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_86])).
% 3.45/1.53  tff(c_144, plain, (k1_xboole_0='#skF_9'), inference(negUnitSimplification, [status(thm)], [c_139, c_87])).
% 3.45/1.53  tff(c_44, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=k1_xboole_0 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.45/1.53  tff(c_146, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)='#skF_9' | ~r1_tarski(A_17, B_18))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_44])).
% 3.45/1.53  tff(c_264, plain, (k4_xboole_0('#skF_9', '#skF_8')='#skF_9'), inference(resolution, [status(thm)], [c_243, c_146])).
% 3.45/1.53  tff(c_48, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=A_21 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.45/1.53  tff(c_265, plain, (k3_xboole_0('#skF_9', '#skF_8')='#skF_9'), inference(resolution, [status(thm)], [c_243, c_48])).
% 3.45/1.53  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.45/1.53  tff(c_272, plain, (k3_xboole_0('#skF_8', '#skF_9')='#skF_9'), inference(superposition, [status(thm), theory('equality')], [c_265, c_2])).
% 3.45/1.53  tff(c_496, plain, (![A_91, B_92]: (k4_xboole_0(A_91, B_92)=k3_subset_1(A_91, B_92) | ~m1_subset_1(B_92, k1_zfmisc_1(A_91)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.45/1.53  tff(c_509, plain, (k4_xboole_0('#skF_8', '#skF_9')=k3_subset_1('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_78, c_496])).
% 3.45/1.53  tff(c_50, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.45/1.53  tff(c_520, plain, (k4_xboole_0('#skF_8', k3_subset_1('#skF_8', '#skF_9'))=k3_xboole_0('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_509, c_50])).
% 3.45/1.53  tff(c_523, plain, (k4_xboole_0('#skF_8', k3_subset_1('#skF_8', '#skF_9'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_272, c_520])).
% 3.45/1.53  tff(c_42, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | k4_xboole_0(A_17, B_18)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.45/1.53  tff(c_197, plain, (![A_59, B_60]: (r1_tarski(A_59, B_60) | k4_xboole_0(A_59, B_60)!='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_42])).
% 3.45/1.53  tff(c_604, plain, (![A_97, B_98]: (k3_xboole_0(A_97, B_98)=A_97 | k4_xboole_0(A_97, B_98)!='#skF_9')), inference(resolution, [status(thm)], [c_197, c_48])).
% 3.45/1.53  tff(c_620, plain, (k3_xboole_0('#skF_8', k3_subset_1('#skF_8', '#skF_9'))='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_523, c_604])).
% 3.45/1.53  tff(c_534, plain, (k3_xboole_0('#skF_8', k3_subset_1('#skF_8', '#skF_9'))=k4_xboole_0('#skF_8', '#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_523, c_50])).
% 3.45/1.53  tff(c_537, plain, (k3_xboole_0('#skF_8', k3_subset_1('#skF_8', '#skF_9'))=k3_subset_1('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_509, c_534])).
% 3.45/1.53  tff(c_723, plain, (k3_subset_1('#skF_8', '#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_620, c_537])).
% 3.45/1.53  tff(c_143, plain, (k4_xboole_0('#skF_9', k3_subset_1('#skF_8', '#skF_9'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_139])).
% 3.45/1.53  tff(c_145, plain, (k4_xboole_0('#skF_9', k3_subset_1('#skF_8', '#skF_9'))!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_144, c_143])).
% 3.45/1.53  tff(c_732, plain, (k4_xboole_0('#skF_9', '#skF_8')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_723, c_145])).
% 3.45/1.53  tff(c_736, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_264, c_732])).
% 3.45/1.53  tff(c_737, plain, (k1_xboole_0!='#skF_9'), inference(splitRight, [status(thm)], [c_88])).
% 3.45/1.53  tff(c_40, plain, (![A_15]: (r2_hidden('#skF_5'(A_15), A_15) | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.45/1.53  tff(c_738, plain, (r1_tarski('#skF_9', k3_subset_1('#skF_8', '#skF_9'))), inference(splitRight, [status(thm)], [c_88])).
% 3.45/1.53  tff(c_768, plain, (![A_108, B_109]: (k3_xboole_0(A_108, B_109)=A_108 | ~r1_tarski(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.45/1.53  tff(c_775, plain, (k3_xboole_0('#skF_9', k3_subset_1('#skF_8', '#skF_9'))='#skF_9'), inference(resolution, [status(thm)], [c_738, c_768])).
% 3.45/1.53  tff(c_1014, plain, (![D_130, B_131, A_132]: (r2_hidden(D_130, B_131) | ~r2_hidden(D_130, k3_xboole_0(A_132, B_131)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.45/1.53  tff(c_1302, plain, (![D_152]: (r2_hidden(D_152, k3_subset_1('#skF_8', '#skF_9')) | ~r2_hidden(D_152, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_775, c_1014])).
% 3.45/1.53  tff(c_1092, plain, (![A_138, B_139]: (k4_xboole_0(A_138, B_139)=k3_subset_1(A_138, B_139) | ~m1_subset_1(B_139, k1_zfmisc_1(A_138)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.45/1.53  tff(c_1105, plain, (k4_xboole_0('#skF_8', '#skF_9')=k3_subset_1('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_78, c_1092])).
% 3.45/1.53  tff(c_24, plain, (![D_14, B_10, A_9]: (~r2_hidden(D_14, B_10) | ~r2_hidden(D_14, k4_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.45/1.53  tff(c_1110, plain, (![D_14]: (~r2_hidden(D_14, '#skF_9') | ~r2_hidden(D_14, k3_subset_1('#skF_8', '#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_1105, c_24])).
% 3.45/1.53  tff(c_1320, plain, (![D_153]: (~r2_hidden(D_153, '#skF_9'))), inference(resolution, [status(thm)], [c_1302, c_1110])).
% 3.45/1.53  tff(c_1328, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_40, c_1320])).
% 3.45/1.53  tff(c_1333, plain, $false, inference(negUnitSimplification, [status(thm)], [c_737, c_1328])).
% 3.45/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.45/1.53  
% 3.45/1.53  Inference rules
% 3.45/1.53  ----------------------
% 3.45/1.53  #Ref     : 0
% 3.45/1.53  #Sup     : 304
% 3.45/1.53  #Fact    : 0
% 3.45/1.53  #Define  : 0
% 3.45/1.53  #Split   : 8
% 3.45/1.53  #Chain   : 0
% 3.45/1.53  #Close   : 0
% 3.45/1.53  
% 3.45/1.53  Ordering : KBO
% 3.45/1.53  
% 3.45/1.53  Simplification rules
% 3.45/1.53  ----------------------
% 3.45/1.53  #Subsume      : 50
% 3.45/1.53  #Demod        : 73
% 3.45/1.53  #Tautology    : 145
% 3.45/1.53  #SimpNegUnit  : 18
% 3.45/1.53  #BackRed      : 17
% 3.45/1.53  
% 3.45/1.53  #Partial instantiations: 0
% 3.45/1.53  #Strategies tried      : 1
% 3.45/1.53  
% 3.45/1.53  Timing (in seconds)
% 3.45/1.53  ----------------------
% 3.45/1.53  Preprocessing        : 0.35
% 3.45/1.54  Parsing              : 0.18
% 3.45/1.54  CNF conversion       : 0.03
% 3.45/1.54  Main loop            : 0.42
% 3.45/1.54  Inferencing          : 0.15
% 3.45/1.54  Reduction            : 0.13
% 3.45/1.54  Demodulation         : 0.10
% 3.45/1.54  BG Simplification    : 0.03
% 3.45/1.54  Subsumption          : 0.08
% 3.45/1.54  Abstraction          : 0.02
% 3.45/1.54  MUC search           : 0.00
% 3.45/1.54  Cooper               : 0.00
% 3.45/1.54  Total                : 0.80
% 3.45/1.54  Index Insertion      : 0.00
% 3.45/1.54  Index Deletion       : 0.00
% 3.45/1.54  Index Matching       : 0.00
% 3.45/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
