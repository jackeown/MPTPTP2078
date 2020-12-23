%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:01 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.91s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 243 expanded)
%              Number of leaves         :   32 (  92 expanded)
%              Depth                    :   12
%              Number of atoms          :  109 ( 311 expanded)
%              Number of equality atoms :   58 ( 183 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_69,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_45,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_76,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_42,plain,(
    ! [A_23] : k1_subset_1(A_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_50,plain,
    ( k1_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_58,plain,
    ( k1_xboole_0 != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_50])).

tff(c_130,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_56,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_57,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_56])).

tff(c_137,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_57])).

tff(c_20,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_139,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_20])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_187,plain,(
    ! [A_47,B_48] :
      ( k3_xboole_0(A_47,B_48) = A_47
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_195,plain,(
    ! [B_4] : k3_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_187])).

tff(c_253,plain,(
    ! [A_60,B_61] : k5_xboole_0(A_60,k3_xboole_0(A_60,B_61)) = k4_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_262,plain,(
    ! [B_4] : k5_xboole_0(B_4,B_4) = k4_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_253])).

tff(c_279,plain,(
    ! [B_62] : k4_xboole_0(B_62,B_62) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_262])).

tff(c_14,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_284,plain,(
    ! [B_62] : r1_tarski('#skF_4',B_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_14])).

tff(c_292,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_130])).

tff(c_293,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_16,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_804,plain,(
    ! [A_97,B_98,C_99] : k5_xboole_0(k5_xboole_0(A_97,B_98),C_99) = k5_xboole_0(A_97,k5_xboole_0(B_98,C_99)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1239,plain,(
    ! [A_110,C_111] : k5_xboole_0(A_110,k5_xboole_0(A_110,C_111)) = k5_xboole_0(k1_xboole_0,C_111) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_804])).

tff(c_1335,plain,(
    ! [A_15] : k5_xboole_0(k1_xboole_0,A_15) = k5_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_1239])).

tff(c_1359,plain,(
    ! [A_15] : k5_xboole_0(k1_xboole_0,A_15) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1335])).

tff(c_859,plain,(
    ! [A_15,C_99] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_99)) = k5_xboole_0(k1_xboole_0,C_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_804])).

tff(c_1360,plain,(
    ! [A_15,C_99] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_99)) = C_99 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1359,c_859])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_618,plain,(
    ! [A_91,B_92] :
      ( k4_xboole_0(A_91,B_92) = k3_subset_1(A_91,B_92)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_631,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_618])).

tff(c_635,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_631,c_14])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_644,plain,
    ( k3_subset_1('#skF_3','#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_635,c_4])).

tff(c_1526,plain,(
    ~ r1_tarski('#skF_3',k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_644])).

tff(c_46,plain,(
    ! [A_26] : ~ v1_xboole_0(k1_zfmisc_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_341,plain,(
    ! [B_72,A_73] :
      ( r2_hidden(B_72,A_73)
      | ~ m1_subset_1(B_72,A_73)
      | v1_xboole_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_22,plain,(
    ! [C_20,A_16] :
      ( r1_tarski(C_20,A_16)
      | ~ r2_hidden(C_20,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_345,plain,(
    ! [B_72,A_16] :
      ( r1_tarski(B_72,A_16)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_16))
      | v1_xboole_0(k1_zfmisc_1(A_16)) ) ),
    inference(resolution,[status(thm)],[c_341,c_22])).

tff(c_349,plain,(
    ! [B_74,A_75] :
      ( r1_tarski(B_74,A_75)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_75)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_345])).

tff(c_358,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_349])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_362,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_358,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_387,plain,(
    ! [A_80,B_81] : k5_xboole_0(A_80,k3_xboole_0(A_80,B_81)) = k4_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_682,plain,(
    ! [A_93,B_94] : k5_xboole_0(A_93,k3_xboole_0(B_94,A_93)) = k4_xboole_0(A_93,B_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_387])).

tff(c_708,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_682])).

tff(c_727,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_631,c_708])).

tff(c_826,plain,(
    ! [A_97,B_98] : k5_xboole_0(A_97,k5_xboole_0(B_98,k5_xboole_0(A_97,B_98))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_804,c_20])).

tff(c_1438,plain,(
    ! [A_113,C_114] : k5_xboole_0(A_113,k5_xboole_0(A_113,C_114)) = C_114 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1359,c_859])).

tff(c_1482,plain,(
    ! [B_98,A_97] : k5_xboole_0(B_98,k5_xboole_0(A_97,B_98)) = k5_xboole_0(A_97,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_826,c_1438])).

tff(c_1530,plain,(
    ! [B_115,A_116] : k5_xboole_0(B_115,k5_xboole_0(A_116,B_115)) = A_116 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1482])).

tff(c_1836,plain,(
    ! [A_123,C_124] : k5_xboole_0(k5_xboole_0(A_123,C_124),C_124) = A_123 ),
    inference(superposition,[status(thm),theory(equality)],[c_1360,c_1530])).

tff(c_1917,plain,(
    k5_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_727,c_1836])).

tff(c_294,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_310,plain,(
    ! [A_67,B_68] :
      ( k3_xboole_0(A_67,B_68) = A_67
      | ~ r1_tarski(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_320,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_294,c_310])).

tff(c_714,plain,(
    k5_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = k4_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_682])).

tff(c_2385,plain,(
    k4_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1917,c_714])).

tff(c_2401,plain,(
    r1_tarski('#skF_3',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2385,c_14])).

tff(c_2409,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1526,c_2401])).

tff(c_2410,plain,(
    k3_subset_1('#skF_3','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_644])).

tff(c_2413,plain,(
    k5_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2410,c_727])).

tff(c_2450,plain,(
    k5_xboole_0('#skF_3','#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2413,c_1360])).

tff(c_2466,plain,(
    k5_xboole_0('#skF_3',k5_xboole_0('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2450,c_826])).

tff(c_2477,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1360,c_2466])).

tff(c_2479,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_293,c_2477])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.62/1.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/1.74  
% 3.85/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/1.75  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.85/1.75  
% 3.85/1.75  %Foreground sorts:
% 3.85/1.75  
% 3.85/1.75  
% 3.85/1.75  %Background operators:
% 3.85/1.75  
% 3.85/1.75  
% 3.85/1.75  %Foreground operators:
% 3.85/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.85/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.85/1.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.85/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.85/1.75  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.85/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.85/1.75  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.85/1.75  tff('#skF_3', type, '#skF_3': $i).
% 3.85/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.85/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.85/1.75  tff('#skF_4', type, '#skF_4': $i).
% 3.85/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.85/1.75  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.85/1.75  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.85/1.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.85/1.75  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.85/1.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.85/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.85/1.75  
% 3.91/1.76  tff(f_69, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 3.91/1.76  tff(f_83, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 3.91/1.76  tff(f_47, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.91/1.76  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.91/1.76  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.91/1.76  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.91/1.76  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.91/1.76  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.91/1.76  tff(f_45, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.91/1.76  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.91/1.76  tff(f_76, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.91/1.76  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.91/1.76  tff(f_54, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.91/1.76  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.91/1.76  tff(c_42, plain, (![A_23]: (k1_subset_1(A_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.91/1.76  tff(c_50, plain, (k1_subset_1('#skF_3')!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.91/1.76  tff(c_58, plain, (k1_xboole_0!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_50])).
% 3.91/1.76  tff(c_130, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_58])).
% 3.91/1.76  tff(c_56, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.91/1.76  tff(c_57, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_56])).
% 3.91/1.76  tff(c_137, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_130, c_57])).
% 3.91/1.76  tff(c_20, plain, (![A_15]: (k5_xboole_0(A_15, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.91/1.76  tff(c_139, plain, (![A_15]: (k5_xboole_0(A_15, A_15)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_137, c_20])).
% 3.91/1.76  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.91/1.76  tff(c_187, plain, (![A_47, B_48]: (k3_xboole_0(A_47, B_48)=A_47 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.91/1.76  tff(c_195, plain, (![B_4]: (k3_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_187])).
% 3.91/1.76  tff(c_253, plain, (![A_60, B_61]: (k5_xboole_0(A_60, k3_xboole_0(A_60, B_61))=k4_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.91/1.76  tff(c_262, plain, (![B_4]: (k5_xboole_0(B_4, B_4)=k4_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_195, c_253])).
% 3.91/1.76  tff(c_279, plain, (![B_62]: (k4_xboole_0(B_62, B_62)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_262])).
% 3.91/1.76  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.91/1.76  tff(c_284, plain, (![B_62]: (r1_tarski('#skF_4', B_62))), inference(superposition, [status(thm), theory('equality')], [c_279, c_14])).
% 3.91/1.76  tff(c_292, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_284, c_130])).
% 3.91/1.76  tff(c_293, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_58])).
% 3.91/1.76  tff(c_16, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.91/1.76  tff(c_804, plain, (![A_97, B_98, C_99]: (k5_xboole_0(k5_xboole_0(A_97, B_98), C_99)=k5_xboole_0(A_97, k5_xboole_0(B_98, C_99)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.91/1.76  tff(c_1239, plain, (![A_110, C_111]: (k5_xboole_0(A_110, k5_xboole_0(A_110, C_111))=k5_xboole_0(k1_xboole_0, C_111))), inference(superposition, [status(thm), theory('equality')], [c_20, c_804])).
% 3.91/1.76  tff(c_1335, plain, (![A_15]: (k5_xboole_0(k1_xboole_0, A_15)=k5_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_1239])).
% 3.91/1.76  tff(c_1359, plain, (![A_15]: (k5_xboole_0(k1_xboole_0, A_15)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1335])).
% 3.91/1.76  tff(c_859, plain, (![A_15, C_99]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_99))=k5_xboole_0(k1_xboole_0, C_99))), inference(superposition, [status(thm), theory('equality')], [c_20, c_804])).
% 3.91/1.76  tff(c_1360, plain, (![A_15, C_99]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_99))=C_99)), inference(demodulation, [status(thm), theory('equality')], [c_1359, c_859])).
% 3.91/1.76  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.91/1.76  tff(c_618, plain, (![A_91, B_92]: (k4_xboole_0(A_91, B_92)=k3_subset_1(A_91, B_92) | ~m1_subset_1(B_92, k1_zfmisc_1(A_91)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.91/1.76  tff(c_631, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_618])).
% 3.91/1.76  tff(c_635, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_631, c_14])).
% 3.91/1.76  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.91/1.76  tff(c_644, plain, (k3_subset_1('#skF_3', '#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_635, c_4])).
% 3.91/1.76  tff(c_1526, plain, (~r1_tarski('#skF_3', k3_subset_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_644])).
% 3.91/1.76  tff(c_46, plain, (![A_26]: (~v1_xboole_0(k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.91/1.76  tff(c_341, plain, (![B_72, A_73]: (r2_hidden(B_72, A_73) | ~m1_subset_1(B_72, A_73) | v1_xboole_0(A_73))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.91/1.76  tff(c_22, plain, (![C_20, A_16]: (r1_tarski(C_20, A_16) | ~r2_hidden(C_20, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.91/1.76  tff(c_345, plain, (![B_72, A_16]: (r1_tarski(B_72, A_16) | ~m1_subset_1(B_72, k1_zfmisc_1(A_16)) | v1_xboole_0(k1_zfmisc_1(A_16)))), inference(resolution, [status(thm)], [c_341, c_22])).
% 3.91/1.76  tff(c_349, plain, (![B_74, A_75]: (r1_tarski(B_74, A_75) | ~m1_subset_1(B_74, k1_zfmisc_1(A_75)))), inference(negUnitSimplification, [status(thm)], [c_46, c_345])).
% 3.91/1.76  tff(c_358, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_349])).
% 3.91/1.76  tff(c_12, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.91/1.76  tff(c_362, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_358, c_12])).
% 3.91/1.76  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.91/1.76  tff(c_387, plain, (![A_80, B_81]: (k5_xboole_0(A_80, k3_xboole_0(A_80, B_81))=k4_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.91/1.76  tff(c_682, plain, (![A_93, B_94]: (k5_xboole_0(A_93, k3_xboole_0(B_94, A_93))=k4_xboole_0(A_93, B_94))), inference(superposition, [status(thm), theory('equality')], [c_2, c_387])).
% 3.91/1.76  tff(c_708, plain, (k5_xboole_0('#skF_3', '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_362, c_682])).
% 3.91/1.76  tff(c_727, plain, (k5_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_631, c_708])).
% 3.91/1.76  tff(c_826, plain, (![A_97, B_98]: (k5_xboole_0(A_97, k5_xboole_0(B_98, k5_xboole_0(A_97, B_98)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_804, c_20])).
% 3.91/1.76  tff(c_1438, plain, (![A_113, C_114]: (k5_xboole_0(A_113, k5_xboole_0(A_113, C_114))=C_114)), inference(demodulation, [status(thm), theory('equality')], [c_1359, c_859])).
% 3.91/1.76  tff(c_1482, plain, (![B_98, A_97]: (k5_xboole_0(B_98, k5_xboole_0(A_97, B_98))=k5_xboole_0(A_97, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_826, c_1438])).
% 3.91/1.76  tff(c_1530, plain, (![B_115, A_116]: (k5_xboole_0(B_115, k5_xboole_0(A_116, B_115))=A_116)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1482])).
% 3.91/1.76  tff(c_1836, plain, (![A_123, C_124]: (k5_xboole_0(k5_xboole_0(A_123, C_124), C_124)=A_123)), inference(superposition, [status(thm), theory('equality')], [c_1360, c_1530])).
% 3.91/1.76  tff(c_1917, plain, (k5_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_727, c_1836])).
% 3.91/1.76  tff(c_294, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_58])).
% 3.91/1.76  tff(c_310, plain, (![A_67, B_68]: (k3_xboole_0(A_67, B_68)=A_67 | ~r1_tarski(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.91/1.76  tff(c_320, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_294, c_310])).
% 3.91/1.76  tff(c_714, plain, (k5_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')=k4_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_320, c_682])).
% 3.91/1.76  tff(c_2385, plain, (k4_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1917, c_714])).
% 3.91/1.76  tff(c_2401, plain, (r1_tarski('#skF_3', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2385, c_14])).
% 3.91/1.76  tff(c_2409, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1526, c_2401])).
% 3.91/1.76  tff(c_2410, plain, (k3_subset_1('#skF_3', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_644])).
% 3.91/1.76  tff(c_2413, plain, (k5_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2410, c_727])).
% 3.91/1.76  tff(c_2450, plain, (k5_xboole_0('#skF_3', '#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2413, c_1360])).
% 3.91/1.76  tff(c_2466, plain, (k5_xboole_0('#skF_3', k5_xboole_0('#skF_3', '#skF_4'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2450, c_826])).
% 3.91/1.76  tff(c_2477, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1360, c_2466])).
% 3.91/1.76  tff(c_2479, plain, $false, inference(negUnitSimplification, [status(thm)], [c_293, c_2477])).
% 3.91/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.76  
% 3.91/1.76  Inference rules
% 3.91/1.76  ----------------------
% 3.91/1.76  #Ref     : 0
% 3.91/1.76  #Sup     : 586
% 3.91/1.76  #Fact    : 0
% 3.91/1.76  #Define  : 0
% 3.91/1.76  #Split   : 5
% 3.91/1.76  #Chain   : 0
% 3.91/1.76  #Close   : 0
% 3.91/1.76  
% 3.91/1.76  Ordering : KBO
% 3.91/1.76  
% 3.91/1.76  Simplification rules
% 3.91/1.76  ----------------------
% 3.91/1.76  #Subsume      : 17
% 3.91/1.76  #Demod        : 450
% 3.91/1.76  #Tautology    : 425
% 3.91/1.76  #SimpNegUnit  : 10
% 3.91/1.76  #BackRed      : 17
% 3.91/1.76  
% 3.91/1.76  #Partial instantiations: 0
% 3.91/1.76  #Strategies tried      : 1
% 3.91/1.76  
% 3.91/1.76  Timing (in seconds)
% 3.91/1.76  ----------------------
% 3.91/1.77  Preprocessing        : 0.33
% 3.91/1.77  Parsing              : 0.18
% 3.91/1.77  CNF conversion       : 0.02
% 3.91/1.77  Main loop            : 0.60
% 3.91/1.77  Inferencing          : 0.20
% 3.91/1.77  Reduction            : 0.23
% 3.91/1.77  Demodulation         : 0.18
% 3.91/1.77  BG Simplification    : 0.03
% 3.91/1.77  Subsumption          : 0.09
% 3.91/1.77  Abstraction          : 0.03
% 3.91/1.77  MUC search           : 0.00
% 3.91/1.77  Cooper               : 0.00
% 3.91/1.77  Total                : 0.97
% 3.91/1.77  Index Insertion      : 0.00
% 3.91/1.77  Index Deletion       : 0.00
% 3.91/1.77  Index Matching       : 0.00
% 3.91/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
