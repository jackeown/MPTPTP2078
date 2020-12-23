%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:47 EST 2020

% Result     : Theorem 3.81s
% Output     : CNFRefutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 140 expanded)
%              Number of leaves         :   28 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :  101 ( 240 expanded)
%              Number of equality atoms :   14 (  39 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,C)
            <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(c_38,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_154,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_32,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_186,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_32])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_174,plain,(
    ! [A_57,B_58] :
      ( k3_subset_1(A_57,k3_subset_1(A_57,B_58)) = B_58
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_180,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_174])).

tff(c_24,plain,(
    ! [A_27,B_28] :
      ( m1_subset_1(k3_subset_1(A_27,B_28),k1_zfmisc_1(A_27))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_238,plain,(
    ! [A_68,B_69] :
      ( k4_xboole_0(A_68,B_69) = k3_subset_1(A_68,B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_391,plain,(
    ! [A_86,B_87] :
      ( k4_xboole_0(A_86,k3_subset_1(A_86,B_87)) = k3_subset_1(A_86,k3_subset_1(A_86,B_87))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_86)) ) ),
    inference(resolution,[status(thm)],[c_24,c_238])).

tff(c_397,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_391])).

tff(c_402,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_397])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_455,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_6])).

tff(c_165,plain,(
    ! [A_48,C_49,B_50] :
      ( r1_xboole_0(A_48,k4_xboole_0(C_49,B_50))
      | ~ r1_tarski(A_48,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_168,plain,(
    ! [C_49,B_50,A_48] :
      ( r1_xboole_0(k4_xboole_0(C_49,B_50),A_48)
      | ~ r1_tarski(A_48,B_50) ) ),
    inference(resolution,[status(thm)],[c_165,c_2])).

tff(c_460,plain,(
    ! [A_88] :
      ( r1_xboole_0('#skF_2',A_88)
      | ~ r1_tarski(A_88,k3_subset_1('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_168])).

tff(c_473,plain,(
    r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_154,c_460])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_179,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_28,c_174])).

tff(c_395,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_391])).

tff(c_400,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_395])).

tff(c_14,plain,(
    ! [A_16,B_17,C_18] :
      ( r1_tarski(A_16,k4_xboole_0(B_17,C_18))
      | ~ r1_xboole_0(A_16,C_18)
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1200,plain,(
    ! [A_127] :
      ( r1_tarski(A_127,'#skF_3')
      | ~ r1_xboole_0(A_127,k3_subset_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_127,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_14])).

tff(c_1203,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_473,c_1200])).

tff(c_1221,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_455,c_1203])).

tff(c_1223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_1221])).

tff(c_1224,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1295,plain,(
    ! [A_148,B_149] :
      ( k4_xboole_0(A_148,B_149) = k3_subset_1(A_148,B_149)
      | ~ m1_subset_1(B_149,k1_zfmisc_1(A_148)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1306,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_1295])).

tff(c_1236,plain,(
    ! [A_130,C_131,B_132] :
      ( r1_xboole_0(A_130,k4_xboole_0(C_131,B_132))
      | ~ r1_tarski(A_130,B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1239,plain,(
    ! [C_131,B_132,A_130] :
      ( r1_xboole_0(k4_xboole_0(C_131,B_132),A_130)
      | ~ r1_tarski(A_130,B_132) ) ),
    inference(resolution,[status(thm)],[c_1236,c_2])).

tff(c_1351,plain,(
    ! [A_130] :
      ( r1_xboole_0(k3_subset_1('#skF_1','#skF_3'),A_130)
      | ~ r1_tarski(A_130,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1306,c_1239])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] :
      ( r1_tarski(k4_xboole_0(A_7,B_8),C_9)
      | ~ r1_tarski(A_7,k2_xboole_0(B_8,C_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1747,plain,(
    ! [C_186] :
      ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),C_186)
      | ~ r1_tarski('#skF_1',k2_xboole_0('#skF_3',C_186)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1306,c_8])).

tff(c_1225,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1770,plain,(
    ~ r1_tarski('#skF_1',k2_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_1747,c_1225])).

tff(c_1357,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1306,c_6])).

tff(c_1307,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_1295])).

tff(c_1373,plain,(
    ! [A_155,B_156,C_157] :
      ( r1_tarski(A_155,k4_xboole_0(B_156,C_157))
      | ~ r1_xboole_0(A_155,C_157)
      | ~ r1_tarski(A_155,B_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1895,plain,(
    ! [A_194] :
      ( r1_tarski(A_194,k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_xboole_0(A_194,'#skF_2')
      | ~ r1_tarski(A_194,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1307,c_1373])).

tff(c_10,plain,(
    ! [A_10,B_11,C_12] :
      ( r1_tarski(A_10,k2_xboole_0(B_11,C_12))
      | ~ r1_tarski(k4_xboole_0(A_10,B_11),C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1345,plain,(
    ! [C_12] :
      ( r1_tarski('#skF_1',k2_xboole_0('#skF_3',C_12))
      | ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),C_12) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1306,c_10])).

tff(c_1909,plain,
    ( r1_tarski('#skF_1',k2_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2')))
    | ~ r1_xboole_0(k3_subset_1('#skF_1','#skF_3'),'#skF_2')
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1895,c_1345])).

tff(c_1924,plain,
    ( r1_tarski('#skF_1',k2_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2')))
    | ~ r1_xboole_0(k3_subset_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1357,c_1909])).

tff(c_1925,plain,(
    ~ r1_xboole_0(k3_subset_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_1770,c_1924])).

tff(c_1932,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_1351,c_1925])).

tff(c_1936,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1224,c_1932])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:48:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.81/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.81/1.66  
% 3.81/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.81/1.66  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.81/1.66  
% 3.81/1.66  %Foreground sorts:
% 3.81/1.66  
% 3.81/1.66  
% 3.81/1.66  %Background operators:
% 3.81/1.66  
% 3.81/1.66  
% 3.81/1.66  %Foreground operators:
% 3.81/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.81/1.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.81/1.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.81/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.81/1.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.81/1.66  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.81/1.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.81/1.66  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.81/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.81/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.81/1.66  tff('#skF_1', type, '#skF_1': $i).
% 3.81/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.81/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.81/1.66  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.81/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.81/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.81/1.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.81/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.81/1.66  
% 3.81/1.68  tff(f_79, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 3.81/1.68  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.81/1.68  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.81/1.68  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.81/1.68  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.81/1.68  tff(f_45, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 3.81/1.68  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.81/1.68  tff(f_51, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 3.81/1.68  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 3.81/1.68  tff(f_41, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 3.81/1.68  tff(c_38, plain, (r1_tarski('#skF_2', '#skF_3') | r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.81/1.68  tff(c_154, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_38])).
% 3.81/1.68  tff(c_32, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.81/1.68  tff(c_186, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_154, c_32])).
% 3.81/1.68  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.81/1.68  tff(c_174, plain, (![A_57, B_58]: (k3_subset_1(A_57, k3_subset_1(A_57, B_58))=B_58 | ~m1_subset_1(B_58, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.81/1.68  tff(c_180, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_30, c_174])).
% 3.81/1.68  tff(c_24, plain, (![A_27, B_28]: (m1_subset_1(k3_subset_1(A_27, B_28), k1_zfmisc_1(A_27)) | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.81/1.68  tff(c_238, plain, (![A_68, B_69]: (k4_xboole_0(A_68, B_69)=k3_subset_1(A_68, B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.81/1.68  tff(c_391, plain, (![A_86, B_87]: (k4_xboole_0(A_86, k3_subset_1(A_86, B_87))=k3_subset_1(A_86, k3_subset_1(A_86, B_87)) | ~m1_subset_1(B_87, k1_zfmisc_1(A_86)))), inference(resolution, [status(thm)], [c_24, c_238])).
% 3.81/1.68  tff(c_397, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_391])).
% 3.81/1.68  tff(c_402, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_180, c_397])).
% 3.81/1.68  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.81/1.68  tff(c_455, plain, (r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_402, c_6])).
% 3.81/1.68  tff(c_165, plain, (![A_48, C_49, B_50]: (r1_xboole_0(A_48, k4_xboole_0(C_49, B_50)) | ~r1_tarski(A_48, B_50))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.81/1.68  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.81/1.68  tff(c_168, plain, (![C_49, B_50, A_48]: (r1_xboole_0(k4_xboole_0(C_49, B_50), A_48) | ~r1_tarski(A_48, B_50))), inference(resolution, [status(thm)], [c_165, c_2])).
% 3.81/1.68  tff(c_460, plain, (![A_88]: (r1_xboole_0('#skF_2', A_88) | ~r1_tarski(A_88, k3_subset_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_402, c_168])).
% 3.81/1.68  tff(c_473, plain, (r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_154, c_460])).
% 3.81/1.68  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.81/1.68  tff(c_179, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_28, c_174])).
% 3.81/1.68  tff(c_395, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_391])).
% 3.81/1.68  tff(c_400, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_179, c_395])).
% 3.81/1.68  tff(c_14, plain, (![A_16, B_17, C_18]: (r1_tarski(A_16, k4_xboole_0(B_17, C_18)) | ~r1_xboole_0(A_16, C_18) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.81/1.68  tff(c_1200, plain, (![A_127]: (r1_tarski(A_127, '#skF_3') | ~r1_xboole_0(A_127, k3_subset_1('#skF_1', '#skF_3')) | ~r1_tarski(A_127, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_400, c_14])).
% 3.81/1.68  tff(c_1203, plain, (r1_tarski('#skF_2', '#skF_3') | ~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_473, c_1200])).
% 3.81/1.68  tff(c_1221, plain, (r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_455, c_1203])).
% 3.81/1.68  tff(c_1223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_186, c_1221])).
% 3.81/1.68  tff(c_1224, plain, (r1_tarski('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_38])).
% 3.81/1.68  tff(c_1295, plain, (![A_148, B_149]: (k4_xboole_0(A_148, B_149)=k3_subset_1(A_148, B_149) | ~m1_subset_1(B_149, k1_zfmisc_1(A_148)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.81/1.68  tff(c_1306, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_1295])).
% 3.81/1.68  tff(c_1236, plain, (![A_130, C_131, B_132]: (r1_xboole_0(A_130, k4_xboole_0(C_131, B_132)) | ~r1_tarski(A_130, B_132))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.81/1.68  tff(c_1239, plain, (![C_131, B_132, A_130]: (r1_xboole_0(k4_xboole_0(C_131, B_132), A_130) | ~r1_tarski(A_130, B_132))), inference(resolution, [status(thm)], [c_1236, c_2])).
% 3.81/1.68  tff(c_1351, plain, (![A_130]: (r1_xboole_0(k3_subset_1('#skF_1', '#skF_3'), A_130) | ~r1_tarski(A_130, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1306, c_1239])).
% 3.81/1.68  tff(c_8, plain, (![A_7, B_8, C_9]: (r1_tarski(k4_xboole_0(A_7, B_8), C_9) | ~r1_tarski(A_7, k2_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.81/1.68  tff(c_1747, plain, (![C_186]: (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), C_186) | ~r1_tarski('#skF_1', k2_xboole_0('#skF_3', C_186)))), inference(superposition, [status(thm), theory('equality')], [c_1306, c_8])).
% 3.81/1.68  tff(c_1225, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_38])).
% 3.81/1.68  tff(c_1770, plain, (~r1_tarski('#skF_1', k2_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_1747, c_1225])).
% 3.81/1.68  tff(c_1357, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1306, c_6])).
% 3.81/1.68  tff(c_1307, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_1295])).
% 3.81/1.68  tff(c_1373, plain, (![A_155, B_156, C_157]: (r1_tarski(A_155, k4_xboole_0(B_156, C_157)) | ~r1_xboole_0(A_155, C_157) | ~r1_tarski(A_155, B_156))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.81/1.68  tff(c_1895, plain, (![A_194]: (r1_tarski(A_194, k3_subset_1('#skF_1', '#skF_2')) | ~r1_xboole_0(A_194, '#skF_2') | ~r1_tarski(A_194, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1307, c_1373])).
% 3.81/1.68  tff(c_10, plain, (![A_10, B_11, C_12]: (r1_tarski(A_10, k2_xboole_0(B_11, C_12)) | ~r1_tarski(k4_xboole_0(A_10, B_11), C_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.81/1.68  tff(c_1345, plain, (![C_12]: (r1_tarski('#skF_1', k2_xboole_0('#skF_3', C_12)) | ~r1_tarski(k3_subset_1('#skF_1', '#skF_3'), C_12))), inference(superposition, [status(thm), theory('equality')], [c_1306, c_10])).
% 3.81/1.68  tff(c_1909, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_2'))) | ~r1_xboole_0(k3_subset_1('#skF_1', '#skF_3'), '#skF_2') | ~r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_1895, c_1345])).
% 3.81/1.68  tff(c_1924, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_2'))) | ~r1_xboole_0(k3_subset_1('#skF_1', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1357, c_1909])).
% 3.81/1.68  tff(c_1925, plain, (~r1_xboole_0(k3_subset_1('#skF_1', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_1770, c_1924])).
% 3.81/1.68  tff(c_1932, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_1351, c_1925])).
% 3.81/1.68  tff(c_1936, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1224, c_1932])).
% 3.81/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.81/1.68  
% 3.81/1.68  Inference rules
% 3.81/1.68  ----------------------
% 3.81/1.68  #Ref     : 0
% 3.81/1.68  #Sup     : 432
% 3.81/1.68  #Fact    : 0
% 3.81/1.68  #Define  : 0
% 3.81/1.68  #Split   : 5
% 3.81/1.68  #Chain   : 0
% 3.81/1.68  #Close   : 0
% 3.81/1.68  
% 3.81/1.68  Ordering : KBO
% 3.81/1.68  
% 3.81/1.68  Simplification rules
% 3.81/1.68  ----------------------
% 3.81/1.68  #Subsume      : 24
% 3.81/1.68  #Demod        : 162
% 3.81/1.68  #Tautology    : 195
% 3.81/1.68  #SimpNegUnit  : 2
% 3.81/1.68  #BackRed      : 0
% 3.81/1.68  
% 3.81/1.68  #Partial instantiations: 0
% 3.81/1.68  #Strategies tried      : 1
% 3.81/1.68  
% 3.81/1.68  Timing (in seconds)
% 3.81/1.68  ----------------------
% 3.81/1.68  Preprocessing        : 0.30
% 3.81/1.68  Parsing              : 0.16
% 3.81/1.68  CNF conversion       : 0.02
% 3.81/1.68  Main loop            : 0.58
% 3.81/1.68  Inferencing          : 0.20
% 3.81/1.68  Reduction            : 0.22
% 3.81/1.68  Demodulation         : 0.17
% 3.81/1.68  BG Simplification    : 0.02
% 3.81/1.68  Subsumption          : 0.10
% 3.81/1.68  Abstraction          : 0.02
% 3.81/1.68  MUC search           : 0.00
% 3.81/1.68  Cooper               : 0.00
% 3.81/1.68  Total                : 0.91
% 3.81/1.68  Index Insertion      : 0.00
% 3.81/1.68  Index Deletion       : 0.00
% 3.81/1.68  Index Matching       : 0.00
% 3.81/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
