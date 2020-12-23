%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:14 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 140 expanded)
%              Number of leaves         :   32 (  60 expanded)
%              Depth                    :    9
%              Number of atoms          :   96 ( 204 expanded)
%              Number of equality atoms :   40 (  91 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_79,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_86,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_974,plain,(
    ! [A_138,B_139] :
      ( k4_xboole_0(A_138,B_139) = k3_subset_1(A_138,B_139)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(A_138)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_987,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_974])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_151,plain,(
    ! [A_59,B_60] :
      ( k4_xboole_0(A_59,B_60) = k1_xboole_0
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_159,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_151])).

tff(c_256,plain,(
    ! [A_75,C_76,B_77] :
      ( r1_tarski(k4_xboole_0(A_75,C_76),B_77)
      | ~ r1_tarski(A_75,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_292,plain,(
    ! [B_79,B_80] :
      ( r1_tarski(k1_xboole_0,B_79)
      | ~ r1_tarski(B_80,B_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_256])).

tff(c_303,plain,(
    ! [B_81] : r1_tarski(k1_xboole_0,B_81) ),
    inference(resolution,[status(thm)],[c_8,c_292])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_310,plain,(
    ! [B_81] : k4_xboole_0(k1_xboole_0,B_81) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_303,c_12])).

tff(c_52,plain,(
    ! [A_36] : k2_subset_1(A_36) = A_36 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_60,plain,
    ( k2_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_68,plain,
    ( '#skF_3' != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_60])).

tff(c_99,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_66,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | k2_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_67,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_66])).

tff(c_105,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_67])).

tff(c_107,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_58])).

tff(c_467,plain,(
    ! [A_88,B_89] :
      ( k4_xboole_0(A_88,B_89) = k3_subset_1(A_88,B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_477,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k3_subset_1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_107,c_467])).

tff(c_481,plain,(
    k3_subset_1('#skF_4','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_477])).

tff(c_100,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,B_46)
      | k4_xboole_0(A_45,B_46) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_104,plain,(
    k4_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_100,c_99])).

tff(c_116,plain,(
    k4_xboole_0(k3_subset_1('#skF_4','#skF_4'),'#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_104])).

tff(c_482,plain,(
    k4_xboole_0(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_481,c_116])).

tff(c_486,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_482])).

tff(c_487,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_56,plain,(
    ! [A_39] : ~ v1_xboole_0(k1_zfmisc_1(A_39)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_939,plain,(
    ! [B_134,A_135] :
      ( r2_hidden(B_134,A_135)
      | ~ m1_subset_1(B_134,A_135)
      | v1_xboole_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_30,plain,(
    ! [C_31,A_27] :
      ( r1_tarski(C_31,A_27)
      | ~ r2_hidden(C_31,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_946,plain,(
    ! [B_134,A_27] :
      ( r1_tarski(B_134,A_27)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(A_27))
      | v1_xboole_0(k1_zfmisc_1(A_27)) ) ),
    inference(resolution,[status(thm)],[c_939,c_30])).

tff(c_951,plain,(
    ! [B_136,A_137] :
      ( r1_tarski(B_136,A_137)
      | ~ m1_subset_1(B_136,k1_zfmisc_1(A_137)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_946])).

tff(c_964,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_951])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_966,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_964,c_4])).

tff(c_972,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_487,c_966])).

tff(c_991,plain,(
    k4_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_972])).

tff(c_1014,plain,(
    k3_subset_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_987,c_991])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1051,plain,(
    ! [A_140,B_141,C_142] : k4_xboole_0(k4_xboole_0(A_140,B_141),C_142) = k4_xboole_0(A_140,k2_xboole_0(B_141,C_142)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2388,plain,(
    ! [C_181] : k4_xboole_0(k3_subset_1('#skF_3','#skF_4'),C_181) = k4_xboole_0('#skF_3',k2_xboole_0('#skF_4',C_181)) ),
    inference(superposition,[status(thm),theory(equality)],[c_987,c_1051])).

tff(c_488,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_491,plain,(
    ! [A_94,B_95] :
      ( k4_xboole_0(A_94,B_95) = k1_xboole_0
      | ~ r1_tarski(A_94,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_502,plain,(
    k4_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_488,c_491])).

tff(c_2436,plain,(
    k4_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_4')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2388,c_502])).

tff(c_2483,plain,(
    k3_subset_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_987,c_2,c_2436])).

tff(c_2485,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1014,c_2483])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:13:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.35/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.61  
% 3.35/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.61  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.35/1.61  
% 3.35/1.61  %Foreground sorts:
% 3.35/1.61  
% 3.35/1.61  
% 3.35/1.61  %Background operators:
% 3.35/1.61  
% 3.35/1.61  
% 3.35/1.61  %Foreground operators:
% 3.35/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.35/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.35/1.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.35/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.35/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.35/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.35/1.61  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.35/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.35/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.35/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.35/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.35/1.61  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.35/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.35/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.35/1.61  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.35/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.35/1.61  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.35/1.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.35/1.61  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.35/1.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.35/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.35/1.61  
% 3.74/1.63  tff(f_93, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 3.74/1.63  tff(f_83, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.74/1.63  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.74/1.63  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.74/1.63  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t109_xboole_1)).
% 3.74/1.63  tff(f_79, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.74/1.63  tff(f_86, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.74/1.63  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.74/1.63  tff(f_62, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.74/1.63  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.74/1.63  tff(f_49, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.74/1.63  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.74/1.63  tff(c_974, plain, (![A_138, B_139]: (k4_xboole_0(A_138, B_139)=k3_subset_1(A_138, B_139) | ~m1_subset_1(B_139, k1_zfmisc_1(A_138)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.74/1.63  tff(c_987, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_974])).
% 3.74/1.63  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.74/1.63  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.74/1.63  tff(c_151, plain, (![A_59, B_60]: (k4_xboole_0(A_59, B_60)=k1_xboole_0 | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.74/1.63  tff(c_159, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_151])).
% 3.74/1.63  tff(c_256, plain, (![A_75, C_76, B_77]: (r1_tarski(k4_xboole_0(A_75, C_76), B_77) | ~r1_tarski(A_75, B_77))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.74/1.63  tff(c_292, plain, (![B_79, B_80]: (r1_tarski(k1_xboole_0, B_79) | ~r1_tarski(B_80, B_79))), inference(superposition, [status(thm), theory('equality')], [c_159, c_256])).
% 3.74/1.63  tff(c_303, plain, (![B_81]: (r1_tarski(k1_xboole_0, B_81))), inference(resolution, [status(thm)], [c_8, c_292])).
% 3.74/1.63  tff(c_12, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.74/1.63  tff(c_310, plain, (![B_81]: (k4_xboole_0(k1_xboole_0, B_81)=k1_xboole_0)), inference(resolution, [status(thm)], [c_303, c_12])).
% 3.74/1.63  tff(c_52, plain, (![A_36]: (k2_subset_1(A_36)=A_36)), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.74/1.63  tff(c_60, plain, (k2_subset_1('#skF_3')!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.74/1.63  tff(c_68, plain, ('#skF_3'!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_60])).
% 3.74/1.63  tff(c_99, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_68])).
% 3.74/1.63  tff(c_66, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | k2_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.74/1.63  tff(c_67, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_66])).
% 3.74/1.63  tff(c_105, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_99, c_67])).
% 3.74/1.63  tff(c_107, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_58])).
% 3.74/1.63  tff(c_467, plain, (![A_88, B_89]: (k4_xboole_0(A_88, B_89)=k3_subset_1(A_88, B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(A_88)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.74/1.63  tff(c_477, plain, (k4_xboole_0('#skF_4', '#skF_4')=k3_subset_1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_107, c_467])).
% 3.74/1.63  tff(c_481, plain, (k3_subset_1('#skF_4', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_159, c_477])).
% 3.74/1.63  tff(c_100, plain, (![A_45, B_46]: (r1_tarski(A_45, B_46) | k4_xboole_0(A_45, B_46)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.74/1.63  tff(c_104, plain, (k4_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_100, c_99])).
% 3.74/1.63  tff(c_116, plain, (k4_xboole_0(k3_subset_1('#skF_4', '#skF_4'), '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_105, c_104])).
% 3.74/1.63  tff(c_482, plain, (k4_xboole_0(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_481, c_116])).
% 3.74/1.63  tff(c_486, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_310, c_482])).
% 3.74/1.63  tff(c_487, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_68])).
% 3.74/1.63  tff(c_56, plain, (![A_39]: (~v1_xboole_0(k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.74/1.63  tff(c_939, plain, (![B_134, A_135]: (r2_hidden(B_134, A_135) | ~m1_subset_1(B_134, A_135) | v1_xboole_0(A_135))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.74/1.63  tff(c_30, plain, (![C_31, A_27]: (r1_tarski(C_31, A_27) | ~r2_hidden(C_31, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.74/1.63  tff(c_946, plain, (![B_134, A_27]: (r1_tarski(B_134, A_27) | ~m1_subset_1(B_134, k1_zfmisc_1(A_27)) | v1_xboole_0(k1_zfmisc_1(A_27)))), inference(resolution, [status(thm)], [c_939, c_30])).
% 3.74/1.63  tff(c_951, plain, (![B_136, A_137]: (r1_tarski(B_136, A_137) | ~m1_subset_1(B_136, k1_zfmisc_1(A_137)))), inference(negUnitSimplification, [status(thm)], [c_56, c_946])).
% 3.74/1.63  tff(c_964, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_951])).
% 3.74/1.63  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.74/1.63  tff(c_966, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_964, c_4])).
% 3.74/1.63  tff(c_972, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_487, c_966])).
% 3.74/1.63  tff(c_991, plain, (k4_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_972])).
% 3.74/1.63  tff(c_1014, plain, (k3_subset_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_987, c_991])).
% 3.74/1.63  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.74/1.63  tff(c_1051, plain, (![A_140, B_141, C_142]: (k4_xboole_0(k4_xboole_0(A_140, B_141), C_142)=k4_xboole_0(A_140, k2_xboole_0(B_141, C_142)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.74/1.63  tff(c_2388, plain, (![C_181]: (k4_xboole_0(k3_subset_1('#skF_3', '#skF_4'), C_181)=k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', C_181)))), inference(superposition, [status(thm), theory('equality')], [c_987, c_1051])).
% 3.74/1.63  tff(c_488, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_68])).
% 3.74/1.63  tff(c_491, plain, (![A_94, B_95]: (k4_xboole_0(A_94, B_95)=k1_xboole_0 | ~r1_tarski(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.74/1.63  tff(c_502, plain, (k4_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_488, c_491])).
% 3.74/1.63  tff(c_2436, plain, (k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_4'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2388, c_502])).
% 3.74/1.63  tff(c_2483, plain, (k3_subset_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_987, c_2, c_2436])).
% 3.74/1.63  tff(c_2485, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1014, c_2483])).
% 3.74/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.63  
% 3.74/1.63  Inference rules
% 3.74/1.63  ----------------------
% 3.74/1.63  #Ref     : 0
% 3.74/1.63  #Sup     : 599
% 3.74/1.63  #Fact    : 0
% 3.74/1.63  #Define  : 0
% 3.74/1.63  #Split   : 2
% 3.74/1.63  #Chain   : 0
% 3.74/1.63  #Close   : 0
% 3.74/1.63  
% 3.74/1.63  Ordering : KBO
% 3.74/1.63  
% 3.74/1.63  Simplification rules
% 3.74/1.63  ----------------------
% 3.74/1.63  #Subsume      : 47
% 3.74/1.63  #Demod        : 258
% 3.74/1.63  #Tautology    : 289
% 3.74/1.63  #SimpNegUnit  : 15
% 3.74/1.63  #BackRed      : 6
% 3.74/1.63  
% 3.74/1.63  #Partial instantiations: 0
% 3.74/1.63  #Strategies tried      : 1
% 3.74/1.63  
% 3.74/1.63  Timing (in seconds)
% 3.74/1.63  ----------------------
% 3.74/1.63  Preprocessing        : 0.33
% 3.74/1.63  Parsing              : 0.17
% 3.74/1.63  CNF conversion       : 0.02
% 3.74/1.63  Main loop            : 0.55
% 3.74/1.63  Inferencing          : 0.19
% 3.74/1.63  Reduction            : 0.20
% 3.74/1.63  Demodulation         : 0.15
% 3.74/1.63  BG Simplification    : 0.03
% 3.74/1.63  Subsumption          : 0.09
% 3.74/1.63  Abstraction          : 0.03
% 3.74/1.63  MUC search           : 0.00
% 3.74/1.63  Cooper               : 0.00
% 3.74/1.63  Total                : 0.91
% 3.74/1.63  Index Insertion      : 0.00
% 3.74/1.63  Index Deletion       : 0.00
% 3.74/1.63  Index Matching       : 0.00
% 3.74/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
