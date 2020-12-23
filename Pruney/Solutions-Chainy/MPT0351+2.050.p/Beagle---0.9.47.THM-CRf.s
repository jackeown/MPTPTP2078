%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:43 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 114 expanded)
%              Number of leaves         :   34 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :   82 ( 138 expanded)
%              Number of equality atoms :   40 (  65 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_66,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_68,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_44,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_52,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_50,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k4_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_34,plain,(
    ! [A_29] : k2_subset_1(A_29) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_36,plain,(
    ! [A_30] : m1_subset_1(k2_subset_1(A_30),k1_zfmisc_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_45,plain,(
    ! [A_30] : m1_subset_1(A_30,k1_zfmisc_1(A_30)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36])).

tff(c_400,plain,(
    ! [A_87,B_88,C_89] :
      ( k4_subset_1(A_87,B_88,C_89) = k2_xboole_0(B_88,C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(A_87))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_431,plain,(
    ! [A_91,B_92] :
      ( k4_subset_1(A_91,B_92,A_91) = k2_xboole_0(B_92,A_91)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_91)) ) ),
    inference(resolution,[status(thm)],[c_45,c_400])).

tff(c_438,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_431])).

tff(c_42,plain,(
    k4_subset_1('#skF_2','#skF_3',k2_subset_1('#skF_2')) != k2_subset_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_46,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_42])).

tff(c_448,plain,(
    k2_xboole_0('#skF_3','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_438,c_46])).

tff(c_18,plain,(
    ! [A_12] : k2_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_68,plain,(
    ! [A_42,B_43] : k4_xboole_0(A_42,k2_xboole_0(A_42,B_43)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_75,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_68])).

tff(c_14,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_118,plain,(
    ! [A_47,B_48] :
      ( k3_xboole_0(A_47,B_48) = A_47
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_122,plain,(
    ! [B_9] : k3_xboole_0(B_9,B_9) = B_9 ),
    inference(resolution,[status(thm)],[c_14,c_118])).

tff(c_209,plain,(
    ! [A_63,B_64] : k5_xboole_0(A_63,k3_xboole_0(A_63,B_64)) = k4_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_218,plain,(
    ! [B_9] : k5_xboole_0(B_9,B_9) = k4_xboole_0(B_9,B_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_209])).

tff(c_227,plain,(
    ! [B_9] : k5_xboole_0(B_9,B_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_218])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_323,plain,(
    ! [C_76,A_77,B_78] :
      ( r2_hidden(C_76,A_77)
      | ~ r2_hidden(C_76,B_78)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_339,plain,(
    ! [A_82,B_83,A_84] :
      ( r2_hidden('#skF_1'(A_82,B_83),A_84)
      | ~ m1_subset_1(A_82,k1_zfmisc_1(A_84))
      | r1_tarski(A_82,B_83) ) ),
    inference(resolution,[status(thm)],[c_8,c_323])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_351,plain,(
    ! [A_85,A_86] :
      ( ~ m1_subset_1(A_85,k1_zfmisc_1(A_86))
      | r1_tarski(A_85,A_86) ) ),
    inference(resolution,[status(thm)],[c_339,c_6])).

tff(c_360,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_351])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0(A_13,B_14) = A_13
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_367,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_360,c_20])).

tff(c_16,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_374,plain,(
    k5_xboole_0('#skF_3','#skF_3') = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_16])).

tff(c_377,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_374])).

tff(c_22,plain,(
    ! [A_15,B_16] : k2_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_382,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_22])).

tff(c_385,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_382])).

tff(c_411,plain,(
    ! [B_90] :
      ( k4_subset_1('#skF_2',B_90,'#skF_3') = k2_xboole_0(B_90,'#skF_3')
      | ~ m1_subset_1(B_90,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_44,c_400])).

tff(c_415,plain,(
    k4_subset_1('#skF_2','#skF_2','#skF_3') = k2_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_45,c_411])).

tff(c_420,plain,(
    k4_subset_1('#skF_2','#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_385,c_415])).

tff(c_460,plain,(
    ! [A_98,C_99,B_100] :
      ( k4_subset_1(A_98,C_99,B_100) = k4_subset_1(A_98,B_100,C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(A_98))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_497,plain,(
    ! [B_105] :
      ( k4_subset_1('#skF_2',B_105,'#skF_3') = k4_subset_1('#skF_2','#skF_3',B_105)
      | ~ m1_subset_1(B_105,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_44,c_460])).

tff(c_501,plain,(
    k4_subset_1('#skF_2','#skF_2','#skF_3') = k4_subset_1('#skF_2','#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_45,c_497])).

tff(c_506,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_438,c_420,c_501])).

tff(c_508,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_448,c_506])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:41:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.80  
% 3.17/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.80  %$ r2_hidden > r1_tarski > m1_subset_1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.17/1.80  
% 3.17/1.80  %Foreground sorts:
% 3.17/1.80  
% 3.17/1.80  
% 3.17/1.80  %Background operators:
% 3.17/1.80  
% 3.17/1.80  
% 3.17/1.80  %Foreground operators:
% 3.17/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.17/1.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.17/1.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.17/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.17/1.80  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.17/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.17/1.80  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.17/1.80  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.17/1.80  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.17/1.80  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.17/1.80  tff('#skF_2', type, '#skF_2': $i).
% 3.17/1.80  tff('#skF_3', type, '#skF_3': $i).
% 3.17/1.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.17/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.17/1.80  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.17/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.17/1.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.17/1.80  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.17/1.80  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.17/1.80  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.17/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.17/1.80  
% 3.31/1.83  tff(f_86, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 3.31/1.83  tff(f_66, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.31/1.83  tff(f_68, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.31/1.83  tff(f_81, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.31/1.83  tff(f_44, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.31/1.83  tff(f_52, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.31/1.83  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.31/1.83  tff(f_48, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.31/1.83  tff(f_42, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.31/1.83  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.31/1.83  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.31/1.83  tff(f_50, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.31/1.83  tff(f_64, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k4_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k4_subset_1)).
% 3.31/1.83  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.31/1.83  tff(c_34, plain, (![A_29]: (k2_subset_1(A_29)=A_29)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.31/1.83  tff(c_36, plain, (![A_30]: (m1_subset_1(k2_subset_1(A_30), k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.31/1.83  tff(c_45, plain, (![A_30]: (m1_subset_1(A_30, k1_zfmisc_1(A_30)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36])).
% 3.31/1.83  tff(c_400, plain, (![A_87, B_88, C_89]: (k4_subset_1(A_87, B_88, C_89)=k2_xboole_0(B_88, C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(A_87)) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.31/1.83  tff(c_431, plain, (![A_91, B_92]: (k4_subset_1(A_91, B_92, A_91)=k2_xboole_0(B_92, A_91) | ~m1_subset_1(B_92, k1_zfmisc_1(A_91)))), inference(resolution, [status(thm)], [c_45, c_400])).
% 3.31/1.83  tff(c_438, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')=k2_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_431])).
% 3.31/1.83  tff(c_42, plain, (k4_subset_1('#skF_2', '#skF_3', k2_subset_1('#skF_2'))!=k2_subset_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.31/1.83  tff(c_46, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_42])).
% 3.31/1.83  tff(c_448, plain, (k2_xboole_0('#skF_3', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_438, c_46])).
% 3.31/1.83  tff(c_18, plain, (![A_12]: (k2_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.31/1.83  tff(c_68, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k2_xboole_0(A_42, B_43))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.31/1.83  tff(c_75, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_68])).
% 3.31/1.83  tff(c_14, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.31/1.83  tff(c_118, plain, (![A_47, B_48]: (k3_xboole_0(A_47, B_48)=A_47 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.31/1.83  tff(c_122, plain, (![B_9]: (k3_xboole_0(B_9, B_9)=B_9)), inference(resolution, [status(thm)], [c_14, c_118])).
% 3.31/1.83  tff(c_209, plain, (![A_63, B_64]: (k5_xboole_0(A_63, k3_xboole_0(A_63, B_64))=k4_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.31/1.83  tff(c_218, plain, (![B_9]: (k5_xboole_0(B_9, B_9)=k4_xboole_0(B_9, B_9))), inference(superposition, [status(thm), theory('equality')], [c_122, c_209])).
% 3.31/1.83  tff(c_227, plain, (![B_9]: (k5_xboole_0(B_9, B_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_75, c_218])).
% 3.31/1.83  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.31/1.83  tff(c_323, plain, (![C_76, A_77, B_78]: (r2_hidden(C_76, A_77) | ~r2_hidden(C_76, B_78) | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.31/1.83  tff(c_339, plain, (![A_82, B_83, A_84]: (r2_hidden('#skF_1'(A_82, B_83), A_84) | ~m1_subset_1(A_82, k1_zfmisc_1(A_84)) | r1_tarski(A_82, B_83))), inference(resolution, [status(thm)], [c_8, c_323])).
% 3.31/1.83  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.31/1.83  tff(c_351, plain, (![A_85, A_86]: (~m1_subset_1(A_85, k1_zfmisc_1(A_86)) | r1_tarski(A_85, A_86))), inference(resolution, [status(thm)], [c_339, c_6])).
% 3.31/1.83  tff(c_360, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_351])).
% 3.31/1.83  tff(c_20, plain, (![A_13, B_14]: (k3_xboole_0(A_13, B_14)=A_13 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.31/1.83  tff(c_367, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_360, c_20])).
% 3.31/1.83  tff(c_16, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.31/1.83  tff(c_374, plain, (k5_xboole_0('#skF_3', '#skF_3')=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_367, c_16])).
% 3.31/1.83  tff(c_377, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_227, c_374])).
% 3.31/1.83  tff(c_22, plain, (![A_15, B_16]: (k2_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.31/1.83  tff(c_382, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_377, c_22])).
% 3.31/1.83  tff(c_385, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_382])).
% 3.31/1.83  tff(c_411, plain, (![B_90]: (k4_subset_1('#skF_2', B_90, '#skF_3')=k2_xboole_0(B_90, '#skF_3') | ~m1_subset_1(B_90, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_44, c_400])).
% 3.31/1.83  tff(c_415, plain, (k4_subset_1('#skF_2', '#skF_2', '#skF_3')=k2_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_45, c_411])).
% 3.31/1.83  tff(c_420, plain, (k4_subset_1('#skF_2', '#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_385, c_415])).
% 3.31/1.83  tff(c_460, plain, (![A_98, C_99, B_100]: (k4_subset_1(A_98, C_99, B_100)=k4_subset_1(A_98, B_100, C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(A_98)) | ~m1_subset_1(B_100, k1_zfmisc_1(A_98)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.31/1.83  tff(c_497, plain, (![B_105]: (k4_subset_1('#skF_2', B_105, '#skF_3')=k4_subset_1('#skF_2', '#skF_3', B_105) | ~m1_subset_1(B_105, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_44, c_460])).
% 3.31/1.83  tff(c_501, plain, (k4_subset_1('#skF_2', '#skF_2', '#skF_3')=k4_subset_1('#skF_2', '#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_45, c_497])).
% 3.31/1.83  tff(c_506, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_438, c_420, c_501])).
% 3.31/1.83  tff(c_508, plain, $false, inference(negUnitSimplification, [status(thm)], [c_448, c_506])).
% 3.31/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.83  
% 3.31/1.83  Inference rules
% 3.31/1.83  ----------------------
% 3.31/1.83  #Ref     : 0
% 3.31/1.83  #Sup     : 114
% 3.31/1.83  #Fact    : 0
% 3.31/1.83  #Define  : 0
% 3.31/1.83  #Split   : 1
% 3.31/1.83  #Chain   : 0
% 3.31/1.83  #Close   : 0
% 3.31/1.83  
% 3.31/1.83  Ordering : KBO
% 3.31/1.83  
% 3.31/1.83  Simplification rules
% 3.31/1.83  ----------------------
% 3.31/1.83  #Subsume      : 1
% 3.31/1.83  #Demod        : 44
% 3.31/1.83  #Tautology    : 78
% 3.31/1.83  #SimpNegUnit  : 1
% 3.31/1.83  #BackRed      : 1
% 3.31/1.83  
% 3.31/1.83  #Partial instantiations: 0
% 3.31/1.83  #Strategies tried      : 1
% 3.31/1.83  
% 3.31/1.83  Timing (in seconds)
% 3.31/1.83  ----------------------
% 3.31/1.83  Preprocessing        : 0.51
% 3.31/1.83  Parsing              : 0.27
% 3.31/1.83  CNF conversion       : 0.03
% 3.31/1.83  Main loop            : 0.44
% 3.31/1.83  Inferencing          : 0.16
% 3.31/1.83  Reduction            : 0.14
% 3.31/1.83  Demodulation         : 0.11
% 3.31/1.83  BG Simplification    : 0.03
% 3.31/1.84  Subsumption          : 0.09
% 3.31/1.84  Abstraction          : 0.03
% 3.31/1.84  MUC search           : 0.00
% 3.31/1.84  Cooper               : 0.00
% 3.31/1.84  Total                : 1.01
% 3.31/1.84  Index Insertion      : 0.00
% 3.31/1.84  Index Deletion       : 0.00
% 3.31/1.84  Index Matching       : 0.00
% 3.31/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
