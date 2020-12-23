%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:38 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   66 (  70 expanded)
%              Number of leaves         :   35 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :   74 (  87 expanded)
%              Number of equality atoms :   19 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_xboole_0(k1_relat_1(A),k1_relat_1(B))
             => r1_xboole_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t214_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(A,C)
        & r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_xboole_1)).

tff(c_40,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_44,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_46,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_42,plain,(
    r1_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_36,plain,(
    ! [A_49] :
      ( r1_tarski(A_49,k2_zfmisc_1(k1_relat_1(A_49),k2_relat_1(A_49)))
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_223,plain,(
    ! [A_78,B_79,C_80,D_81] :
      ( ~ r1_xboole_0(A_78,B_79)
      | r1_xboole_0(k2_zfmisc_1(A_78,C_80),k2_zfmisc_1(B_79,D_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_12,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_xboole_0(A_9,C_11)
      | ~ r1_xboole_0(B_10,C_11)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_443,plain,(
    ! [C_115,D_116,B_118,A_117,A_114] :
      ( r1_xboole_0(A_117,k2_zfmisc_1(B_118,D_116))
      | ~ r1_tarski(A_117,k2_zfmisc_1(A_114,C_115))
      | ~ r1_xboole_0(A_114,B_118) ) ),
    inference(resolution,[status(thm)],[c_223,c_12])).

tff(c_456,plain,(
    ! [A_125,B_126,D_127] :
      ( r1_xboole_0(A_125,k2_zfmisc_1(B_126,D_127))
      | ~ r1_xboole_0(k1_relat_1(A_125),B_126)
      | ~ v1_relat_1(A_125) ) ),
    inference(resolution,[status(thm)],[c_36,c_443])).

tff(c_461,plain,(
    ! [D_127] :
      ( r1_xboole_0('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_2'),D_127))
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_42,c_456])).

tff(c_470,plain,(
    ! [D_128] : r1_xboole_0('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_2'),D_128)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_461])).

tff(c_14,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_101,plain,(
    ! [A_60,B_61] : k4_xboole_0(A_60,k4_xboole_0(A_60,B_61)) = k3_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_116,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_101])).

tff(c_119,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_116])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_141,plain,(
    ! [A_63,B_64] : k5_xboole_0(A_63,k3_xboole_0(A_63,B_64)) = k4_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_150,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_141])).

tff(c_156,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_150])).

tff(c_210,plain,(
    ! [A_77] :
      ( k3_xboole_0(A_77,k2_zfmisc_1(k1_relat_1(A_77),k2_relat_1(A_77))) = A_77
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_216,plain,(
    ! [A_77] :
      ( k4_xboole_0(A_77,k2_zfmisc_1(k1_relat_1(A_77),k2_relat_1(A_77))) = k5_xboole_0(A_77,A_77)
      | ~ v1_relat_1(A_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_4])).

tff(c_221,plain,(
    ! [A_77] :
      ( k4_xboole_0(A_77,k2_zfmisc_1(k1_relat_1(A_77),k2_relat_1(A_77))) = k1_xboole_0
      | ~ v1_relat_1(A_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_216])).

tff(c_278,plain,(
    ! [A_93,B_94,C_95] :
      ( ~ r1_xboole_0(A_93,k4_xboole_0(B_94,C_95))
      | ~ r1_xboole_0(A_93,C_95)
      | r1_xboole_0(A_93,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_281,plain,(
    ! [A_93,A_77] :
      ( ~ r1_xboole_0(A_93,k1_xboole_0)
      | ~ r1_xboole_0(A_93,k2_zfmisc_1(k1_relat_1(A_77),k2_relat_1(A_77)))
      | r1_xboole_0(A_93,A_77)
      | ~ v1_relat_1(A_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_221,c_278])).

tff(c_295,plain,(
    ! [A_93,A_77] :
      ( ~ r1_xboole_0(A_93,k2_zfmisc_1(k1_relat_1(A_77),k2_relat_1(A_77)))
      | r1_xboole_0(A_93,A_77)
      | ~ v1_relat_1(A_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_281])).

tff(c_474,plain,
    ( r1_xboole_0('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_470,c_295])).

tff(c_479,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_474])).

tff(c_481,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_479])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:54:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.83  
% 3.02/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.83  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.02/1.83  
% 3.02/1.83  %Foreground sorts:
% 3.02/1.83  
% 3.02/1.83  
% 3.02/1.83  %Background operators:
% 3.02/1.83  
% 3.02/1.83  
% 3.02/1.83  %Foreground operators:
% 3.02/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.83  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.02/1.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.02/1.83  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.02/1.83  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.02/1.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.02/1.83  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.02/1.83  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.02/1.83  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.02/1.83  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.02/1.83  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.02/1.83  tff('#skF_2', type, '#skF_2': $i).
% 3.02/1.83  tff('#skF_1', type, '#skF_1': $i).
% 3.02/1.83  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.02/1.83  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.02/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.02/1.83  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.02/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.83  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.02/1.83  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.02/1.83  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.02/1.83  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.02/1.83  
% 3.29/1.85  tff(f_89, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k1_relat_1(A), k1_relat_1(B)) => r1_xboole_0(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t214_relat_1)).
% 3.29/1.85  tff(f_75, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 3.29/1.85  tff(f_69, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 3.29/1.85  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.29/1.85  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.29/1.85  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.29/1.85  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.29/1.85  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.29/1.85  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.29/1.85  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.29/1.85  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 3.29/1.85  tff(f_51, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_xboole_1)).
% 3.29/1.85  tff(c_40, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.29/1.85  tff(c_44, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.29/1.85  tff(c_46, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.29/1.85  tff(c_42, plain, (r1_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.29/1.85  tff(c_36, plain, (![A_49]: (r1_tarski(A_49, k2_zfmisc_1(k1_relat_1(A_49), k2_relat_1(A_49))) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.29/1.85  tff(c_223, plain, (![A_78, B_79, C_80, D_81]: (~r1_xboole_0(A_78, B_79) | r1_xboole_0(k2_zfmisc_1(A_78, C_80), k2_zfmisc_1(B_79, D_81)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.29/1.85  tff(c_12, plain, (![A_9, C_11, B_10]: (r1_xboole_0(A_9, C_11) | ~r1_xboole_0(B_10, C_11) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.29/1.85  tff(c_443, plain, (![C_115, D_116, B_118, A_117, A_114]: (r1_xboole_0(A_117, k2_zfmisc_1(B_118, D_116)) | ~r1_tarski(A_117, k2_zfmisc_1(A_114, C_115)) | ~r1_xboole_0(A_114, B_118))), inference(resolution, [status(thm)], [c_223, c_12])).
% 3.29/1.85  tff(c_456, plain, (![A_125, B_126, D_127]: (r1_xboole_0(A_125, k2_zfmisc_1(B_126, D_127)) | ~r1_xboole_0(k1_relat_1(A_125), B_126) | ~v1_relat_1(A_125))), inference(resolution, [status(thm)], [c_36, c_443])).
% 3.29/1.85  tff(c_461, plain, (![D_127]: (r1_xboole_0('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_2'), D_127)) | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_42, c_456])).
% 3.29/1.85  tff(c_470, plain, (![D_128]: (r1_xboole_0('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_2'), D_128)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_461])).
% 3.29/1.85  tff(c_14, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.29/1.85  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.29/1.85  tff(c_8, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.29/1.85  tff(c_101, plain, (![A_60, B_61]: (k4_xboole_0(A_60, k4_xboole_0(A_60, B_61))=k3_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.29/1.85  tff(c_116, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_101])).
% 3.29/1.85  tff(c_119, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_116])).
% 3.29/1.85  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.29/1.85  tff(c_141, plain, (![A_63, B_64]: (k5_xboole_0(A_63, k3_xboole_0(A_63, B_64))=k4_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.29/1.85  tff(c_150, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_141])).
% 3.29/1.85  tff(c_156, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_119, c_150])).
% 3.29/1.85  tff(c_210, plain, (![A_77]: (k3_xboole_0(A_77, k2_zfmisc_1(k1_relat_1(A_77), k2_relat_1(A_77)))=A_77 | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.29/1.85  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.29/1.85  tff(c_216, plain, (![A_77]: (k4_xboole_0(A_77, k2_zfmisc_1(k1_relat_1(A_77), k2_relat_1(A_77)))=k5_xboole_0(A_77, A_77) | ~v1_relat_1(A_77))), inference(superposition, [status(thm), theory('equality')], [c_210, c_4])).
% 3.29/1.85  tff(c_221, plain, (![A_77]: (k4_xboole_0(A_77, k2_zfmisc_1(k1_relat_1(A_77), k2_relat_1(A_77)))=k1_xboole_0 | ~v1_relat_1(A_77))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_216])).
% 3.29/1.85  tff(c_278, plain, (![A_93, B_94, C_95]: (~r1_xboole_0(A_93, k4_xboole_0(B_94, C_95)) | ~r1_xboole_0(A_93, C_95) | r1_xboole_0(A_93, B_94))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.29/1.85  tff(c_281, plain, (![A_93, A_77]: (~r1_xboole_0(A_93, k1_xboole_0) | ~r1_xboole_0(A_93, k2_zfmisc_1(k1_relat_1(A_77), k2_relat_1(A_77))) | r1_xboole_0(A_93, A_77) | ~v1_relat_1(A_77))), inference(superposition, [status(thm), theory('equality')], [c_221, c_278])).
% 3.29/1.85  tff(c_295, plain, (![A_93, A_77]: (~r1_xboole_0(A_93, k2_zfmisc_1(k1_relat_1(A_77), k2_relat_1(A_77))) | r1_xboole_0(A_93, A_77) | ~v1_relat_1(A_77))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_281])).
% 3.29/1.85  tff(c_474, plain, (r1_xboole_0('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_470, c_295])).
% 3.29/1.85  tff(c_479, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_474])).
% 3.29/1.85  tff(c_481, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_479])).
% 3.29/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.85  
% 3.29/1.85  Inference rules
% 3.29/1.85  ----------------------
% 3.29/1.85  #Ref     : 0
% 3.29/1.85  #Sup     : 101
% 3.29/1.85  #Fact    : 0
% 3.29/1.85  #Define  : 0
% 3.29/1.85  #Split   : 0
% 3.29/1.85  #Chain   : 0
% 3.29/1.85  #Close   : 0
% 3.29/1.85  
% 3.29/1.85  Ordering : KBO
% 3.29/1.85  
% 3.29/1.85  Simplification rules
% 3.29/1.85  ----------------------
% 3.29/1.85  #Subsume      : 5
% 3.29/1.85  #Demod        : 44
% 3.29/1.85  #Tautology    : 59
% 3.29/1.85  #SimpNegUnit  : 1
% 3.29/1.85  #BackRed      : 0
% 3.29/1.85  
% 3.29/1.85  #Partial instantiations: 0
% 3.29/1.85  #Strategies tried      : 1
% 3.29/1.85  
% 3.29/1.85  Timing (in seconds)
% 3.29/1.85  ----------------------
% 3.29/1.86  Preprocessing        : 0.50
% 3.29/1.86  Parsing              : 0.26
% 3.29/1.86  CNF conversion       : 0.04
% 3.29/1.86  Main loop            : 0.42
% 3.29/1.86  Inferencing          : 0.17
% 3.29/1.86  Reduction            : 0.13
% 3.29/1.86  Demodulation         : 0.10
% 3.29/1.86  BG Simplification    : 0.03
% 3.29/1.86  Subsumption          : 0.07
% 3.29/1.86  Abstraction          : 0.03
% 3.29/1.86  MUC search           : 0.00
% 3.29/1.86  Cooper               : 0.00
% 3.29/1.86  Total                : 0.97
% 3.29/1.86  Index Insertion      : 0.00
% 3.29/1.86  Index Deletion       : 0.00
% 3.29/1.86  Index Matching       : 0.00
% 3.29/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
