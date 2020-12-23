%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:29 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 124 expanded)
%              Number of leaves         :   40 (  63 expanded)
%              Depth                    :    7
%              Number of atoms          :   86 ( 269 expanded)
%              Number of equality atoms :   52 (  93 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_68,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_70,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_66,axiom,(
    ! [A,B,C,D,E] :
      ( E = k2_enumset1(A,B,C,D)
    <=> ! [F] :
          ( r2_hidden(F,E)
        <=> ~ ( F != A
              & F != B
              & F != C
              & F != D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).

tff(c_60,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_68,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_66,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_64,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_62,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_351,plain,(
    ! [D_157,C_158,B_159,A_160] :
      ( r2_hidden(k1_funct_1(D_157,C_158),B_159)
      | k1_xboole_0 = B_159
      | ~ r2_hidden(C_158,A_160)
      | ~ m1_subset_1(D_157,k1_zfmisc_1(k2_zfmisc_1(A_160,B_159)))
      | ~ v1_funct_2(D_157,A_160,B_159)
      | ~ v1_funct_1(D_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_388,plain,(
    ! [D_161,B_162] :
      ( r2_hidden(k1_funct_1(D_161,'#skF_5'),B_162)
      | k1_xboole_0 = B_162
      | ~ m1_subset_1(D_161,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_162)))
      | ~ v1_funct_2(D_161,'#skF_3',B_162)
      | ~ v1_funct_1(D_161) ) ),
    inference(resolution,[status(thm)],[c_62,c_351])).

tff(c_391,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_388])).

tff(c_394,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_391])).

tff(c_395,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_394])).

tff(c_54,plain,(
    ! [A_42] : k1_setfam_1(k1_tarski(A_42)) = A_42 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_6,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_96,plain,(
    ! [A_52,B_53] : k1_setfam_1(k2_tarski(A_52,B_53)) = k3_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_105,plain,(
    ! [A_4] : k3_xboole_0(A_4,A_4) = k1_setfam_1(k1_tarski(A_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_96])).

tff(c_108,plain,(
    ! [A_4] : k3_xboole_0(A_4,A_4) = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_105])).

tff(c_132,plain,(
    ! [A_74,B_75] : k5_xboole_0(A_74,k3_xboole_0(A_74,B_75)) = k4_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_144,plain,(
    ! [A_76] : k5_xboole_0(A_76,A_76) = k4_xboole_0(A_76,A_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_132])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_151,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_4])).

tff(c_20,plain,(
    ! [B_33] : k4_xboole_0(k1_tarski(B_33),k1_tarski(B_33)) != k1_tarski(B_33) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_414,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_4')) != k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_395,c_20])).

tff(c_426,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_151,c_395,c_414])).

tff(c_427,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_394])).

tff(c_8,plain,(
    ! [A_5,B_6] : k1_enumset1(A_5,A_5,B_6) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9] : k2_enumset1(A_7,A_7,B_8,C_9) = k1_enumset1(A_7,B_8,C_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_245,plain,(
    ! [A_105,B_108,F_107,C_109,D_106] :
      ( F_107 = D_106
      | F_107 = C_109
      | F_107 = B_108
      | F_107 = A_105
      | ~ r2_hidden(F_107,k2_enumset1(A_105,B_108,C_109,D_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_269,plain,(
    ! [F_110,C_111,B_112,A_113] :
      ( F_110 = C_111
      | F_110 = B_112
      | F_110 = A_113
      | F_110 = A_113
      | ~ r2_hidden(F_110,k1_enumset1(A_113,B_112,C_111)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_245])).

tff(c_288,plain,(
    ! [F_114,B_115,A_116] :
      ( F_114 = B_115
      | F_114 = A_116
      | F_114 = A_116
      | F_114 = A_116
      | ~ r2_hidden(F_114,k2_tarski(A_116,B_115)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_269])).

tff(c_297,plain,(
    ! [F_114,A_4] :
      ( F_114 = A_4
      | F_114 = A_4
      | F_114 = A_4
      | F_114 = A_4
      | ~ r2_hidden(F_114,k1_tarski(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_288])).

tff(c_433,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_427,c_297])).

tff(c_438,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_60,c_60,c_60,c_433])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:41:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.39  
% 2.72/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.39  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_4
% 2.72/1.39  
% 2.72/1.39  %Foreground sorts:
% 2.72/1.39  
% 2.72/1.39  
% 2.72/1.39  %Background operators:
% 2.72/1.39  
% 2.72/1.39  
% 2.72/1.39  %Foreground operators:
% 2.72/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.72/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.72/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.72/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.72/1.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.72/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.72/1.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.72/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.72/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.72/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.72/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.72/1.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.72/1.39  tff('#skF_6', type, '#skF_6': $i).
% 2.72/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.72/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.72/1.39  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.72/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.72/1.39  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.72/1.39  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.72/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.72/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.72/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.72/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.72/1.39  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.72/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.72/1.39  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.72/1.39  
% 2.72/1.40  tff(f_93, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 2.72/1.40  tff(f_82, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.72/1.40  tff(f_68, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.72/1.40  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.72/1.40  tff(f_70, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.72/1.40  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.72/1.40  tff(f_29, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.72/1.40  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.72/1.40  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.72/1.40  tff(f_35, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.72/1.40  tff(f_66, axiom, (![A, B, C, D, E]: ((E = k2_enumset1(A, B, C, D)) <=> (![F]: (r2_hidden(F, E) <=> ~(((~(F = A) & ~(F = B)) & ~(F = C)) & ~(F = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_enumset1)).
% 2.72/1.40  tff(c_60, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.72/1.40  tff(c_68, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.72/1.40  tff(c_66, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.72/1.40  tff(c_64, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.72/1.40  tff(c_62, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.72/1.40  tff(c_351, plain, (![D_157, C_158, B_159, A_160]: (r2_hidden(k1_funct_1(D_157, C_158), B_159) | k1_xboole_0=B_159 | ~r2_hidden(C_158, A_160) | ~m1_subset_1(D_157, k1_zfmisc_1(k2_zfmisc_1(A_160, B_159))) | ~v1_funct_2(D_157, A_160, B_159) | ~v1_funct_1(D_157))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.72/1.40  tff(c_388, plain, (![D_161, B_162]: (r2_hidden(k1_funct_1(D_161, '#skF_5'), B_162) | k1_xboole_0=B_162 | ~m1_subset_1(D_161, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_162))) | ~v1_funct_2(D_161, '#skF_3', B_162) | ~v1_funct_1(D_161))), inference(resolution, [status(thm)], [c_62, c_351])).
% 2.72/1.40  tff(c_391, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_64, c_388])).
% 2.72/1.40  tff(c_394, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_391])).
% 2.72/1.40  tff(c_395, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_394])).
% 2.72/1.40  tff(c_54, plain, (![A_42]: (k1_setfam_1(k1_tarski(A_42))=A_42)), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.72/1.40  tff(c_6, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.72/1.40  tff(c_96, plain, (![A_52, B_53]: (k1_setfam_1(k2_tarski(A_52, B_53))=k3_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.72/1.40  tff(c_105, plain, (![A_4]: (k3_xboole_0(A_4, A_4)=k1_setfam_1(k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_96])).
% 2.72/1.40  tff(c_108, plain, (![A_4]: (k3_xboole_0(A_4, A_4)=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_105])).
% 2.72/1.40  tff(c_132, plain, (![A_74, B_75]: (k5_xboole_0(A_74, k3_xboole_0(A_74, B_75))=k4_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.72/1.40  tff(c_144, plain, (![A_76]: (k5_xboole_0(A_76, A_76)=k4_xboole_0(A_76, A_76))), inference(superposition, [status(thm), theory('equality')], [c_108, c_132])).
% 2.72/1.40  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.72/1.40  tff(c_151, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_144, c_4])).
% 2.72/1.40  tff(c_20, plain, (![B_33]: (k4_xboole_0(k1_tarski(B_33), k1_tarski(B_33))!=k1_tarski(B_33))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.72/1.40  tff(c_414, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_4'))!=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_395, c_20])).
% 2.72/1.40  tff(c_426, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_395, c_151, c_395, c_414])).
% 2.72/1.40  tff(c_427, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_394])).
% 2.72/1.40  tff(c_8, plain, (![A_5, B_6]: (k1_enumset1(A_5, A_5, B_6)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.72/1.40  tff(c_10, plain, (![A_7, B_8, C_9]: (k2_enumset1(A_7, A_7, B_8, C_9)=k1_enumset1(A_7, B_8, C_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.72/1.40  tff(c_245, plain, (![A_105, B_108, F_107, C_109, D_106]: (F_107=D_106 | F_107=C_109 | F_107=B_108 | F_107=A_105 | ~r2_hidden(F_107, k2_enumset1(A_105, B_108, C_109, D_106)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.72/1.40  tff(c_269, plain, (![F_110, C_111, B_112, A_113]: (F_110=C_111 | F_110=B_112 | F_110=A_113 | F_110=A_113 | ~r2_hidden(F_110, k1_enumset1(A_113, B_112, C_111)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_245])).
% 2.72/1.40  tff(c_288, plain, (![F_114, B_115, A_116]: (F_114=B_115 | F_114=A_116 | F_114=A_116 | F_114=A_116 | ~r2_hidden(F_114, k2_tarski(A_116, B_115)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_269])).
% 2.72/1.40  tff(c_297, plain, (![F_114, A_4]: (F_114=A_4 | F_114=A_4 | F_114=A_4 | F_114=A_4 | ~r2_hidden(F_114, k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_288])).
% 2.72/1.40  tff(c_433, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_427, c_297])).
% 2.72/1.40  tff(c_438, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_60, c_60, c_60, c_433])).
% 2.72/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.40  
% 2.72/1.40  Inference rules
% 2.72/1.40  ----------------------
% 2.72/1.40  #Ref     : 0
% 2.72/1.40  #Sup     : 85
% 2.72/1.40  #Fact    : 0
% 2.72/1.40  #Define  : 0
% 2.72/1.40  #Split   : 1
% 2.72/1.40  #Chain   : 0
% 2.72/1.40  #Close   : 0
% 2.72/1.40  
% 2.72/1.40  Ordering : KBO
% 2.72/1.40  
% 2.72/1.40  Simplification rules
% 2.72/1.40  ----------------------
% 2.72/1.40  #Subsume      : 0
% 2.72/1.40  #Demod        : 13
% 2.72/1.40  #Tautology    : 46
% 2.72/1.40  #SimpNegUnit  : 1
% 2.72/1.40  #BackRed      : 2
% 2.72/1.40  
% 2.72/1.40  #Partial instantiations: 0
% 2.72/1.40  #Strategies tried      : 1
% 2.72/1.40  
% 2.72/1.40  Timing (in seconds)
% 2.72/1.40  ----------------------
% 2.72/1.41  Preprocessing        : 0.35
% 2.72/1.41  Parsing              : 0.17
% 2.72/1.41  CNF conversion       : 0.02
% 2.72/1.41  Main loop            : 0.29
% 2.72/1.41  Inferencing          : 0.11
% 2.72/1.41  Reduction            : 0.09
% 2.72/1.41  Demodulation         : 0.06
% 2.72/1.41  BG Simplification    : 0.02
% 2.72/1.41  Subsumption          : 0.06
% 2.72/1.41  Abstraction          : 0.02
% 2.72/1.41  MUC search           : 0.00
% 2.72/1.41  Cooper               : 0.00
% 2.72/1.41  Total                : 0.67
% 2.72/1.41  Index Insertion      : 0.00
% 2.72/1.41  Index Deletion       : 0.00
% 2.72/1.41  Index Matching       : 0.00
% 2.72/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
