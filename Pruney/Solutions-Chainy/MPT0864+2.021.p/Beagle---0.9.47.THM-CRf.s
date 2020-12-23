%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:11 EST 2020

% Result     : Theorem 29.48s
% Output     : CNFRefutation 29.48s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 181 expanded)
%              Number of leaves         :   36 (  77 expanded)
%              Depth                    :    9
%              Number of atoms          :  128 ( 327 expanded)
%              Number of equality atoms :   71 ( 191 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_6 > #skF_10 > #skF_9 > #skF_4 > #skF_14 > #skF_13 > #skF_5 > #skF_7 > #skF_11 > #skF_3 > #skF_2 > #skF_8 > #skF_1 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_76,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_63,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_92,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_66,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(c_72,plain,(
    ! [A_56,B_57] : k1_mcart_1(k4_tarski(A_56,B_57)) = A_56 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_16,plain,(
    ! [D_11,A_6] : r2_hidden(D_11,k2_tarski(A_6,D_11)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_62,plain,(
    ! [A_49] : k2_zfmisc_1(A_49,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_156315,plain,(
    ! [E_179630,F_179631,A_179632,B_179633] :
      ( r2_hidden(k4_tarski(E_179630,F_179631),k2_zfmisc_1(A_179632,B_179633))
      | ~ r2_hidden(F_179631,B_179633)
      | ~ r2_hidden(E_179630,A_179632) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_242386,plain,(
    ! [E_292180,F_292181,A_292182] :
      ( r2_hidden(k4_tarski(E_292180,F_292181),k1_xboole_0)
      | ~ r2_hidden(F_292181,k1_xboole_0)
      | ~ r2_hidden(E_292180,A_292182) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_156315])).

tff(c_242510,plain,(
    ! [D_293083,F_293084] :
      ( r2_hidden(k4_tarski(D_293083,F_293084),k1_xboole_0)
      | ~ r2_hidden(F_293084,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_242386])).

tff(c_131745,plain,(
    ! [A_151157,B_151158,C_151159] :
      ( r2_hidden(k1_mcart_1(A_151157),B_151158)
      | ~ r2_hidden(A_151157,k2_zfmisc_1(B_151158,C_151159)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_131754,plain,(
    ! [A_151160,A_151161] :
      ( r2_hidden(k1_mcart_1(A_151160),A_151161)
      | ~ r2_hidden(A_151160,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_131745])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_131769,plain,(
    ! [A_151160,A_1] :
      ( k1_mcart_1(A_151160) = A_1
      | ~ r2_hidden(A_151160,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_131754,c_2])).

tff(c_242560,plain,(
    ! [D_293083,F_293084,A_1] :
      ( k1_mcart_1(k4_tarski(D_293083,F_293084)) = A_1
      | ~ r2_hidden(F_293084,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_242510,c_131769])).

tff(c_242638,plain,(
    ! [D_293083,A_1,F_293084] :
      ( D_293083 = A_1
      | ~ r2_hidden(F_293084,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_242560])).

tff(c_242772,plain,(
    ! [F_293084] : ~ r2_hidden(F_293084,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_242638])).

tff(c_74,plain,(
    ! [A_56,B_57] : k2_mcart_1(k4_tarski(A_56,B_57)) = B_57 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_64,plain,(
    ! [B_50] : k2_zfmisc_1(k1_xboole_0,B_50) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_18079,plain,(
    ! [E_21683,F_21684,A_21685,B_21686] :
      ( r2_hidden(k4_tarski(E_21683,F_21684),k2_zfmisc_1(A_21685,B_21686))
      | ~ r2_hidden(F_21684,B_21686)
      | ~ r2_hidden(E_21683,A_21685) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_116350,plain,(
    ! [E_141938,F_141939,B_141940] :
      ( r2_hidden(k4_tarski(E_141938,F_141939),k1_xboole_0)
      | ~ r2_hidden(F_141939,B_141940)
      | ~ r2_hidden(E_141938,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_18079])).

tff(c_116480,plain,(
    ! [E_142841,D_142842] :
      ( r2_hidden(k4_tarski(E_142841,D_142842),k1_xboole_0)
      | ~ r2_hidden(E_142841,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_116350])).

tff(c_230,plain,(
    ! [A_92,C_93,B_94] :
      ( r2_hidden(k2_mcart_1(A_92),C_93)
      | ~ r2_hidden(A_92,k2_zfmisc_1(B_94,C_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_256,plain,(
    ! [A_99,B_100] :
      ( r2_hidden(k2_mcart_1(A_99),B_100)
      | ~ r2_hidden(A_99,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_230])).

tff(c_275,plain,(
    ! [A_99,A_1] :
      ( k2_mcart_1(A_99) = A_1
      | ~ r2_hidden(A_99,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_256,c_2])).

tff(c_116530,plain,(
    ! [E_142841,D_142842,A_1] :
      ( k2_mcart_1(k4_tarski(E_142841,D_142842)) = A_1
      | ~ r2_hidden(E_142841,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_116480,c_275])).

tff(c_116608,plain,(
    ! [D_142842,A_1,E_142841] :
      ( D_142842 = A_1
      | ~ r2_hidden(E_142841,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_116530])).

tff(c_116742,plain,(
    ! [E_142841] : ~ r2_hidden(E_142841,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_116608])).

tff(c_84,plain,(
    k4_tarski('#skF_13','#skF_14') = '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_114,plain,(
    ! [A_77,B_78] : k1_mcart_1(k4_tarski(A_77,B_78)) = A_77 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_123,plain,(
    k1_mcart_1('#skF_12') = '#skF_13' ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_114])).

tff(c_82,plain,
    ( k2_mcart_1('#skF_12') = '#skF_12'
    | k1_mcart_1('#skF_12') = '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_147,plain,
    ( k2_mcart_1('#skF_12') = '#skF_12'
    | '#skF_13' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_82])).

tff(c_148,plain,(
    '#skF_13' = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_147])).

tff(c_150,plain,(
    k4_tarski('#skF_12','#skF_14') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_84])).

tff(c_76,plain,(
    ! [A_58] :
      ( r2_hidden('#skF_11'(A_58),A_58)
      | k1_xboole_0 = A_58 ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_185,plain,(
    ! [C_85,A_86] :
      ( C_85 = A_86
      | ~ r2_hidden(C_85,k1_tarski(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_193,plain,(
    ! [A_86] :
      ( '#skF_11'(k1_tarski(A_86)) = A_86
      | k1_tarski(A_86) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_76,c_185])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2636,plain,(
    ! [C_4222,A_4223,D_4224] :
      ( ~ r2_hidden(C_4222,A_4223)
      | k4_tarski(C_4222,D_4224) != '#skF_11'(A_4223)
      | k1_xboole_0 = A_4223 ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_36877,plain,(
    ! [C_61369,D_61370] :
      ( k4_tarski(C_61369,D_61370) != '#skF_11'(k1_tarski(C_61369))
      | k1_tarski(C_61369) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_2636])).

tff(c_118594,plain,(
    ! [A_144841,D_144842] :
      ( k4_tarski(A_144841,D_144842) != A_144841
      | k1_tarski(A_144841) = k1_xboole_0
      | k1_tarski(A_144841) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_36877])).

tff(c_118607,plain,(
    k1_tarski('#skF_12') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_118594])).

tff(c_118674,plain,(
    r2_hidden('#skF_12',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_118607,c_4])).

tff(c_118698,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116742,c_118674])).

tff(c_118701,plain,(
    ! [D_144843,A_144844] : D_144843 = A_144844 ),
    inference(splitRight,[status(thm)],[c_116608])).

tff(c_66,plain,(
    ! [A_51,B_52] : k2_xboole_0(k1_tarski(A_51),B_52) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_131087,plain,(
    ! [D_144843] : k1_xboole_0 != D_144843 ),
    inference(superposition,[status(thm),theory(equality)],[c_118701,c_66])).

tff(c_131661,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_131087])).

tff(c_131662,plain,(
    k2_mcart_1('#skF_12') = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_147])).

tff(c_131668,plain,(
    ! [A_151145,B_151146] : k2_mcart_1(k4_tarski(A_151145,B_151146)) = B_151146 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_131677,plain,(
    k2_mcart_1('#skF_12') = '#skF_14' ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_131668])).

tff(c_131680,plain,(
    '#skF_14' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131662,c_131677])).

tff(c_131682,plain,(
    k4_tarski('#skF_13','#skF_12') = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131680,c_84])).

tff(c_131700,plain,(
    ! [C_151150,A_151151] :
      ( C_151150 = A_151151
      | ~ r2_hidden(C_151150,k1_tarski(A_151151)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_131708,plain,(
    ! [A_151151] :
      ( '#skF_11'(k1_tarski(A_151151)) = A_151151
      | k1_tarski(A_151151) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_76,c_131700])).

tff(c_134173,plain,(
    ! [D_155504,A_155505,C_155506] :
      ( ~ r2_hidden(D_155504,A_155505)
      | k4_tarski(C_155506,D_155504) != '#skF_11'(A_155505)
      | k1_xboole_0 = A_155505 ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_168144,plain,(
    ! [C_213099,C_213100] :
      ( k4_tarski(C_213099,C_213100) != '#skF_11'(k1_tarski(C_213100))
      | k1_tarski(C_213100) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_134173])).

tff(c_244515,plain,(
    ! [C_295077,A_295078] :
      ( k4_tarski(C_295077,A_295078) != A_295078
      | k1_tarski(A_295078) = k1_xboole_0
      | k1_tarski(A_295078) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131708,c_168144])).

tff(c_244528,plain,(
    k1_tarski('#skF_12') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_131682,c_244515])).

tff(c_244595,plain,(
    r2_hidden('#skF_12',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_244528,c_4])).

tff(c_244619,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_242772,c_244595])).

tff(c_244755,plain,(
    ! [D_295982,A_295983] : D_295982 = A_295983 ),
    inference(splitRight,[status(thm)],[c_242638])).

tff(c_256037,plain,(
    ! [D_295982] : k1_xboole_0 != D_295982 ),
    inference(superposition,[status(thm),theory(equality)],[c_244755,c_66])).

tff(c_256615,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_256037])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n024.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 17:28:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 29.48/18.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 29.48/18.41  
% 29.48/18.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 29.48/18.41  %$ r2_hidden > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_6 > #skF_10 > #skF_9 > #skF_4 > #skF_14 > #skF_13 > #skF_5 > #skF_7 > #skF_11 > #skF_3 > #skF_2 > #skF_8 > #skF_1 > #skF_12
% 29.48/18.41  
% 29.48/18.41  %Foreground sorts:
% 29.48/18.41  
% 29.48/18.41  
% 29.48/18.41  %Background operators:
% 29.48/18.41  
% 29.48/18.41  
% 29.48/18.41  %Foreground operators:
% 29.48/18.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 29.48/18.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 29.48/18.41  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 29.48/18.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 29.48/18.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 29.48/18.41  tff('#skF_10', type, '#skF_10': ($i * $i * $i * $i) > $i).
% 29.48/18.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 29.48/18.41  tff('#skF_9', type, '#skF_9': ($i * $i * $i * $i) > $i).
% 29.48/18.41  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 29.48/18.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 29.48/18.41  tff('#skF_14', type, '#skF_14': $i).
% 29.48/18.41  tff('#skF_13', type, '#skF_13': $i).
% 29.48/18.41  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 29.48/18.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 29.48/18.41  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 29.48/18.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 29.48/18.41  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 29.48/18.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 29.48/18.41  tff('#skF_11', type, '#skF_11': $i > $i).
% 29.48/18.41  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 29.48/18.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 29.48/18.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 29.48/18.41  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 29.48/18.41  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 29.48/18.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 29.48/18.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 29.48/18.41  tff('#skF_12', type, '#skF_12': $i).
% 29.48/18.41  
% 29.48/18.43  tff(f_76, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 29.48/18.43  tff(f_41, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 29.48/18.43  tff(f_63, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 29.48/18.43  tff(f_57, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 29.48/18.43  tff(f_72, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 29.48/18.43  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 29.48/18.43  tff(f_102, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 29.48/18.43  tff(f_92, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 29.48/18.43  tff(f_66, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 29.48/18.43  tff(c_72, plain, (![A_56, B_57]: (k1_mcart_1(k4_tarski(A_56, B_57))=A_56)), inference(cnfTransformation, [status(thm)], [f_76])).
% 29.48/18.43  tff(c_16, plain, (![D_11, A_6]: (r2_hidden(D_11, k2_tarski(A_6, D_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 29.48/18.43  tff(c_62, plain, (![A_49]: (k2_zfmisc_1(A_49, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 29.48/18.43  tff(c_156315, plain, (![E_179630, F_179631, A_179632, B_179633]: (r2_hidden(k4_tarski(E_179630, F_179631), k2_zfmisc_1(A_179632, B_179633)) | ~r2_hidden(F_179631, B_179633) | ~r2_hidden(E_179630, A_179632))), inference(cnfTransformation, [status(thm)], [f_57])).
% 29.48/18.43  tff(c_242386, plain, (![E_292180, F_292181, A_292182]: (r2_hidden(k4_tarski(E_292180, F_292181), k1_xboole_0) | ~r2_hidden(F_292181, k1_xboole_0) | ~r2_hidden(E_292180, A_292182))), inference(superposition, [status(thm), theory('equality')], [c_62, c_156315])).
% 29.48/18.43  tff(c_242510, plain, (![D_293083, F_293084]: (r2_hidden(k4_tarski(D_293083, F_293084), k1_xboole_0) | ~r2_hidden(F_293084, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_242386])).
% 29.48/18.43  tff(c_131745, plain, (![A_151157, B_151158, C_151159]: (r2_hidden(k1_mcart_1(A_151157), B_151158) | ~r2_hidden(A_151157, k2_zfmisc_1(B_151158, C_151159)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 29.48/18.43  tff(c_131754, plain, (![A_151160, A_151161]: (r2_hidden(k1_mcart_1(A_151160), A_151161) | ~r2_hidden(A_151160, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_62, c_131745])).
% 29.48/18.43  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 29.48/18.43  tff(c_131769, plain, (![A_151160, A_1]: (k1_mcart_1(A_151160)=A_1 | ~r2_hidden(A_151160, k1_xboole_0))), inference(resolution, [status(thm)], [c_131754, c_2])).
% 29.48/18.43  tff(c_242560, plain, (![D_293083, F_293084, A_1]: (k1_mcart_1(k4_tarski(D_293083, F_293084))=A_1 | ~r2_hidden(F_293084, k1_xboole_0))), inference(resolution, [status(thm)], [c_242510, c_131769])).
% 29.48/18.43  tff(c_242638, plain, (![D_293083, A_1, F_293084]: (D_293083=A_1 | ~r2_hidden(F_293084, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_242560])).
% 29.48/18.43  tff(c_242772, plain, (![F_293084]: (~r2_hidden(F_293084, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_242638])).
% 29.48/18.43  tff(c_74, plain, (![A_56, B_57]: (k2_mcart_1(k4_tarski(A_56, B_57))=B_57)), inference(cnfTransformation, [status(thm)], [f_76])).
% 29.48/18.43  tff(c_64, plain, (![B_50]: (k2_zfmisc_1(k1_xboole_0, B_50)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 29.48/18.43  tff(c_18079, plain, (![E_21683, F_21684, A_21685, B_21686]: (r2_hidden(k4_tarski(E_21683, F_21684), k2_zfmisc_1(A_21685, B_21686)) | ~r2_hidden(F_21684, B_21686) | ~r2_hidden(E_21683, A_21685))), inference(cnfTransformation, [status(thm)], [f_57])).
% 29.48/18.43  tff(c_116350, plain, (![E_141938, F_141939, B_141940]: (r2_hidden(k4_tarski(E_141938, F_141939), k1_xboole_0) | ~r2_hidden(F_141939, B_141940) | ~r2_hidden(E_141938, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_64, c_18079])).
% 29.48/18.43  tff(c_116480, plain, (![E_142841, D_142842]: (r2_hidden(k4_tarski(E_142841, D_142842), k1_xboole_0) | ~r2_hidden(E_142841, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_116350])).
% 29.48/18.43  tff(c_230, plain, (![A_92, C_93, B_94]: (r2_hidden(k2_mcart_1(A_92), C_93) | ~r2_hidden(A_92, k2_zfmisc_1(B_94, C_93)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 29.48/18.43  tff(c_256, plain, (![A_99, B_100]: (r2_hidden(k2_mcart_1(A_99), B_100) | ~r2_hidden(A_99, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_64, c_230])).
% 29.48/18.43  tff(c_275, plain, (![A_99, A_1]: (k2_mcart_1(A_99)=A_1 | ~r2_hidden(A_99, k1_xboole_0))), inference(resolution, [status(thm)], [c_256, c_2])).
% 29.48/18.43  tff(c_116530, plain, (![E_142841, D_142842, A_1]: (k2_mcart_1(k4_tarski(E_142841, D_142842))=A_1 | ~r2_hidden(E_142841, k1_xboole_0))), inference(resolution, [status(thm)], [c_116480, c_275])).
% 29.48/18.43  tff(c_116608, plain, (![D_142842, A_1, E_142841]: (D_142842=A_1 | ~r2_hidden(E_142841, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_116530])).
% 29.48/18.43  tff(c_116742, plain, (![E_142841]: (~r2_hidden(E_142841, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_116608])).
% 29.48/18.43  tff(c_84, plain, (k4_tarski('#skF_13', '#skF_14')='#skF_12'), inference(cnfTransformation, [status(thm)], [f_102])).
% 29.48/18.43  tff(c_114, plain, (![A_77, B_78]: (k1_mcart_1(k4_tarski(A_77, B_78))=A_77)), inference(cnfTransformation, [status(thm)], [f_76])).
% 29.48/18.43  tff(c_123, plain, (k1_mcart_1('#skF_12')='#skF_13'), inference(superposition, [status(thm), theory('equality')], [c_84, c_114])).
% 29.48/18.43  tff(c_82, plain, (k2_mcart_1('#skF_12')='#skF_12' | k1_mcart_1('#skF_12')='#skF_12'), inference(cnfTransformation, [status(thm)], [f_102])).
% 29.48/18.43  tff(c_147, plain, (k2_mcart_1('#skF_12')='#skF_12' | '#skF_13'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_123, c_82])).
% 29.48/18.43  tff(c_148, plain, ('#skF_13'='#skF_12'), inference(splitLeft, [status(thm)], [c_147])).
% 29.48/18.43  tff(c_150, plain, (k4_tarski('#skF_12', '#skF_14')='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_148, c_84])).
% 29.48/18.43  tff(c_76, plain, (![A_58]: (r2_hidden('#skF_11'(A_58), A_58) | k1_xboole_0=A_58)), inference(cnfTransformation, [status(thm)], [f_92])).
% 29.48/18.43  tff(c_185, plain, (![C_85, A_86]: (C_85=A_86 | ~r2_hidden(C_85, k1_tarski(A_86)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 29.48/18.43  tff(c_193, plain, (![A_86]: ('#skF_11'(k1_tarski(A_86))=A_86 | k1_tarski(A_86)=k1_xboole_0)), inference(resolution, [status(thm)], [c_76, c_185])).
% 29.48/18.43  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 29.48/18.43  tff(c_2636, plain, (![C_4222, A_4223, D_4224]: (~r2_hidden(C_4222, A_4223) | k4_tarski(C_4222, D_4224)!='#skF_11'(A_4223) | k1_xboole_0=A_4223)), inference(cnfTransformation, [status(thm)], [f_92])).
% 29.48/18.43  tff(c_36877, plain, (![C_61369, D_61370]: (k4_tarski(C_61369, D_61370)!='#skF_11'(k1_tarski(C_61369)) | k1_tarski(C_61369)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_2636])).
% 29.48/18.43  tff(c_118594, plain, (![A_144841, D_144842]: (k4_tarski(A_144841, D_144842)!=A_144841 | k1_tarski(A_144841)=k1_xboole_0 | k1_tarski(A_144841)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_193, c_36877])).
% 29.48/18.43  tff(c_118607, plain, (k1_tarski('#skF_12')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_150, c_118594])).
% 29.48/18.43  tff(c_118674, plain, (r2_hidden('#skF_12', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_118607, c_4])).
% 29.48/18.43  tff(c_118698, plain, $false, inference(negUnitSimplification, [status(thm)], [c_116742, c_118674])).
% 29.48/18.43  tff(c_118701, plain, (![D_144843, A_144844]: (D_144843=A_144844)), inference(splitRight, [status(thm)], [c_116608])).
% 29.48/18.43  tff(c_66, plain, (![A_51, B_52]: (k2_xboole_0(k1_tarski(A_51), B_52)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_66])).
% 29.48/18.43  tff(c_131087, plain, (![D_144843]: (k1_xboole_0!=D_144843)), inference(superposition, [status(thm), theory('equality')], [c_118701, c_66])).
% 29.48/18.43  tff(c_131661, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_131087])).
% 29.48/18.43  tff(c_131662, plain, (k2_mcart_1('#skF_12')='#skF_12'), inference(splitRight, [status(thm)], [c_147])).
% 29.48/18.43  tff(c_131668, plain, (![A_151145, B_151146]: (k2_mcart_1(k4_tarski(A_151145, B_151146))=B_151146)), inference(cnfTransformation, [status(thm)], [f_76])).
% 29.48/18.43  tff(c_131677, plain, (k2_mcart_1('#skF_12')='#skF_14'), inference(superposition, [status(thm), theory('equality')], [c_84, c_131668])).
% 29.48/18.43  tff(c_131680, plain, ('#skF_14'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_131662, c_131677])).
% 29.48/18.43  tff(c_131682, plain, (k4_tarski('#skF_13', '#skF_12')='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_131680, c_84])).
% 29.48/18.43  tff(c_131700, plain, (![C_151150, A_151151]: (C_151150=A_151151 | ~r2_hidden(C_151150, k1_tarski(A_151151)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 29.48/18.43  tff(c_131708, plain, (![A_151151]: ('#skF_11'(k1_tarski(A_151151))=A_151151 | k1_tarski(A_151151)=k1_xboole_0)), inference(resolution, [status(thm)], [c_76, c_131700])).
% 29.48/18.43  tff(c_134173, plain, (![D_155504, A_155505, C_155506]: (~r2_hidden(D_155504, A_155505) | k4_tarski(C_155506, D_155504)!='#skF_11'(A_155505) | k1_xboole_0=A_155505)), inference(cnfTransformation, [status(thm)], [f_92])).
% 29.48/18.43  tff(c_168144, plain, (![C_213099, C_213100]: (k4_tarski(C_213099, C_213100)!='#skF_11'(k1_tarski(C_213100)) | k1_tarski(C_213100)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_134173])).
% 29.48/18.43  tff(c_244515, plain, (![C_295077, A_295078]: (k4_tarski(C_295077, A_295078)!=A_295078 | k1_tarski(A_295078)=k1_xboole_0 | k1_tarski(A_295078)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_131708, c_168144])).
% 29.48/18.43  tff(c_244528, plain, (k1_tarski('#skF_12')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_131682, c_244515])).
% 29.48/18.43  tff(c_244595, plain, (r2_hidden('#skF_12', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_244528, c_4])).
% 29.48/18.43  tff(c_244619, plain, $false, inference(negUnitSimplification, [status(thm)], [c_242772, c_244595])).
% 29.48/18.43  tff(c_244755, plain, (![D_295982, A_295983]: (D_295982=A_295983)), inference(splitRight, [status(thm)], [c_242638])).
% 29.48/18.43  tff(c_256037, plain, (![D_295982]: (k1_xboole_0!=D_295982)), inference(superposition, [status(thm), theory('equality')], [c_244755, c_66])).
% 29.48/18.43  tff(c_256615, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_256037])).
% 29.48/18.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 29.48/18.43  
% 29.48/18.43  Inference rules
% 29.48/18.43  ----------------------
% 29.48/18.43  #Ref     : 2
% 29.48/18.43  #Sup     : 52794
% 29.48/18.43  #Fact    : 4
% 29.48/18.43  #Define  : 0
% 29.48/18.43  #Split   : 41
% 29.48/18.43  #Chain   : 0
% 29.48/18.43  #Close   : 0
% 29.48/18.43  
% 29.48/18.43  Ordering : KBO
% 29.48/18.43  
% 29.48/18.43  Simplification rules
% 29.48/18.43  ----------------------
% 29.48/18.43  #Subsume      : 20683
% 29.48/18.43  #Demod        : 6180
% 29.48/18.43  #Tautology    : 256
% 29.48/18.43  #SimpNegUnit  : 135
% 29.48/18.43  #BackRed      : 3
% 29.48/18.43  
% 29.48/18.43  #Partial instantiations: 153847
% 29.48/18.43  #Strategies tried      : 1
% 29.48/18.43  
% 29.48/18.43  Timing (in seconds)
% 29.48/18.43  ----------------------
% 29.48/18.43  Preprocessing        : 0.39
% 29.48/18.43  Parsing              : 0.17
% 29.48/18.43  CNF conversion       : 0.04
% 29.48/18.43  Main loop            : 17.24
% 29.65/18.43  Inferencing          : 3.97
% 29.65/18.43  Reduction            : 3.77
% 29.65/18.43  Demodulation         : 2.73
% 29.65/18.43  BG Simplification    : 0.50
% 29.65/18.43  Subsumption          : 6.09
% 29.65/18.43  Abstraction          : 0.57
% 29.65/18.43  MUC search           : 0.00
% 29.65/18.43  Cooper               : 0.00
% 29.65/18.43  Total                : 17.67
% 29.65/18.43  Index Insertion      : 0.00
% 29.65/18.43  Index Deletion       : 0.00
% 29.65/18.43  Index Matching       : 0.00
% 29.65/18.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
