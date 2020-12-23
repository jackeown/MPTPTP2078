%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:14 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 120 expanded)
%              Number of leaves         :   35 (  56 expanded)
%              Depth                    :    8
%              Number of atoms          :   77 ( 141 expanded)
%              Number of equality atoms :   49 ( 107 expanded)
%              Maximal formula depth    :   14 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_74,axiom,(
    ! [A,B,C,D,E] :
      ( E = k2_enumset1(A,B,C,D)
    <=> ! [F] :
          ( r2_hidden(F,E)
        <=> ~ ( F != A
              & F != B
              & F != C
              & F != D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(c_10,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_10,B_11] : k1_enumset1(A_10,A_10,B_11) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_576,plain,(
    ! [A_153,B_154,C_155] : k2_enumset1(A_153,A_153,B_154,C_155) = k1_enumset1(A_153,B_154,C_155) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_32,plain,(
    ! [F_31,A_24,B_25,C_26] : r2_hidden(F_31,k2_enumset1(A_24,B_25,C_26,F_31)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_597,plain,(
    ! [C_156,A_157,B_158] : r2_hidden(C_156,k1_enumset1(A_157,B_158,C_156)) ),
    inference(superposition,[status(thm),theory(equality)],[c_576,c_32])).

tff(c_601,plain,(
    ! [B_159,A_160] : r2_hidden(B_159,k2_tarski(A_160,B_159)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_597])).

tff(c_604,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_601])).

tff(c_252,plain,(
    ! [A_86,B_87,C_88] : k2_enumset1(A_86,A_86,B_87,C_88) = k1_enumset1(A_86,B_87,C_88) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_273,plain,(
    ! [C_89,A_90,B_91] : r2_hidden(C_89,k1_enumset1(A_90,B_91,C_89)) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_32])).

tff(c_277,plain,(
    ! [B_92,A_93] : r2_hidden(B_92,k2_tarski(A_93,B_92)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_273])).

tff(c_280,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_277])).

tff(c_68,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_91,plain,(
    ! [A_40,B_41] : k1_mcart_1(k4_tarski(A_40,B_41)) = A_40 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_100,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_91])).

tff(c_66,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | k1_mcart_1('#skF_3') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_134,plain,
    ( k2_mcart_1('#skF_3') = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_66])).

tff(c_135,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_137,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_68])).

tff(c_286,plain,(
    ! [A_98,B_99,C_100] : k2_zfmisc_1(k1_tarski(A_98),k2_tarski(B_99,C_100)) = k2_tarski(k4_tarski(A_98,B_99),k4_tarski(A_98,C_100)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_314,plain,(
    ! [A_98,C_100] : k2_zfmisc_1(k1_tarski(A_98),k2_tarski(C_100,C_100)) = k1_tarski(k4_tarski(A_98,C_100)) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_10])).

tff(c_425,plain,(
    ! [A_109,C_110] : k2_zfmisc_1(k1_tarski(A_109),k1_tarski(C_110)) = k1_tarski(k4_tarski(A_109,C_110)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_314])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_107,plain,(
    ! [A_42,B_43] : k2_xboole_0(k1_tarski(A_42),B_43) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_111,plain,(
    ! [A_42] : k1_tarski(A_42) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_107])).

tff(c_176,plain,(
    ! [A_62,B_63] :
      ( r1_tarski(k1_tarski(A_62),B_63)
      | ~ r2_hidden(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( ~ r1_tarski(A_17,k2_zfmisc_1(A_17,B_18))
      | k1_xboole_0 = A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_180,plain,(
    ! [A_62,B_18] :
      ( k1_tarski(A_62) = k1_xboole_0
      | ~ r2_hidden(A_62,k2_zfmisc_1(k1_tarski(A_62),B_18)) ) ),
    inference(resolution,[status(thm)],[c_176,c_22])).

tff(c_186,plain,(
    ! [A_62,B_18] : ~ r2_hidden(A_62,k2_zfmisc_1(k1_tarski(A_62),B_18)) ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_180])).

tff(c_452,plain,(
    ! [A_113,C_114] : ~ r2_hidden(A_113,k1_tarski(k4_tarski(A_113,C_114))) ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_186])).

tff(c_455,plain,(
    ~ r2_hidden('#skF_4',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_452])).

tff(c_458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_455])).

tff(c_459,plain,(
    k2_mcart_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_122,plain,(
    ! [A_46,B_47] : k2_mcart_1(k4_tarski(A_46,B_47)) = B_47 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_131,plain,(
    k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_122])).

tff(c_466,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_131])).

tff(c_471,plain,(
    k4_tarski('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_68])).

tff(c_606,plain,(
    ! [A_162,B_163,C_164] : k2_zfmisc_1(k1_tarski(A_162),k2_tarski(B_163,C_164)) = k2_tarski(k4_tarski(A_162,B_163),k4_tarski(A_162,C_164)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_634,plain,(
    ! [A_162,C_164] : k2_zfmisc_1(k1_tarski(A_162),k2_tarski(C_164,C_164)) = k1_tarski(k4_tarski(A_162,C_164)) ),
    inference(superposition,[status(thm),theory(equality)],[c_606,c_10])).

tff(c_677,plain,(
    ! [A_173,C_174] : k2_zfmisc_1(k1_tarski(A_173),k1_tarski(C_174)) = k1_tarski(k4_tarski(A_173,C_174)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_634])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(k1_tarski(A_15),B_16)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_514,plain,(
    ! [A_137,B_138] :
      ( ~ r1_tarski(A_137,k2_zfmisc_1(B_138,A_137))
      | k1_xboole_0 = A_137 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_518,plain,(
    ! [A_15,B_138] :
      ( k1_tarski(A_15) = k1_xboole_0
      | ~ r2_hidden(A_15,k2_zfmisc_1(B_138,k1_tarski(A_15))) ) ),
    inference(resolution,[status(thm)],[c_18,c_514])).

tff(c_521,plain,(
    ! [A_15,B_138] : ~ r2_hidden(A_15,k2_zfmisc_1(B_138,k1_tarski(A_15))) ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_518])).

tff(c_772,plain,(
    ! [C_178,A_179] : ~ r2_hidden(C_178,k1_tarski(k4_tarski(A_179,C_178))) ),
    inference(superposition,[status(thm),theory(equality)],[c_677,c_521])).

tff(c_775,plain,(
    ~ r2_hidden('#skF_3',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_471,c_772])).

tff(c_778,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_604,c_775])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:24:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.41  
% 2.77/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.41  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4
% 2.77/1.41  
% 2.77/1.41  %Foreground sorts:
% 2.77/1.41  
% 2.77/1.41  
% 2.77/1.41  %Background operators:
% 2.77/1.41  
% 2.77/1.41  
% 2.77/1.41  %Foreground operators:
% 2.77/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.77/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.77/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.77/1.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.77/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.77/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.77/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.77/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.77/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.77/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.77/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.77/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.77/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.77/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.41  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.77/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.77/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.77/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.41  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.77/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.77/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.77/1.41  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.77/1.41  
% 2.77/1.43  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.77/1.43  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.77/1.43  tff(f_39, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.77/1.43  tff(f_74, axiom, (![A, B, C, D, E]: ((E = k2_enumset1(A, B, C, D)) <=> (![F]: (r2_hidden(F, E) <=> ~(((~(F = A) & ~(F = B)) & ~(F = C)) & ~(F = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_enumset1)).
% 2.77/1.43  tff(f_90, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.77/1.43  tff(f_80, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.77/1.43  tff(f_53, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 2.77/1.43  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.77/1.43  tff(f_56, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.77/1.43  tff(f_43, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.77/1.43  tff(f_49, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 2.77/1.43  tff(c_10, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.77/1.43  tff(c_12, plain, (![A_10, B_11]: (k1_enumset1(A_10, A_10, B_11)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.77/1.43  tff(c_576, plain, (![A_153, B_154, C_155]: (k2_enumset1(A_153, A_153, B_154, C_155)=k1_enumset1(A_153, B_154, C_155))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.77/1.43  tff(c_32, plain, (![F_31, A_24, B_25, C_26]: (r2_hidden(F_31, k2_enumset1(A_24, B_25, C_26, F_31)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.77/1.43  tff(c_597, plain, (![C_156, A_157, B_158]: (r2_hidden(C_156, k1_enumset1(A_157, B_158, C_156)))), inference(superposition, [status(thm), theory('equality')], [c_576, c_32])).
% 2.77/1.43  tff(c_601, plain, (![B_159, A_160]: (r2_hidden(B_159, k2_tarski(A_160, B_159)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_597])).
% 2.77/1.43  tff(c_604, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_601])).
% 2.77/1.43  tff(c_252, plain, (![A_86, B_87, C_88]: (k2_enumset1(A_86, A_86, B_87, C_88)=k1_enumset1(A_86, B_87, C_88))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.77/1.43  tff(c_273, plain, (![C_89, A_90, B_91]: (r2_hidden(C_89, k1_enumset1(A_90, B_91, C_89)))), inference(superposition, [status(thm), theory('equality')], [c_252, c_32])).
% 2.77/1.43  tff(c_277, plain, (![B_92, A_93]: (r2_hidden(B_92, k2_tarski(A_93, B_92)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_273])).
% 2.77/1.43  tff(c_280, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_277])).
% 2.77/1.43  tff(c_68, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.77/1.43  tff(c_91, plain, (![A_40, B_41]: (k1_mcart_1(k4_tarski(A_40, B_41))=A_40)), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.77/1.43  tff(c_100, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_68, c_91])).
% 2.77/1.43  tff(c_66, plain, (k2_mcart_1('#skF_3')='#skF_3' | k1_mcart_1('#skF_3')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.77/1.43  tff(c_134, plain, (k2_mcart_1('#skF_3')='#skF_3' | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_66])).
% 2.77/1.43  tff(c_135, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_134])).
% 2.77/1.43  tff(c_137, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_135, c_68])).
% 2.77/1.43  tff(c_286, plain, (![A_98, B_99, C_100]: (k2_zfmisc_1(k1_tarski(A_98), k2_tarski(B_99, C_100))=k2_tarski(k4_tarski(A_98, B_99), k4_tarski(A_98, C_100)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.77/1.43  tff(c_314, plain, (![A_98, C_100]: (k2_zfmisc_1(k1_tarski(A_98), k2_tarski(C_100, C_100))=k1_tarski(k4_tarski(A_98, C_100)))), inference(superposition, [status(thm), theory('equality')], [c_286, c_10])).
% 2.77/1.43  tff(c_425, plain, (![A_109, C_110]: (k2_zfmisc_1(k1_tarski(A_109), k1_tarski(C_110))=k1_tarski(k4_tarski(A_109, C_110)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_314])).
% 2.77/1.43  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.77/1.43  tff(c_107, plain, (![A_42, B_43]: (k2_xboole_0(k1_tarski(A_42), B_43)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.77/1.43  tff(c_111, plain, (![A_42]: (k1_tarski(A_42)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_107])).
% 2.77/1.43  tff(c_176, plain, (![A_62, B_63]: (r1_tarski(k1_tarski(A_62), B_63) | ~r2_hidden(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.77/1.43  tff(c_22, plain, (![A_17, B_18]: (~r1_tarski(A_17, k2_zfmisc_1(A_17, B_18)) | k1_xboole_0=A_17)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.77/1.43  tff(c_180, plain, (![A_62, B_18]: (k1_tarski(A_62)=k1_xboole_0 | ~r2_hidden(A_62, k2_zfmisc_1(k1_tarski(A_62), B_18)))), inference(resolution, [status(thm)], [c_176, c_22])).
% 2.77/1.43  tff(c_186, plain, (![A_62, B_18]: (~r2_hidden(A_62, k2_zfmisc_1(k1_tarski(A_62), B_18)))), inference(negUnitSimplification, [status(thm)], [c_111, c_180])).
% 2.77/1.43  tff(c_452, plain, (![A_113, C_114]: (~r2_hidden(A_113, k1_tarski(k4_tarski(A_113, C_114))))), inference(superposition, [status(thm), theory('equality')], [c_425, c_186])).
% 2.77/1.43  tff(c_455, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_137, c_452])).
% 2.77/1.43  tff(c_458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_280, c_455])).
% 2.77/1.43  tff(c_459, plain, (k2_mcart_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_134])).
% 2.77/1.43  tff(c_122, plain, (![A_46, B_47]: (k2_mcart_1(k4_tarski(A_46, B_47))=B_47)), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.77/1.43  tff(c_131, plain, (k2_mcart_1('#skF_3')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_68, c_122])).
% 2.77/1.43  tff(c_466, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_459, c_131])).
% 2.77/1.43  tff(c_471, plain, (k4_tarski('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_466, c_68])).
% 2.77/1.43  tff(c_606, plain, (![A_162, B_163, C_164]: (k2_zfmisc_1(k1_tarski(A_162), k2_tarski(B_163, C_164))=k2_tarski(k4_tarski(A_162, B_163), k4_tarski(A_162, C_164)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.77/1.43  tff(c_634, plain, (![A_162, C_164]: (k2_zfmisc_1(k1_tarski(A_162), k2_tarski(C_164, C_164))=k1_tarski(k4_tarski(A_162, C_164)))), inference(superposition, [status(thm), theory('equality')], [c_606, c_10])).
% 2.77/1.43  tff(c_677, plain, (![A_173, C_174]: (k2_zfmisc_1(k1_tarski(A_173), k1_tarski(C_174))=k1_tarski(k4_tarski(A_173, C_174)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_634])).
% 2.77/1.43  tff(c_18, plain, (![A_15, B_16]: (r1_tarski(k1_tarski(A_15), B_16) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.77/1.43  tff(c_514, plain, (![A_137, B_138]: (~r1_tarski(A_137, k2_zfmisc_1(B_138, A_137)) | k1_xboole_0=A_137)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.77/1.43  tff(c_518, plain, (![A_15, B_138]: (k1_tarski(A_15)=k1_xboole_0 | ~r2_hidden(A_15, k2_zfmisc_1(B_138, k1_tarski(A_15))))), inference(resolution, [status(thm)], [c_18, c_514])).
% 2.77/1.43  tff(c_521, plain, (![A_15, B_138]: (~r2_hidden(A_15, k2_zfmisc_1(B_138, k1_tarski(A_15))))), inference(negUnitSimplification, [status(thm)], [c_111, c_518])).
% 2.77/1.43  tff(c_772, plain, (![C_178, A_179]: (~r2_hidden(C_178, k1_tarski(k4_tarski(A_179, C_178))))), inference(superposition, [status(thm), theory('equality')], [c_677, c_521])).
% 2.77/1.43  tff(c_775, plain, (~r2_hidden('#skF_3', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_471, c_772])).
% 2.77/1.43  tff(c_778, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_604, c_775])).
% 2.77/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.43  
% 2.77/1.43  Inference rules
% 2.77/1.43  ----------------------
% 2.77/1.43  #Ref     : 0
% 2.77/1.43  #Sup     : 176
% 2.77/1.43  #Fact    : 0
% 2.77/1.43  #Define  : 0
% 2.77/1.43  #Split   : 1
% 2.77/1.43  #Chain   : 0
% 2.77/1.43  #Close   : 0
% 2.77/1.43  
% 2.77/1.43  Ordering : KBO
% 2.77/1.43  
% 2.77/1.43  Simplification rules
% 2.77/1.43  ----------------------
% 2.77/1.43  #Subsume      : 0
% 2.77/1.43  #Demod        : 43
% 2.77/1.43  #Tautology    : 97
% 2.77/1.43  #SimpNegUnit  : 12
% 2.77/1.43  #BackRed      : 4
% 2.77/1.43  
% 2.77/1.43  #Partial instantiations: 0
% 2.77/1.43  #Strategies tried      : 1
% 2.77/1.43  
% 2.77/1.43  Timing (in seconds)
% 2.77/1.43  ----------------------
% 2.77/1.43  Preprocessing        : 0.33
% 2.77/1.43  Parsing              : 0.17
% 2.77/1.43  CNF conversion       : 0.02
% 2.77/1.43  Main loop            : 0.34
% 2.77/1.43  Inferencing          : 0.13
% 2.77/1.43  Reduction            : 0.11
% 2.77/1.43  Demodulation         : 0.08
% 2.77/1.43  BG Simplification    : 0.02
% 2.77/1.43  Subsumption          : 0.05
% 2.77/1.43  Abstraction          : 0.02
% 2.77/1.43  MUC search           : 0.00
% 2.77/1.43  Cooper               : 0.00
% 2.77/1.43  Total                : 0.70
% 2.77/1.43  Index Insertion      : 0.00
% 2.77/1.43  Index Deletion       : 0.00
% 2.77/1.43  Index Matching       : 0.00
% 2.77/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
