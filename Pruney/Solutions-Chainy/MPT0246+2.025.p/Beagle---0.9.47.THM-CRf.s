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
% DateTime   : Thu Dec  3 09:50:03 EST 2020

% Result     : Theorem 10.43s
% Output     : CNFRefutation 10.59s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 458 expanded)
%              Number of leaves         :   27 ( 165 expanded)
%              Depth                    :   17
%              Number of atoms          :  136 ( 966 expanded)
%              Number of equality atoms :   45 ( 324 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_103,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_tarski(B)
          & A != k1_xboole_0
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & C != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_61,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k4_xboole_0(B,A)
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

tff(c_54,plain,(
    k1_tarski('#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_65,plain,(
    ! [A_34] :
      ( r2_hidden('#skF_4'(A_34),A_34)
      | k1_xboole_0 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_50,plain,(
    ! [C_31] :
      ( C_31 = '#skF_6'
      | ~ r2_hidden(C_31,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_69,plain,
    ( '#skF_4'('#skF_5') = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_65,c_50])).

tff(c_72,plain,(
    '#skF_4'('#skF_5') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_69])).

tff(c_26,plain,(
    ! [A_12] :
      ( r2_hidden('#skF_4'(A_12),A_12)
      | k1_xboole_0 = A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_77,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_26])).

tff(c_80,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_77])).

tff(c_192,plain,(
    ! [D_63,A_64,B_65] :
      ( r2_hidden(D_63,A_64)
      | ~ r2_hidden(D_63,k4_xboole_0(A_64,B_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_207,plain,(
    ! [A_64,B_65] :
      ( r2_hidden('#skF_4'(k4_xboole_0(A_64,B_65)),A_64)
      | k4_xboole_0(A_64,B_65) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_192])).

tff(c_506,plain,(
    ! [A_104,B_105] :
      ( r2_hidden('#skF_4'(k4_xboole_0(A_104,B_105)),A_104)
      | k4_xboole_0(A_104,B_105) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_192])).

tff(c_171,plain,(
    ! [D_58,B_59,A_60] :
      ( ~ r2_hidden(D_58,B_59)
      | ~ r2_hidden(D_58,k4_xboole_0(A_60,B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_186,plain,(
    ! [A_60,B_59] :
      ( ~ r2_hidden('#skF_4'(k4_xboole_0(A_60,B_59)),B_59)
      | k4_xboole_0(A_60,B_59) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_171])).

tff(c_558,plain,(
    ! [A_106] : k4_xboole_0(A_106,A_106) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_506,c_186])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | k4_xboole_0(A_14,B_15) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_108,plain,(
    ! [A_47,B_48] :
      ( r2_hidden(A_47,B_48)
      | ~ r1_tarski(k1_tarski(A_47),B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_117,plain,(
    ! [A_47,B_15] :
      ( r2_hidden(A_47,B_15)
      | k4_xboole_0(k1_tarski(A_47),B_15) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_108])).

tff(c_618,plain,(
    ! [A_47] : r2_hidden(A_47,k1_tarski(A_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_117])).

tff(c_660,plain,(
    ! [A_108] : r2_hidden(A_108,k1_tarski(A_108)) ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_117])).

tff(c_94,plain,(
    ! [A_43,B_44] :
      ( r1_tarski(k1_tarski(A_43),B_44)
      | ~ r2_hidden(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_30,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = k1_xboole_0
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_98,plain,(
    ! [A_43,B_44] :
      ( k4_xboole_0(k1_tarski(A_43),B_44) = k1_xboole_0
      | ~ r2_hidden(A_43,B_44) ) ),
    inference(resolution,[status(thm)],[c_94,c_30])).

tff(c_118,plain,(
    ! [A_49,B_50] :
      ( r1_xboole_0(A_49,B_50)
      | k4_xboole_0(A_49,B_50) != A_49 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_48,plain,(
    ! [A_28,B_29] :
      ( ~ r2_hidden(A_28,B_29)
      | ~ r1_xboole_0(k1_tarski(A_28),B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_345,plain,(
    ! [A_80,B_81] :
      ( ~ r2_hidden(A_80,B_81)
      | k4_xboole_0(k1_tarski(A_80),B_81) != k1_tarski(A_80) ) ),
    inference(resolution,[status(thm)],[c_118,c_48])).

tff(c_352,plain,(
    ! [A_43,B_44] :
      ( ~ r2_hidden(A_43,B_44)
      | k1_tarski(A_43) != k1_xboole_0
      | ~ r2_hidden(A_43,B_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_345])).

tff(c_672,plain,(
    ! [A_108] :
      ( k1_tarski(A_108) != k1_xboole_0
      | ~ r2_hidden(A_108,k1_tarski(A_108)) ) ),
    inference(resolution,[status(thm)],[c_660,c_352])).

tff(c_682,plain,(
    ! [A_108] : k1_tarski(A_108) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_618,c_672])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_728,plain,(
    ! [D_112,A_113] :
      ( ~ r2_hidden(D_112,A_113)
      | ~ r2_hidden(D_112,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_558,c_4])).

tff(c_743,plain,(
    ! [A_47] : ~ r2_hidden(A_47,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_618,c_728])).

tff(c_368,plain,(
    ! [D_85,A_86,B_87] :
      ( r2_hidden(D_85,k4_xboole_0(A_86,B_87))
      | r2_hidden(D_85,B_87)
      | ~ r2_hidden(D_85,A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_387,plain,(
    ! [D_85,B_44,A_43] :
      ( r2_hidden(D_85,k1_xboole_0)
      | r2_hidden(D_85,B_44)
      | ~ r2_hidden(D_85,k1_tarski(A_43))
      | ~ r2_hidden(A_43,B_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_368])).

tff(c_21449,plain,(
    ! [D_458,B_459,A_460] :
      ( r2_hidden(D_458,B_459)
      | ~ r2_hidden(D_458,k1_tarski(A_460))
      | ~ r2_hidden(A_460,B_459) ) ),
    inference(negUnitSimplification,[status(thm)],[c_743,c_387])).

tff(c_21525,plain,(
    ! [A_460,B_459] :
      ( r2_hidden('#skF_4'(k1_tarski(A_460)),B_459)
      | ~ r2_hidden(A_460,B_459)
      | k1_tarski(A_460) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_21449])).

tff(c_21833,plain,(
    ! [A_467,B_468] :
      ( r2_hidden('#skF_4'(k1_tarski(A_467)),B_468)
      | ~ r2_hidden(A_467,B_468) ) ),
    inference(negUnitSimplification,[status(thm)],[c_682,c_21525])).

tff(c_21948,plain,(
    ! [A_469] :
      ( '#skF_4'(k1_tarski(A_469)) = '#skF_6'
      | ~ r2_hidden(A_469,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_21833,c_50])).

tff(c_21557,plain,(
    ! [A_460,B_459] :
      ( r2_hidden('#skF_4'(k1_tarski(A_460)),B_459)
      | ~ r2_hidden(A_460,B_459) ) ),
    inference(negUnitSimplification,[status(thm)],[c_682,c_21525])).

tff(c_25882,plain,(
    ! [B_519,A_520] :
      ( r2_hidden('#skF_6',B_519)
      | ~ r2_hidden(A_520,B_519)
      | ~ r2_hidden(A_520,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21948,c_21557])).

tff(c_27470,plain,(
    ! [A_541] :
      ( r2_hidden('#skF_6',A_541)
      | ~ r2_hidden('#skF_4'(A_541),'#skF_5')
      | k1_xboole_0 = A_541 ) ),
    inference(resolution,[status(thm)],[c_26,c_25882])).

tff(c_27697,plain,(
    ! [B_546] :
      ( r2_hidden('#skF_6',k4_xboole_0('#skF_5',B_546))
      | k4_xboole_0('#skF_5',B_546) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_207,c_27470])).

tff(c_21947,plain,(
    ! [A_467] :
      ( '#skF_4'(k1_tarski(A_467)) = '#skF_6'
      | ~ r2_hidden(A_467,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_21833,c_50])).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2176,plain,(
    ! [A_165,A_166,B_167] :
      ( ~ r2_hidden('#skF_3'(A_165,k4_xboole_0(A_166,B_167)),B_167)
      | r1_xboole_0(A_165,k4_xboole_0(A_166,B_167)) ) ),
    inference(resolution,[status(thm)],[c_22,c_171])).

tff(c_2225,plain,(
    ! [A_168,A_169] : r1_xboole_0(A_168,k4_xboole_0(A_169,A_168)) ),
    inference(resolution,[status(thm)],[c_24,c_2176])).

tff(c_2263,plain,(
    ! [A_28,A_169] : ~ r2_hidden(A_28,k4_xboole_0(A_169,k1_tarski(A_28))) ),
    inference(resolution,[status(thm)],[c_2225,c_48])).

tff(c_22235,plain,(
    ! [A_474,A_475] : ~ r2_hidden(A_474,k4_xboole_0(A_475,k1_tarski('#skF_4'(k1_tarski(A_474))))) ),
    inference(resolution,[status(thm)],[c_21833,c_2263])).

tff(c_22238,plain,(
    ! [A_467,A_475] :
      ( ~ r2_hidden(A_467,k4_xboole_0(A_475,k1_tarski('#skF_6')))
      | ~ r2_hidden(A_467,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21947,c_22235])).

tff(c_27705,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_27697,c_22238])).

tff(c_27851,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_27705])).

tff(c_209,plain,(
    ! [A_68,B_69] :
      ( k4_xboole_0(k1_tarski(A_68),B_69) = k1_xboole_0
      | ~ r2_hidden(A_68,B_69) ) ),
    inference(resolution,[status(thm)],[c_94,c_30])).

tff(c_32,plain,(
    ! [B_17,A_16] :
      ( B_17 = A_16
      | k4_xboole_0(B_17,A_16) != k4_xboole_0(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_221,plain,(
    ! [A_68,B_69] :
      ( k1_tarski(A_68) = B_69
      | k4_xboole_0(B_69,k1_tarski(A_68)) != k1_xboole_0
      | ~ r2_hidden(A_68,B_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_32])).

tff(c_28001,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | ~ r2_hidden('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_27851,c_221])).

tff(c_28338,plain,(
    k1_tarski('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_28001])).

tff(c_28340,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_28338])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:13:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.43/4.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.43/4.07  
% 10.43/4.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.43/4.07  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_6 > #skF_2
% 10.43/4.07  
% 10.43/4.07  %Foreground sorts:
% 10.43/4.07  
% 10.43/4.07  
% 10.43/4.07  %Background operators:
% 10.43/4.07  
% 10.43/4.07  
% 10.43/4.07  %Foreground operators:
% 10.43/4.07  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 10.43/4.07  tff('#skF_4', type, '#skF_4': $i > $i).
% 10.43/4.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.43/4.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.43/4.07  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.43/4.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.43/4.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.43/4.07  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 10.43/4.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.43/4.07  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.43/4.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.43/4.07  tff('#skF_5', type, '#skF_5': $i).
% 10.43/4.07  tff('#skF_6', type, '#skF_6': $i).
% 10.43/4.07  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.43/4.07  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.43/4.07  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.43/4.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.43/4.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.43/4.07  
% 10.59/4.09  tff(f_103, negated_conjecture, ~(![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 10.59/4.09  tff(f_61, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 10.59/4.09  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 10.59/4.09  tff(f_65, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 10.59/4.09  tff(f_83, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 10.59/4.09  tff(f_73, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 10.59/4.09  tff(f_88, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 10.59/4.09  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 10.59/4.09  tff(f_69, axiom, (![A, B]: ((k4_xboole_0(A, B) = k4_xboole_0(B, A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_xboole_1)).
% 10.59/4.09  tff(c_54, plain, (k1_tarski('#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.59/4.09  tff(c_52, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.59/4.09  tff(c_65, plain, (![A_34]: (r2_hidden('#skF_4'(A_34), A_34) | k1_xboole_0=A_34)), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.59/4.09  tff(c_50, plain, (![C_31]: (C_31='#skF_6' | ~r2_hidden(C_31, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 10.59/4.09  tff(c_69, plain, ('#skF_4'('#skF_5')='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_65, c_50])).
% 10.59/4.09  tff(c_72, plain, ('#skF_4'('#skF_5')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_52, c_69])).
% 10.59/4.09  tff(c_26, plain, (![A_12]: (r2_hidden('#skF_4'(A_12), A_12) | k1_xboole_0=A_12)), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.59/4.09  tff(c_77, plain, (r2_hidden('#skF_6', '#skF_5') | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_72, c_26])).
% 10.59/4.09  tff(c_80, plain, (r2_hidden('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_52, c_77])).
% 10.59/4.09  tff(c_192, plain, (![D_63, A_64, B_65]: (r2_hidden(D_63, A_64) | ~r2_hidden(D_63, k4_xboole_0(A_64, B_65)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.59/4.09  tff(c_207, plain, (![A_64, B_65]: (r2_hidden('#skF_4'(k4_xboole_0(A_64, B_65)), A_64) | k4_xboole_0(A_64, B_65)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_192])).
% 10.59/4.09  tff(c_506, plain, (![A_104, B_105]: (r2_hidden('#skF_4'(k4_xboole_0(A_104, B_105)), A_104) | k4_xboole_0(A_104, B_105)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_192])).
% 10.59/4.09  tff(c_171, plain, (![D_58, B_59, A_60]: (~r2_hidden(D_58, B_59) | ~r2_hidden(D_58, k4_xboole_0(A_60, B_59)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.59/4.09  tff(c_186, plain, (![A_60, B_59]: (~r2_hidden('#skF_4'(k4_xboole_0(A_60, B_59)), B_59) | k4_xboole_0(A_60, B_59)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_171])).
% 10.59/4.09  tff(c_558, plain, (![A_106]: (k4_xboole_0(A_106, A_106)=k1_xboole_0)), inference(resolution, [status(thm)], [c_506, c_186])).
% 10.59/4.09  tff(c_28, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | k4_xboole_0(A_14, B_15)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.59/4.09  tff(c_108, plain, (![A_47, B_48]: (r2_hidden(A_47, B_48) | ~r1_tarski(k1_tarski(A_47), B_48))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.59/4.09  tff(c_117, plain, (![A_47, B_15]: (r2_hidden(A_47, B_15) | k4_xboole_0(k1_tarski(A_47), B_15)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_108])).
% 10.59/4.09  tff(c_618, plain, (![A_47]: (r2_hidden(A_47, k1_tarski(A_47)))), inference(superposition, [status(thm), theory('equality')], [c_558, c_117])).
% 10.59/4.09  tff(c_660, plain, (![A_108]: (r2_hidden(A_108, k1_tarski(A_108)))), inference(superposition, [status(thm), theory('equality')], [c_558, c_117])).
% 10.59/4.09  tff(c_94, plain, (![A_43, B_44]: (r1_tarski(k1_tarski(A_43), B_44) | ~r2_hidden(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.59/4.09  tff(c_30, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=k1_xboole_0 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.59/4.09  tff(c_98, plain, (![A_43, B_44]: (k4_xboole_0(k1_tarski(A_43), B_44)=k1_xboole_0 | ~r2_hidden(A_43, B_44))), inference(resolution, [status(thm)], [c_94, c_30])).
% 10.59/4.09  tff(c_118, plain, (![A_49, B_50]: (r1_xboole_0(A_49, B_50) | k4_xboole_0(A_49, B_50)!=A_49)), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.59/4.09  tff(c_48, plain, (![A_28, B_29]: (~r2_hidden(A_28, B_29) | ~r1_xboole_0(k1_tarski(A_28), B_29))), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.59/4.09  tff(c_345, plain, (![A_80, B_81]: (~r2_hidden(A_80, B_81) | k4_xboole_0(k1_tarski(A_80), B_81)!=k1_tarski(A_80))), inference(resolution, [status(thm)], [c_118, c_48])).
% 10.59/4.09  tff(c_352, plain, (![A_43, B_44]: (~r2_hidden(A_43, B_44) | k1_tarski(A_43)!=k1_xboole_0 | ~r2_hidden(A_43, B_44))), inference(superposition, [status(thm), theory('equality')], [c_98, c_345])).
% 10.59/4.09  tff(c_672, plain, (![A_108]: (k1_tarski(A_108)!=k1_xboole_0 | ~r2_hidden(A_108, k1_tarski(A_108)))), inference(resolution, [status(thm)], [c_660, c_352])).
% 10.59/4.09  tff(c_682, plain, (![A_108]: (k1_tarski(A_108)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_618, c_672])).
% 10.59/4.09  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.59/4.09  tff(c_728, plain, (![D_112, A_113]: (~r2_hidden(D_112, A_113) | ~r2_hidden(D_112, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_558, c_4])).
% 10.59/4.09  tff(c_743, plain, (![A_47]: (~r2_hidden(A_47, k1_xboole_0))), inference(resolution, [status(thm)], [c_618, c_728])).
% 10.59/4.09  tff(c_368, plain, (![D_85, A_86, B_87]: (r2_hidden(D_85, k4_xboole_0(A_86, B_87)) | r2_hidden(D_85, B_87) | ~r2_hidden(D_85, A_86))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.59/4.09  tff(c_387, plain, (![D_85, B_44, A_43]: (r2_hidden(D_85, k1_xboole_0) | r2_hidden(D_85, B_44) | ~r2_hidden(D_85, k1_tarski(A_43)) | ~r2_hidden(A_43, B_44))), inference(superposition, [status(thm), theory('equality')], [c_98, c_368])).
% 10.59/4.09  tff(c_21449, plain, (![D_458, B_459, A_460]: (r2_hidden(D_458, B_459) | ~r2_hidden(D_458, k1_tarski(A_460)) | ~r2_hidden(A_460, B_459))), inference(negUnitSimplification, [status(thm)], [c_743, c_387])).
% 10.59/4.09  tff(c_21525, plain, (![A_460, B_459]: (r2_hidden('#skF_4'(k1_tarski(A_460)), B_459) | ~r2_hidden(A_460, B_459) | k1_tarski(A_460)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_21449])).
% 10.59/4.09  tff(c_21833, plain, (![A_467, B_468]: (r2_hidden('#skF_4'(k1_tarski(A_467)), B_468) | ~r2_hidden(A_467, B_468))), inference(negUnitSimplification, [status(thm)], [c_682, c_21525])).
% 10.59/4.09  tff(c_21948, plain, (![A_469]: ('#skF_4'(k1_tarski(A_469))='#skF_6' | ~r2_hidden(A_469, '#skF_5'))), inference(resolution, [status(thm)], [c_21833, c_50])).
% 10.59/4.09  tff(c_21557, plain, (![A_460, B_459]: (r2_hidden('#skF_4'(k1_tarski(A_460)), B_459) | ~r2_hidden(A_460, B_459))), inference(negUnitSimplification, [status(thm)], [c_682, c_21525])).
% 10.59/4.09  tff(c_25882, plain, (![B_519, A_520]: (r2_hidden('#skF_6', B_519) | ~r2_hidden(A_520, B_519) | ~r2_hidden(A_520, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_21948, c_21557])).
% 10.59/4.09  tff(c_27470, plain, (![A_541]: (r2_hidden('#skF_6', A_541) | ~r2_hidden('#skF_4'(A_541), '#skF_5') | k1_xboole_0=A_541)), inference(resolution, [status(thm)], [c_26, c_25882])).
% 10.59/4.09  tff(c_27697, plain, (![B_546]: (r2_hidden('#skF_6', k4_xboole_0('#skF_5', B_546)) | k4_xboole_0('#skF_5', B_546)=k1_xboole_0)), inference(resolution, [status(thm)], [c_207, c_27470])).
% 10.59/4.09  tff(c_21947, plain, (![A_467]: ('#skF_4'(k1_tarski(A_467))='#skF_6' | ~r2_hidden(A_467, '#skF_5'))), inference(resolution, [status(thm)], [c_21833, c_50])).
% 10.59/4.09  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.59/4.09  tff(c_22, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.59/4.09  tff(c_2176, plain, (![A_165, A_166, B_167]: (~r2_hidden('#skF_3'(A_165, k4_xboole_0(A_166, B_167)), B_167) | r1_xboole_0(A_165, k4_xboole_0(A_166, B_167)))), inference(resolution, [status(thm)], [c_22, c_171])).
% 10.59/4.09  tff(c_2225, plain, (![A_168, A_169]: (r1_xboole_0(A_168, k4_xboole_0(A_169, A_168)))), inference(resolution, [status(thm)], [c_24, c_2176])).
% 10.59/4.09  tff(c_2263, plain, (![A_28, A_169]: (~r2_hidden(A_28, k4_xboole_0(A_169, k1_tarski(A_28))))), inference(resolution, [status(thm)], [c_2225, c_48])).
% 10.59/4.09  tff(c_22235, plain, (![A_474, A_475]: (~r2_hidden(A_474, k4_xboole_0(A_475, k1_tarski('#skF_4'(k1_tarski(A_474))))))), inference(resolution, [status(thm)], [c_21833, c_2263])).
% 10.59/4.09  tff(c_22238, plain, (![A_467, A_475]: (~r2_hidden(A_467, k4_xboole_0(A_475, k1_tarski('#skF_6'))) | ~r2_hidden(A_467, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_21947, c_22235])).
% 10.59/4.09  tff(c_27705, plain, (~r2_hidden('#skF_6', '#skF_5') | k4_xboole_0('#skF_5', k1_tarski('#skF_6'))=k1_xboole_0), inference(resolution, [status(thm)], [c_27697, c_22238])).
% 10.59/4.09  tff(c_27851, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_80, c_27705])).
% 10.59/4.09  tff(c_209, plain, (![A_68, B_69]: (k4_xboole_0(k1_tarski(A_68), B_69)=k1_xboole_0 | ~r2_hidden(A_68, B_69))), inference(resolution, [status(thm)], [c_94, c_30])).
% 10.59/4.09  tff(c_32, plain, (![B_17, A_16]: (B_17=A_16 | k4_xboole_0(B_17, A_16)!=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.59/4.09  tff(c_221, plain, (![A_68, B_69]: (k1_tarski(A_68)=B_69 | k4_xboole_0(B_69, k1_tarski(A_68))!=k1_xboole_0 | ~r2_hidden(A_68, B_69))), inference(superposition, [status(thm), theory('equality')], [c_209, c_32])).
% 10.59/4.09  tff(c_28001, plain, (k1_tarski('#skF_6')='#skF_5' | ~r2_hidden('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_27851, c_221])).
% 10.59/4.09  tff(c_28338, plain, (k1_tarski('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_28001])).
% 10.59/4.09  tff(c_28340, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_28338])).
% 10.59/4.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.59/4.09  
% 10.59/4.09  Inference rules
% 10.59/4.09  ----------------------
% 10.59/4.09  #Ref     : 4
% 10.59/4.09  #Sup     : 7227
% 10.59/4.09  #Fact    : 0
% 10.59/4.09  #Define  : 0
% 10.59/4.09  #Split   : 1
% 10.59/4.09  #Chain   : 0
% 10.59/4.09  #Close   : 0
% 10.59/4.09  
% 10.59/4.09  Ordering : KBO
% 10.59/4.09  
% 10.59/4.09  Simplification rules
% 10.59/4.09  ----------------------
% 10.59/4.09  #Subsume      : 2558
% 10.59/4.09  #Demod        : 3493
% 10.59/4.09  #Tautology    : 2551
% 10.59/4.09  #SimpNegUnit  : 370
% 10.59/4.09  #BackRed      : 1
% 10.59/4.09  
% 10.59/4.09  #Partial instantiations: 0
% 10.59/4.09  #Strategies tried      : 1
% 10.59/4.09  
% 10.59/4.09  Timing (in seconds)
% 10.59/4.09  ----------------------
% 10.59/4.09  Preprocessing        : 0.32
% 10.59/4.09  Parsing              : 0.17
% 10.59/4.09  CNF conversion       : 0.02
% 10.59/4.09  Main loop            : 3.06
% 10.59/4.09  Inferencing          : 0.74
% 10.59/4.09  Reduction            : 1.12
% 10.59/4.09  Demodulation         : 0.82
% 10.59/4.09  BG Simplification    : 0.09
% 10.59/4.09  Subsumption          : 0.95
% 10.59/4.09  Abstraction          : 0.12
% 10.59/4.09  MUC search           : 0.00
% 10.59/4.09  Cooper               : 0.00
% 10.59/4.09  Total                : 3.41
% 10.59/4.09  Index Insertion      : 0.00
% 10.59/4.09  Index Deletion       : 0.00
% 10.59/4.09  Index Matching       : 0.00
% 10.59/4.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
