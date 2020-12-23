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
% DateTime   : Thu Dec  3 10:09:23 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 294 expanded)
%              Number of leaves         :   29 ( 104 expanded)
%              Depth                    :   11
%              Number of atoms          :  155 ( 708 expanded)
%              Number of equality atoms :   50 ( 204 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ! [C] :
                ( m1_subset_1(C,k2_zfmisc_1(A,B))
               => ( C != k1_mcart_1(C)
                  & C != k2_mcart_1(C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_mcart_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_91,axiom,(
    ! [A] :
      ( ? [B,C] : A = k4_tarski(B,C)
     => ( A != k1_mcart_1(A)
        & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_77,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_97,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_756,plain,(
    ! [B_187,A_188] :
      ( v1_xboole_0(B_187)
      | ~ m1_subset_1(B_187,A_188)
      | ~ v1_xboole_0(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_760,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_756])).

tff(c_766,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_760])).

tff(c_44,plain,(
    ! [A_32,B_33] : k2_mcart_1(k4_tarski(A_32,B_33)) = B_33 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_36,plain,(
    ! [B_28,C_29] : k2_mcart_1(k4_tarski(B_28,C_29)) != k4_tarski(B_28,C_29) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_54,plain,(
    ! [B_28,C_29] : k4_tarski(B_28,C_29) != C_29 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36])).

tff(c_32,plain,(
    ! [A_21,B_22] : v1_relat_1(k2_zfmisc_1(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_94,plain,(
    ! [B_53,A_54] :
      ( v1_xboole_0(B_53)
      | ~ m1_subset_1(B_53,A_54)
      | ~ v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_98,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_94])).

tff(c_100,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_42,plain,(
    ! [A_32,B_33] : k1_mcart_1(k4_tarski(A_32,B_33)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_38,plain,(
    ! [B_28,C_29] : k1_mcart_1(k4_tarski(B_28,C_29)) != k4_tarski(B_28,C_29) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_53,plain,(
    ! [B_28,C_29] : k4_tarski(B_28,C_29) != B_28 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38])).

tff(c_46,plain,
    ( k2_mcart_1('#skF_5') = '#skF_5'
    | k1_mcart_1('#skF_5') = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_69,plain,(
    k1_mcart_1('#skF_5') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_30,plain,(
    ! [A_19,B_20] :
      ( r2_hidden(A_19,B_20)
      | v1_xboole_0(B_20)
      | ~ m1_subset_1(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_254,plain,(
    ! [A_96,B_97] :
      ( k4_tarski(k1_mcart_1(A_96),k2_mcart_1(A_96)) = A_96
      | ~ r2_hidden(A_96,B_97)
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_345,plain,(
    ! [A_117,B_118] :
      ( k4_tarski(k1_mcart_1(A_117),k2_mcart_1(A_117)) = A_117
      | ~ v1_relat_1(B_118)
      | v1_xboole_0(B_118)
      | ~ m1_subset_1(A_117,B_118) ) ),
    inference(resolution,[status(thm)],[c_30,c_254])).

tff(c_355,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4'))
    | v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_345])).

tff(c_362,plain,
    ( k4_tarski('#skF_5',k2_mcart_1('#skF_5')) = '#skF_5'
    | v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_69,c_355])).

tff(c_364,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_53,c_362])).

tff(c_365,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_373,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_365,c_12])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_375,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_50])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_376,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_52])).

tff(c_366,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( ~ v1_xboole_0(B_12)
      | B_12 = A_11
      | ~ v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_384,plain,(
    ! [A_119] :
      ( A_119 = '#skF_5'
      | ~ v1_xboole_0(A_119) ) ),
    inference(resolution,[status(thm)],[c_365,c_14])).

tff(c_391,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_366,c_384])).

tff(c_599,plain,(
    ! [A_166,B_167,C_168,D_169] :
      ( r2_hidden(k4_tarski(A_166,B_167),k2_zfmisc_1(C_168,D_169))
      | ~ r2_hidden(B_167,D_169)
      | ~ r2_hidden(A_166,C_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_631,plain,(
    ! [C_170,D_171,B_172,A_173] :
      ( ~ v1_xboole_0(k2_zfmisc_1(C_170,D_171))
      | ~ r2_hidden(B_172,D_171)
      | ~ r2_hidden(A_173,C_170) ) ),
    inference(resolution,[status(thm)],[c_599,c_2])).

tff(c_633,plain,(
    ! [B_172,A_173] :
      ( ~ v1_xboole_0('#skF_5')
      | ~ r2_hidden(B_172,'#skF_4')
      | ~ r2_hidden(A_173,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_391,c_631])).

tff(c_635,plain,(
    ! [B_172,A_173] :
      ( ~ r2_hidden(B_172,'#skF_4')
      | ~ r2_hidden(A_173,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_633])).

tff(c_638,plain,(
    ! [A_174] : ~ r2_hidden(A_174,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_635])).

tff(c_658,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_638])).

tff(c_372,plain,(
    ! [A_11] :
      ( A_11 = '#skF_5'
      | ~ v1_xboole_0(A_11) ) ),
    inference(resolution,[status(thm)],[c_365,c_14])).

tff(c_661,plain,(
    '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_658,c_372])).

tff(c_667,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_376,c_661])).

tff(c_670,plain,(
    ! [B_175] : ~ r2_hidden(B_175,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_635])).

tff(c_690,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_670])).

tff(c_722,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_690,c_372])).

tff(c_728,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_375,c_722])).

tff(c_729,plain,(
    k2_mcart_1('#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_903,plain,(
    ! [A_227,B_228] :
      ( k4_tarski(k1_mcart_1(A_227),k2_mcart_1(A_227)) = A_227
      | ~ r2_hidden(A_227,B_228)
      | ~ v1_relat_1(B_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1029,plain,(
    ! [A_260,B_261] :
      ( k4_tarski(k1_mcart_1(A_260),k2_mcart_1(A_260)) = A_260
      | ~ v1_relat_1(B_261)
      | v1_xboole_0(B_261)
      | ~ m1_subset_1(A_260,B_261) ) ),
    inference(resolution,[status(thm)],[c_30,c_903])).

tff(c_1039,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4'))
    | v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_1029])).

tff(c_1046,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),'#skF_5') = '#skF_5'
    | v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_729,c_1039])).

tff(c_1048,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_766,c_54,c_1046])).

tff(c_1049,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_760])).

tff(c_1057,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1049,c_12])).

tff(c_1059,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1057,c_50])).

tff(c_1060,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1057,c_52])).

tff(c_1050,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_760])).

tff(c_1068,plain,(
    ! [A_262] :
      ( A_262 = '#skF_5'
      | ~ v1_xboole_0(A_262) ) ),
    inference(resolution,[status(thm)],[c_1049,c_14])).

tff(c_1075,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1050,c_1068])).

tff(c_1278,plain,(
    ! [A_307,B_308,C_309,D_310] :
      ( r2_hidden(k4_tarski(A_307,B_308),k2_zfmisc_1(C_309,D_310))
      | ~ r2_hidden(B_308,D_310)
      | ~ r2_hidden(A_307,C_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1310,plain,(
    ! [C_311,D_312,B_313,A_314] :
      ( ~ v1_xboole_0(k2_zfmisc_1(C_311,D_312))
      | ~ r2_hidden(B_313,D_312)
      | ~ r2_hidden(A_314,C_311) ) ),
    inference(resolution,[status(thm)],[c_1278,c_2])).

tff(c_1312,plain,(
    ! [B_313,A_314] :
      ( ~ v1_xboole_0('#skF_5')
      | ~ r2_hidden(B_313,'#skF_4')
      | ~ r2_hidden(A_314,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1075,c_1310])).

tff(c_1314,plain,(
    ! [B_313,A_314] :
      ( ~ r2_hidden(B_313,'#skF_4')
      | ~ r2_hidden(A_314,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1049,c_1312])).

tff(c_1317,plain,(
    ! [A_315] : ~ r2_hidden(A_315,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1314])).

tff(c_1337,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_1317])).

tff(c_1056,plain,(
    ! [A_11] :
      ( A_11 = '#skF_5'
      | ~ v1_xboole_0(A_11) ) ),
    inference(resolution,[status(thm)],[c_1049,c_14])).

tff(c_1340,plain,(
    '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1337,c_1056])).

tff(c_1346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1060,c_1340])).

tff(c_1349,plain,(
    ! [B_316] : ~ r2_hidden(B_316,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1314])).

tff(c_1369,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_1349])).

tff(c_1379,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1369,c_1056])).

tff(c_1385,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1059,c_1379])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:42:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.55  
% 3.27/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.27/1.55  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 3.27/1.55  
% 3.27/1.55  %Foreground sorts:
% 3.27/1.55  
% 3.27/1.55  
% 3.27/1.55  %Background operators:
% 3.27/1.55  
% 3.27/1.55  
% 3.27/1.55  %Foreground operators:
% 3.27/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.27/1.55  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.27/1.55  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.27/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.27/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.27/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.27/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.27/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.55  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.27/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.27/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.27/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.27/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.55  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.27/1.55  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.27/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.27/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.27/1.56  
% 3.50/1.57  tff(f_119, negated_conjecture, ~(![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (~(C = k1_mcart_1(C)) & ~(C = k2_mcart_1(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_mcart_1)).
% 3.50/1.57  tff(f_69, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.50/1.57  tff(f_101, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.50/1.57  tff(f_91, axiom, (![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 3.50/1.57  tff(f_77, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.50/1.57  tff(f_75, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.50/1.57  tff(f_97, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 3.50/1.57  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.50/1.57  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.50/1.57  tff(f_50, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 3.50/1.57  tff(f_56, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.50/1.57  tff(c_48, plain, (m1_subset_1('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.50/1.57  tff(c_756, plain, (![B_187, A_188]: (v1_xboole_0(B_187) | ~m1_subset_1(B_187, A_188) | ~v1_xboole_0(A_188))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.50/1.57  tff(c_760, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_756])).
% 3.50/1.57  tff(c_766, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_760])).
% 3.50/1.57  tff(c_44, plain, (![A_32, B_33]: (k2_mcart_1(k4_tarski(A_32, B_33))=B_33)), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.50/1.57  tff(c_36, plain, (![B_28, C_29]: (k2_mcart_1(k4_tarski(B_28, C_29))!=k4_tarski(B_28, C_29))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.50/1.57  tff(c_54, plain, (![B_28, C_29]: (k4_tarski(B_28, C_29)!=C_29)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36])).
% 3.50/1.57  tff(c_32, plain, (![A_21, B_22]: (v1_relat_1(k2_zfmisc_1(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.50/1.57  tff(c_94, plain, (![B_53, A_54]: (v1_xboole_0(B_53) | ~m1_subset_1(B_53, A_54) | ~v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.50/1.57  tff(c_98, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_94])).
% 3.50/1.57  tff(c_100, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_98])).
% 3.50/1.57  tff(c_42, plain, (![A_32, B_33]: (k1_mcart_1(k4_tarski(A_32, B_33))=A_32)), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.50/1.57  tff(c_38, plain, (![B_28, C_29]: (k1_mcart_1(k4_tarski(B_28, C_29))!=k4_tarski(B_28, C_29))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.50/1.57  tff(c_53, plain, (![B_28, C_29]: (k4_tarski(B_28, C_29)!=B_28)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38])).
% 3.50/1.57  tff(c_46, plain, (k2_mcart_1('#skF_5')='#skF_5' | k1_mcart_1('#skF_5')='#skF_5'), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.50/1.57  tff(c_69, plain, (k1_mcart_1('#skF_5')='#skF_5'), inference(splitLeft, [status(thm)], [c_46])).
% 3.50/1.57  tff(c_30, plain, (![A_19, B_20]: (r2_hidden(A_19, B_20) | v1_xboole_0(B_20) | ~m1_subset_1(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.50/1.57  tff(c_254, plain, (![A_96, B_97]: (k4_tarski(k1_mcart_1(A_96), k2_mcart_1(A_96))=A_96 | ~r2_hidden(A_96, B_97) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.50/1.57  tff(c_345, plain, (![A_117, B_118]: (k4_tarski(k1_mcart_1(A_117), k2_mcart_1(A_117))=A_117 | ~v1_relat_1(B_118) | v1_xboole_0(B_118) | ~m1_subset_1(A_117, B_118))), inference(resolution, [status(thm)], [c_30, c_254])).
% 3.50/1.57  tff(c_355, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4')) | v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_345])).
% 3.50/1.57  tff(c_362, plain, (k4_tarski('#skF_5', k2_mcart_1('#skF_5'))='#skF_5' | v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_69, c_355])).
% 3.50/1.57  tff(c_364, plain, $false, inference(negUnitSimplification, [status(thm)], [c_100, c_53, c_362])).
% 3.50/1.57  tff(c_365, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_98])).
% 3.50/1.57  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.50/1.57  tff(c_373, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_365, c_12])).
% 3.50/1.57  tff(c_50, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.50/1.57  tff(c_375, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_373, c_50])).
% 3.50/1.57  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.50/1.57  tff(c_52, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.50/1.57  tff(c_376, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_373, c_52])).
% 3.50/1.57  tff(c_366, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_98])).
% 3.50/1.57  tff(c_14, plain, (![B_12, A_11]: (~v1_xboole_0(B_12) | B_12=A_11 | ~v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.50/1.57  tff(c_384, plain, (![A_119]: (A_119='#skF_5' | ~v1_xboole_0(A_119))), inference(resolution, [status(thm)], [c_365, c_14])).
% 3.50/1.57  tff(c_391, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_366, c_384])).
% 3.50/1.57  tff(c_599, plain, (![A_166, B_167, C_168, D_169]: (r2_hidden(k4_tarski(A_166, B_167), k2_zfmisc_1(C_168, D_169)) | ~r2_hidden(B_167, D_169) | ~r2_hidden(A_166, C_168))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.50/1.57  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.50/1.57  tff(c_631, plain, (![C_170, D_171, B_172, A_173]: (~v1_xboole_0(k2_zfmisc_1(C_170, D_171)) | ~r2_hidden(B_172, D_171) | ~r2_hidden(A_173, C_170))), inference(resolution, [status(thm)], [c_599, c_2])).
% 3.50/1.57  tff(c_633, plain, (![B_172, A_173]: (~v1_xboole_0('#skF_5') | ~r2_hidden(B_172, '#skF_4') | ~r2_hidden(A_173, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_391, c_631])).
% 3.50/1.57  tff(c_635, plain, (![B_172, A_173]: (~r2_hidden(B_172, '#skF_4') | ~r2_hidden(A_173, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_365, c_633])).
% 3.50/1.57  tff(c_638, plain, (![A_174]: (~r2_hidden(A_174, '#skF_3'))), inference(splitLeft, [status(thm)], [c_635])).
% 3.50/1.57  tff(c_658, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_4, c_638])).
% 3.50/1.57  tff(c_372, plain, (![A_11]: (A_11='#skF_5' | ~v1_xboole_0(A_11))), inference(resolution, [status(thm)], [c_365, c_14])).
% 3.50/1.57  tff(c_661, plain, ('#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_658, c_372])).
% 3.50/1.57  tff(c_667, plain, $false, inference(negUnitSimplification, [status(thm)], [c_376, c_661])).
% 3.50/1.57  tff(c_670, plain, (![B_175]: (~r2_hidden(B_175, '#skF_4'))), inference(splitRight, [status(thm)], [c_635])).
% 3.50/1.57  tff(c_690, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_670])).
% 3.50/1.57  tff(c_722, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_690, c_372])).
% 3.50/1.57  tff(c_728, plain, $false, inference(negUnitSimplification, [status(thm)], [c_375, c_722])).
% 3.50/1.57  tff(c_729, plain, (k2_mcart_1('#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_46])).
% 3.50/1.57  tff(c_903, plain, (![A_227, B_228]: (k4_tarski(k1_mcart_1(A_227), k2_mcart_1(A_227))=A_227 | ~r2_hidden(A_227, B_228) | ~v1_relat_1(B_228))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.50/1.57  tff(c_1029, plain, (![A_260, B_261]: (k4_tarski(k1_mcart_1(A_260), k2_mcart_1(A_260))=A_260 | ~v1_relat_1(B_261) | v1_xboole_0(B_261) | ~m1_subset_1(A_260, B_261))), inference(resolution, [status(thm)], [c_30, c_903])).
% 3.50/1.57  tff(c_1039, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4')) | v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_48, c_1029])).
% 3.50/1.57  tff(c_1046, plain, (k4_tarski(k1_mcart_1('#skF_5'), '#skF_5')='#skF_5' | v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_729, c_1039])).
% 3.50/1.57  tff(c_1048, plain, $false, inference(negUnitSimplification, [status(thm)], [c_766, c_54, c_1046])).
% 3.50/1.57  tff(c_1049, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_760])).
% 3.50/1.57  tff(c_1057, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1049, c_12])).
% 3.50/1.57  tff(c_1059, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1057, c_50])).
% 3.50/1.57  tff(c_1060, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1057, c_52])).
% 3.50/1.57  tff(c_1050, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_760])).
% 3.50/1.57  tff(c_1068, plain, (![A_262]: (A_262='#skF_5' | ~v1_xboole_0(A_262))), inference(resolution, [status(thm)], [c_1049, c_14])).
% 3.50/1.57  tff(c_1075, plain, (k2_zfmisc_1('#skF_3', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_1050, c_1068])).
% 3.50/1.57  tff(c_1278, plain, (![A_307, B_308, C_309, D_310]: (r2_hidden(k4_tarski(A_307, B_308), k2_zfmisc_1(C_309, D_310)) | ~r2_hidden(B_308, D_310) | ~r2_hidden(A_307, C_309))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.50/1.57  tff(c_1310, plain, (![C_311, D_312, B_313, A_314]: (~v1_xboole_0(k2_zfmisc_1(C_311, D_312)) | ~r2_hidden(B_313, D_312) | ~r2_hidden(A_314, C_311))), inference(resolution, [status(thm)], [c_1278, c_2])).
% 3.50/1.57  tff(c_1312, plain, (![B_313, A_314]: (~v1_xboole_0('#skF_5') | ~r2_hidden(B_313, '#skF_4') | ~r2_hidden(A_314, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1075, c_1310])).
% 3.50/1.57  tff(c_1314, plain, (![B_313, A_314]: (~r2_hidden(B_313, '#skF_4') | ~r2_hidden(A_314, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1049, c_1312])).
% 3.50/1.57  tff(c_1317, plain, (![A_315]: (~r2_hidden(A_315, '#skF_3'))), inference(splitLeft, [status(thm)], [c_1314])).
% 3.50/1.57  tff(c_1337, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_4, c_1317])).
% 3.50/1.57  tff(c_1056, plain, (![A_11]: (A_11='#skF_5' | ~v1_xboole_0(A_11))), inference(resolution, [status(thm)], [c_1049, c_14])).
% 3.50/1.57  tff(c_1340, plain, ('#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_1337, c_1056])).
% 3.50/1.57  tff(c_1346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1060, c_1340])).
% 3.50/1.57  tff(c_1349, plain, (![B_316]: (~r2_hidden(B_316, '#skF_4'))), inference(splitRight, [status(thm)], [c_1314])).
% 3.50/1.57  tff(c_1369, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_1349])).
% 3.50/1.57  tff(c_1379, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_1369, c_1056])).
% 3.50/1.57  tff(c_1385, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1059, c_1379])).
% 3.50/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.57  
% 3.50/1.57  Inference rules
% 3.50/1.57  ----------------------
% 3.50/1.57  #Ref     : 0
% 3.50/1.57  #Sup     : 295
% 3.50/1.57  #Fact    : 0
% 3.50/1.57  #Define  : 0
% 3.50/1.57  #Split   : 5
% 3.50/1.57  #Chain   : 0
% 3.50/1.57  #Close   : 0
% 3.50/1.57  
% 3.50/1.57  Ordering : KBO
% 3.50/1.57  
% 3.50/1.57  Simplification rules
% 3.50/1.57  ----------------------
% 3.50/1.57  #Subsume      : 37
% 3.50/1.57  #Demod        : 48
% 3.50/1.57  #Tautology    : 95
% 3.50/1.57  #SimpNegUnit  : 10
% 3.50/1.57  #BackRed      : 14
% 3.50/1.57  
% 3.50/1.57  #Partial instantiations: 0
% 3.50/1.57  #Strategies tried      : 1
% 3.50/1.57  
% 3.50/1.57  Timing (in seconds)
% 3.50/1.57  ----------------------
% 3.50/1.58  Preprocessing        : 0.31
% 3.50/1.58  Parsing              : 0.16
% 3.50/1.58  CNF conversion       : 0.02
% 3.50/1.58  Main loop            : 0.44
% 3.50/1.58  Inferencing          : 0.17
% 3.50/1.58  Reduction            : 0.11
% 3.50/1.58  Demodulation         : 0.07
% 3.50/1.58  BG Simplification    : 0.02
% 3.50/1.58  Subsumption          : 0.09
% 3.50/1.58  Abstraction          : 0.02
% 3.50/1.58  MUC search           : 0.00
% 3.50/1.58  Cooper               : 0.00
% 3.50/1.58  Total                : 0.78
% 3.50/1.58  Index Insertion      : 0.00
% 3.50/1.58  Index Deletion       : 0.00
% 3.50/1.58  Index Matching       : 0.00
% 3.50/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
