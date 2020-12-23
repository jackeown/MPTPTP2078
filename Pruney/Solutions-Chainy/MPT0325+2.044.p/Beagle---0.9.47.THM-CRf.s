%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:26 EST 2020

% Result     : Theorem 4.14s
% Output     : CNFRefutation 4.39s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 243 expanded)
%              Number of leaves         :   26 (  91 expanded)
%              Depth                    :   10
%              Number of atoms          :  107 ( 484 expanded)
%              Number of equality atoms :   28 ( 100 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,axiom,(
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

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_52,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_54,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_36,plain,
    ( ~ r1_tarski('#skF_4','#skF_6')
    | ~ r1_tarski('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_79,plain,(
    ~ r1_tarski('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_40,plain,(
    r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_196,plain,(
    ! [A_65,B_66,C_67,D_68] :
      ( r2_hidden(k4_tarski(A_65,B_66),k2_zfmisc_1(C_67,D_68))
      | ~ r2_hidden(B_66,D_68)
      | ~ r2_hidden(A_65,C_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_488,plain,(
    ! [B_115,D_111,B_113,C_112,A_114] :
      ( r2_hidden(k4_tarski(A_114,B_113),B_115)
      | ~ r1_tarski(k2_zfmisc_1(C_112,D_111),B_115)
      | ~ r2_hidden(B_113,D_111)
      | ~ r2_hidden(A_114,C_112) ) ),
    inference(resolution,[status(thm)],[c_196,c_2])).

tff(c_549,plain,(
    ! [A_121,B_122] :
      ( r2_hidden(k4_tarski(A_121,B_122),k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(B_122,'#skF_4')
      | ~ r2_hidden(A_121,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_40,c_488])).

tff(c_28,plain,(
    ! [A_17,C_19,B_18,D_20] :
      ( r2_hidden(A_17,C_19)
      | ~ r2_hidden(k4_tarski(A_17,B_18),k2_zfmisc_1(C_19,D_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_570,plain,(
    ! [A_121,B_122] :
      ( r2_hidden(A_121,'#skF_5')
      | ~ r2_hidden(B_122,'#skF_4')
      | ~ r2_hidden(A_121,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_549,c_28])).

tff(c_1020,plain,(
    ! [B_152] : ~ r2_hidden(B_152,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_570])).

tff(c_1056,plain,(
    ! [A_154] : r1_xboole_0(A_154,'#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_1020])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(A_15,B_16) = A_15
      | ~ r1_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1072,plain,(
    ! [A_156] : k4_xboole_0(A_156,'#skF_4') = A_156 ),
    inference(resolution,[status(thm)],[c_1056,c_20])).

tff(c_14,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_87,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k4_xboole_0(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_102,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k3_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_87])).

tff(c_105,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_102])).

tff(c_1099,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1072,c_105])).

tff(c_32,plain,(
    ! [A_21] : k2_zfmisc_1(A_21,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1150,plain,(
    ! [A_21] : k2_zfmisc_1(A_21,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1099,c_1099,c_32])).

tff(c_38,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1152,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1099,c_38])).

tff(c_1241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1150,c_1152])).

tff(c_1243,plain,(
    ! [A_159] :
      ( r2_hidden(A_159,'#skF_5')
      | ~ r2_hidden(A_159,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_570])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1282,plain,(
    ! [A_160] :
      ( r1_tarski(A_160,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_160,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1243,c_4])).

tff(c_1290,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_1282])).

tff(c_1295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_79,c_1290])).

tff(c_1296,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_1414,plain,(
    ! [A_199,B_200,C_201,D_202] :
      ( r2_hidden(k4_tarski(A_199,B_200),k2_zfmisc_1(C_201,D_202))
      | ~ r2_hidden(B_200,D_202)
      | ~ r2_hidden(A_199,C_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2356,plain,(
    ! [D_296,C_299,B_298,A_297,B_295] :
      ( r2_hidden(k4_tarski(A_297,B_295),B_298)
      | ~ r1_tarski(k2_zfmisc_1(C_299,D_296),B_298)
      | ~ r2_hidden(B_295,D_296)
      | ~ r2_hidden(A_297,C_299) ) ),
    inference(resolution,[status(thm)],[c_1414,c_2])).

tff(c_2452,plain,(
    ! [A_304,B_305] :
      ( r2_hidden(k4_tarski(A_304,B_305),k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(B_305,'#skF_4')
      | ~ r2_hidden(A_304,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_40,c_2356])).

tff(c_26,plain,(
    ! [B_18,D_20,A_17,C_19] :
      ( r2_hidden(B_18,D_20)
      | ~ r2_hidden(k4_tarski(A_17,B_18),k2_zfmisc_1(C_19,D_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2471,plain,(
    ! [B_305,A_304] :
      ( r2_hidden(B_305,'#skF_6')
      | ~ r2_hidden(B_305,'#skF_4')
      | ~ r2_hidden(A_304,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2452,c_26])).

tff(c_2951,plain,(
    ! [A_334] : ~ r2_hidden(A_334,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2471])).

tff(c_2983,plain,(
    ! [A_335] : r1_xboole_0(A_335,'#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_2951])).

tff(c_3000,plain,(
    ! [A_337] : k4_xboole_0(A_337,'#skF_3') = A_337 ),
    inference(resolution,[status(thm)],[c_2983,c_20])).

tff(c_1314,plain,(
    ! [A_174,B_175] : k4_xboole_0(A_174,k4_xboole_0(A_174,B_175)) = k3_xboole_0(A_174,B_175) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1329,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k3_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1314])).

tff(c_1332,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1329])).

tff(c_3018,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_3000,c_1332])).

tff(c_34,plain,(
    ! [B_22] : k2_zfmisc_1(k1_xboole_0,B_22) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3068,plain,(
    ! [B_22] : k2_zfmisc_1('#skF_3',B_22) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3018,c_3018,c_34])).

tff(c_3069,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3018,c_38])).

tff(c_3174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3068,c_3069])).

tff(c_3176,plain,(
    ! [B_340] :
      ( r2_hidden(B_340,'#skF_6')
      | ~ r2_hidden(B_340,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_2471])).

tff(c_3264,plain,(
    ! [A_346] :
      ( r1_tarski(A_346,'#skF_6')
      | ~ r2_hidden('#skF_1'(A_346,'#skF_6'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3176,c_4])).

tff(c_3272,plain,(
    r1_tarski('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_3264])).

tff(c_3277,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1296,c_1296,c_3272])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:10:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.14/1.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.14/1.82  
% 4.14/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.14/1.82  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.14/1.82  
% 4.14/1.82  %Foreground sorts:
% 4.14/1.82  
% 4.14/1.82  
% 4.14/1.82  %Background operators:
% 4.14/1.82  
% 4.14/1.82  
% 4.14/1.82  %Foreground operators:
% 4.14/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.14/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.14/1.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.14/1.82  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.14/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.14/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.14/1.82  tff('#skF_5', type, '#skF_5': $i).
% 4.14/1.82  tff('#skF_6', type, '#skF_6': $i).
% 4.14/1.82  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.14/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.14/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.14/1.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.14/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.14/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.14/1.82  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.14/1.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.14/1.82  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.14/1.82  
% 4.39/1.84  tff(f_81, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 4.39/1.84  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.39/1.84  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.39/1.84  tff(f_66, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 4.39/1.84  tff(f_60, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.39/1.84  tff(f_52, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 4.39/1.84  tff(f_54, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.39/1.84  tff(f_56, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.39/1.84  tff(f_72, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.39/1.84  tff(c_36, plain, (~r1_tarski('#skF_4', '#skF_6') | ~r1_tarski('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.39/1.84  tff(c_79, plain, (~r1_tarski('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_36])).
% 4.39/1.84  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.39/1.84  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.39/1.84  tff(c_40, plain, (r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.39/1.84  tff(c_196, plain, (![A_65, B_66, C_67, D_68]: (r2_hidden(k4_tarski(A_65, B_66), k2_zfmisc_1(C_67, D_68)) | ~r2_hidden(B_66, D_68) | ~r2_hidden(A_65, C_67))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.39/1.84  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.39/1.84  tff(c_488, plain, (![B_115, D_111, B_113, C_112, A_114]: (r2_hidden(k4_tarski(A_114, B_113), B_115) | ~r1_tarski(k2_zfmisc_1(C_112, D_111), B_115) | ~r2_hidden(B_113, D_111) | ~r2_hidden(A_114, C_112))), inference(resolution, [status(thm)], [c_196, c_2])).
% 4.39/1.84  tff(c_549, plain, (![A_121, B_122]: (r2_hidden(k4_tarski(A_121, B_122), k2_zfmisc_1('#skF_5', '#skF_6')) | ~r2_hidden(B_122, '#skF_4') | ~r2_hidden(A_121, '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_488])).
% 4.39/1.84  tff(c_28, plain, (![A_17, C_19, B_18, D_20]: (r2_hidden(A_17, C_19) | ~r2_hidden(k4_tarski(A_17, B_18), k2_zfmisc_1(C_19, D_20)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.39/1.84  tff(c_570, plain, (![A_121, B_122]: (r2_hidden(A_121, '#skF_5') | ~r2_hidden(B_122, '#skF_4') | ~r2_hidden(A_121, '#skF_3'))), inference(resolution, [status(thm)], [c_549, c_28])).
% 4.39/1.84  tff(c_1020, plain, (![B_152]: (~r2_hidden(B_152, '#skF_4'))), inference(splitLeft, [status(thm)], [c_570])).
% 4.39/1.84  tff(c_1056, plain, (![A_154]: (r1_xboole_0(A_154, '#skF_4'))), inference(resolution, [status(thm)], [c_10, c_1020])).
% 4.39/1.84  tff(c_20, plain, (![A_15, B_16]: (k4_xboole_0(A_15, B_16)=A_15 | ~r1_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.39/1.84  tff(c_1072, plain, (![A_156]: (k4_xboole_0(A_156, '#skF_4')=A_156)), inference(resolution, [status(thm)], [c_1056, c_20])).
% 4.39/1.84  tff(c_14, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.39/1.84  tff(c_16, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.39/1.84  tff(c_87, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k4_xboole_0(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.39/1.84  tff(c_102, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k3_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_87])).
% 4.39/1.84  tff(c_105, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_102])).
% 4.39/1.84  tff(c_1099, plain, (k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1072, c_105])).
% 4.39/1.84  tff(c_32, plain, (![A_21]: (k2_zfmisc_1(A_21, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.39/1.84  tff(c_1150, plain, (![A_21]: (k2_zfmisc_1(A_21, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1099, c_1099, c_32])).
% 4.39/1.84  tff(c_38, plain, (k2_zfmisc_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.39/1.84  tff(c_1152, plain, (k2_zfmisc_1('#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1099, c_38])).
% 4.39/1.84  tff(c_1241, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1150, c_1152])).
% 4.39/1.84  tff(c_1243, plain, (![A_159]: (r2_hidden(A_159, '#skF_5') | ~r2_hidden(A_159, '#skF_3'))), inference(splitRight, [status(thm)], [c_570])).
% 4.39/1.84  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.39/1.84  tff(c_1282, plain, (![A_160]: (r1_tarski(A_160, '#skF_5') | ~r2_hidden('#skF_1'(A_160, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_1243, c_4])).
% 4.39/1.84  tff(c_1290, plain, (r1_tarski('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_1282])).
% 4.39/1.84  tff(c_1295, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_79, c_1290])).
% 4.39/1.84  tff(c_1296, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_36])).
% 4.39/1.84  tff(c_1414, plain, (![A_199, B_200, C_201, D_202]: (r2_hidden(k4_tarski(A_199, B_200), k2_zfmisc_1(C_201, D_202)) | ~r2_hidden(B_200, D_202) | ~r2_hidden(A_199, C_201))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.39/1.84  tff(c_2356, plain, (![D_296, C_299, B_298, A_297, B_295]: (r2_hidden(k4_tarski(A_297, B_295), B_298) | ~r1_tarski(k2_zfmisc_1(C_299, D_296), B_298) | ~r2_hidden(B_295, D_296) | ~r2_hidden(A_297, C_299))), inference(resolution, [status(thm)], [c_1414, c_2])).
% 4.39/1.84  tff(c_2452, plain, (![A_304, B_305]: (r2_hidden(k4_tarski(A_304, B_305), k2_zfmisc_1('#skF_5', '#skF_6')) | ~r2_hidden(B_305, '#skF_4') | ~r2_hidden(A_304, '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_2356])).
% 4.39/1.84  tff(c_26, plain, (![B_18, D_20, A_17, C_19]: (r2_hidden(B_18, D_20) | ~r2_hidden(k4_tarski(A_17, B_18), k2_zfmisc_1(C_19, D_20)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.39/1.84  tff(c_2471, plain, (![B_305, A_304]: (r2_hidden(B_305, '#skF_6') | ~r2_hidden(B_305, '#skF_4') | ~r2_hidden(A_304, '#skF_3'))), inference(resolution, [status(thm)], [c_2452, c_26])).
% 4.39/1.84  tff(c_2951, plain, (![A_334]: (~r2_hidden(A_334, '#skF_3'))), inference(splitLeft, [status(thm)], [c_2471])).
% 4.39/1.84  tff(c_2983, plain, (![A_335]: (r1_xboole_0(A_335, '#skF_3'))), inference(resolution, [status(thm)], [c_10, c_2951])).
% 4.39/1.84  tff(c_3000, plain, (![A_337]: (k4_xboole_0(A_337, '#skF_3')=A_337)), inference(resolution, [status(thm)], [c_2983, c_20])).
% 4.39/1.84  tff(c_1314, plain, (![A_174, B_175]: (k4_xboole_0(A_174, k4_xboole_0(A_174, B_175))=k3_xboole_0(A_174, B_175))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.39/1.84  tff(c_1329, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k3_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1314])).
% 4.39/1.84  tff(c_1332, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1329])).
% 4.39/1.84  tff(c_3018, plain, (k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_3000, c_1332])).
% 4.39/1.84  tff(c_34, plain, (![B_22]: (k2_zfmisc_1(k1_xboole_0, B_22)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.39/1.84  tff(c_3068, plain, (![B_22]: (k2_zfmisc_1('#skF_3', B_22)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3018, c_3018, c_34])).
% 4.39/1.84  tff(c_3069, plain, (k2_zfmisc_1('#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3018, c_38])).
% 4.39/1.84  tff(c_3174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3068, c_3069])).
% 4.39/1.84  tff(c_3176, plain, (![B_340]: (r2_hidden(B_340, '#skF_6') | ~r2_hidden(B_340, '#skF_4'))), inference(splitRight, [status(thm)], [c_2471])).
% 4.39/1.84  tff(c_3264, plain, (![A_346]: (r1_tarski(A_346, '#skF_6') | ~r2_hidden('#skF_1'(A_346, '#skF_6'), '#skF_4'))), inference(resolution, [status(thm)], [c_3176, c_4])).
% 4.39/1.84  tff(c_3272, plain, (r1_tarski('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_6, c_3264])).
% 4.39/1.84  tff(c_3277, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1296, c_1296, c_3272])).
% 4.39/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.39/1.84  
% 4.39/1.84  Inference rules
% 4.39/1.84  ----------------------
% 4.39/1.84  #Ref     : 0
% 4.39/1.84  #Sup     : 800
% 4.39/1.84  #Fact    : 0
% 4.39/1.84  #Define  : 0
% 4.39/1.84  #Split   : 9
% 4.39/1.84  #Chain   : 0
% 4.39/1.84  #Close   : 0
% 4.39/1.84  
% 4.39/1.84  Ordering : KBO
% 4.39/1.84  
% 4.39/1.84  Simplification rules
% 4.39/1.84  ----------------------
% 4.39/1.84  #Subsume      : 90
% 4.39/1.84  #Demod        : 286
% 4.39/1.84  #Tautology    : 314
% 4.39/1.84  #SimpNegUnit  : 12
% 4.39/1.84  #BackRed      : 56
% 4.39/1.84  
% 4.39/1.84  #Partial instantiations: 0
% 4.39/1.84  #Strategies tried      : 1
% 4.39/1.84  
% 4.39/1.84  Timing (in seconds)
% 4.39/1.84  ----------------------
% 4.39/1.84  Preprocessing        : 0.30
% 4.39/1.84  Parsing              : 0.17
% 4.39/1.84  CNF conversion       : 0.02
% 4.39/1.84  Main loop            : 0.69
% 4.39/1.84  Inferencing          : 0.26
% 4.39/1.84  Reduction            : 0.20
% 4.39/1.84  Demodulation         : 0.14
% 4.39/1.84  BG Simplification    : 0.03
% 4.39/1.84  Subsumption          : 0.14
% 4.39/1.84  Abstraction          : 0.03
% 4.39/1.84  MUC search           : 0.00
% 4.39/1.84  Cooper               : 0.00
% 4.39/1.84  Total                : 1.03
% 4.39/1.84  Index Insertion      : 0.00
% 4.39/1.84  Index Deletion       : 0.00
% 4.39/1.84  Index Matching       : 0.00
% 4.39/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
