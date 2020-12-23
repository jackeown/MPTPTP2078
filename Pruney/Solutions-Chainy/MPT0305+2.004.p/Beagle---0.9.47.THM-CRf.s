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
% DateTime   : Thu Dec  3 09:53:52 EST 2020

% Result     : Theorem 5.55s
% Output     : CNFRefutation 5.65s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 165 expanded)
%              Number of leaves         :   20 (  63 expanded)
%              Depth                    :    8
%              Number of atoms          :  127 ( 386 expanded)
%              Number of equality atoms :   25 (  48 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( A != k1_xboole_0
          & ( r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(C,A))
            | r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(A,C)) )
          & ~ r1_tarski(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_34,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_26,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2197,plain,(
    ! [A_269,B_270,C_271] :
      ( r2_hidden('#skF_2'(A_269,B_270,C_271),B_270)
      | r2_hidden('#skF_3'(A_269,B_270,C_271),C_271)
      | k3_xboole_0(A_269,B_270) = C_271 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_6,B_7,C_8] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7,C_8),C_8)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k3_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2335,plain,(
    ! [A_284,B_285] :
      ( r2_hidden('#skF_3'(A_284,B_285,B_285),B_285)
      | k3_xboole_0(A_284,B_285) = B_285 ) ),
    inference(resolution,[status(thm)],[c_2197,c_20])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2457,plain,(
    ! [A_294,B_295,B_296] :
      ( r2_hidden('#skF_3'(A_294,B_295,B_295),B_296)
      | ~ r1_tarski(B_295,B_296)
      | k3_xboole_0(A_294,B_295) = B_295 ) ),
    inference(resolution,[status(thm)],[c_2335,c_2])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3134,plain,(
    ! [A_366,B_367,B_368,A_369] :
      ( r2_hidden('#skF_3'(A_366,B_367,B_367),B_368)
      | ~ r1_tarski(B_367,k3_xboole_0(A_369,B_368))
      | k3_xboole_0(A_366,B_367) = B_367 ) ),
    inference(resolution,[status(thm)],[c_2457,c_10])).

tff(c_3174,plain,(
    ! [A_366,B_368] :
      ( r2_hidden('#skF_3'(A_366,k1_xboole_0,k1_xboole_0),B_368)
      | k3_xboole_0(A_366,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_3134])).

tff(c_22,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),B_7)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k3_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_469,plain,(
    ! [A_101,B_102,C_103] :
      ( ~ r2_hidden('#skF_2'(A_101,B_102,C_103),C_103)
      | r2_hidden('#skF_3'(A_101,B_102,C_103),C_103)
      | k3_xboole_0(A_101,B_102) = C_103 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_492,plain,(
    ! [A_105,B_106] :
      ( r2_hidden('#skF_3'(A_105,B_106,B_106),B_106)
      | k3_xboole_0(A_105,B_106) = B_106 ) ),
    inference(resolution,[status(thm)],[c_22,c_469])).

tff(c_569,plain,(
    ! [A_115,B_116,B_117] :
      ( r2_hidden('#skF_3'(A_115,B_116,B_116),B_117)
      | ~ r1_tarski(B_116,B_117)
      | k3_xboole_0(A_115,B_116) = B_116 ) ),
    inference(resolution,[status(thm)],[c_492,c_2])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1245,plain,(
    ! [A_187,B_188,A_189,B_190] :
      ( r2_hidden('#skF_3'(A_187,B_188,B_188),A_189)
      | ~ r1_tarski(B_188,k3_xboole_0(A_189,B_190))
      | k3_xboole_0(A_187,B_188) = B_188 ) ),
    inference(resolution,[status(thm)],[c_569,c_12])).

tff(c_1285,plain,(
    ! [A_187,A_189] :
      ( r2_hidden('#skF_3'(A_187,k1_xboole_0,k1_xboole_0),A_189)
      | k3_xboole_0(A_187,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_1245])).

tff(c_36,plain,
    ( r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_4','#skF_6'))
    | r1_tarski(k2_zfmisc_1('#skF_5','#skF_4'),k2_zfmisc_1('#skF_6','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_64,plain,(
    r1_tarski(k2_zfmisc_1('#skF_5','#skF_4'),k2_zfmisc_1('#skF_6','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_103,plain,(
    ! [A_46,B_47,C_48,D_49] :
      ( r2_hidden(k4_tarski(A_46,B_47),k2_zfmisc_1(C_48,D_49))
      | ~ r2_hidden(B_47,D_49)
      | ~ r2_hidden(A_46,C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1405,plain,(
    ! [C_203,B_204,A_205,D_202,B_201] :
      ( r2_hidden(k4_tarski(A_205,B_201),B_204)
      | ~ r1_tarski(k2_zfmisc_1(C_203,D_202),B_204)
      | ~ r2_hidden(B_201,D_202)
      | ~ r2_hidden(A_205,C_203) ) ),
    inference(resolution,[status(thm)],[c_103,c_2])).

tff(c_1413,plain,(
    ! [A_206,B_207] :
      ( r2_hidden(k4_tarski(A_206,B_207),k2_zfmisc_1('#skF_6','#skF_4'))
      | ~ r2_hidden(B_207,'#skF_4')
      | ~ r2_hidden(A_206,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_64,c_1405])).

tff(c_32,plain,(
    ! [A_13,C_15,B_14,D_16] :
      ( r2_hidden(A_13,C_15)
      | ~ r2_hidden(k4_tarski(A_13,B_14),k2_zfmisc_1(C_15,D_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1428,plain,(
    ! [A_206,B_207] :
      ( r2_hidden(A_206,'#skF_6')
      | ~ r2_hidden(B_207,'#skF_4')
      | ~ r2_hidden(A_206,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1413,c_32])).

tff(c_1432,plain,(
    ! [B_208] : ~ r2_hidden(B_208,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1428])).

tff(c_1773,plain,(
    ! [A_212] : k3_xboole_0(A_212,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1285,c_1432])).

tff(c_24,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_2'(A_6,B_7,C_8),A_6)
      | r2_hidden('#skF_3'(A_6,B_7,C_8),C_8)
      | k3_xboole_0(A_6,B_7) = C_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_483,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_3'(A_6,B_7,A_6),A_6)
      | k3_xboole_0(A_6,B_7) = A_6 ) ),
    inference(resolution,[status(thm)],[c_24,c_469])).

tff(c_1502,plain,(
    ! [B_7] : k3_xboole_0('#skF_4',B_7) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_483,c_1432])).

tff(c_1778,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1773,c_1502])).

tff(c_1853,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1778])).

tff(c_1855,plain,(
    ! [A_213] :
      ( r2_hidden(A_213,'#skF_6')
      | ~ r2_hidden(A_213,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_1428])).

tff(c_1977,plain,(
    ! [B_216] :
      ( r2_hidden('#skF_1'('#skF_5',B_216),'#skF_6')
      | r1_tarski('#skF_5',B_216) ) ),
    inference(resolution,[status(thm)],[c_6,c_1855])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1989,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_1977,c_4])).

tff(c_1997,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_34,c_1989])).

tff(c_1998,plain,(
    r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),k2_zfmisc_1('#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_2058,plain,(
    ! [A_236,B_237,C_238,D_239] :
      ( r2_hidden(k4_tarski(A_236,B_237),k2_zfmisc_1(C_238,D_239))
      | ~ r2_hidden(B_237,D_239)
      | ~ r2_hidden(A_236,C_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3531,plain,(
    ! [D_390,A_389,C_393,B_392,B_391] :
      ( r2_hidden(k4_tarski(A_389,B_392),B_391)
      | ~ r1_tarski(k2_zfmisc_1(C_393,D_390),B_391)
      | ~ r2_hidden(B_392,D_390)
      | ~ r2_hidden(A_389,C_393) ) ),
    inference(resolution,[status(thm)],[c_2058,c_2])).

tff(c_3539,plain,(
    ! [A_394,B_395] :
      ( r2_hidden(k4_tarski(A_394,B_395),k2_zfmisc_1('#skF_4','#skF_6'))
      | ~ r2_hidden(B_395,'#skF_5')
      | ~ r2_hidden(A_394,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1998,c_3531])).

tff(c_30,plain,(
    ! [B_14,D_16,A_13,C_15] :
      ( r2_hidden(B_14,D_16)
      | ~ r2_hidden(k4_tarski(A_13,B_14),k2_zfmisc_1(C_15,D_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3554,plain,(
    ! [B_395,A_394] :
      ( r2_hidden(B_395,'#skF_6')
      | ~ r2_hidden(B_395,'#skF_5')
      | ~ r2_hidden(A_394,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3539,c_30])).

tff(c_3624,plain,(
    ! [A_400] : ~ r2_hidden(A_400,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3554])).

tff(c_4002,plain,(
    ! [A_404] : k3_xboole_0(A_404,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3174,c_3624])).

tff(c_2402,plain,(
    ! [A_289,B_290,C_291] :
      ( r2_hidden('#skF_2'(A_289,B_290,C_291),A_289)
      | r2_hidden('#skF_3'(A_289,B_290,C_291),C_291)
      | k3_xboole_0(A_289,B_290) = C_291 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2432,plain,(
    ! [A_289,B_290] :
      ( r2_hidden('#skF_3'(A_289,B_290,A_289),A_289)
      | k3_xboole_0(A_289,B_290) = A_289 ) ),
    inference(resolution,[status(thm)],[c_2402,c_20])).

tff(c_3711,plain,(
    ! [B_290] : k3_xboole_0('#skF_4',B_290) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2432,c_3624])).

tff(c_4007,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_4002,c_3711])).

tff(c_4090,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_4007])).

tff(c_4092,plain,(
    ! [B_405] :
      ( r2_hidden(B_405,'#skF_6')
      | ~ r2_hidden(B_405,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_3554])).

tff(c_4189,plain,(
    ! [B_406] :
      ( r2_hidden('#skF_1'('#skF_5',B_406),'#skF_6')
      | r1_tarski('#skF_5',B_406) ) ),
    inference(resolution,[status(thm)],[c_6,c_4092])).

tff(c_4201,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_4189,c_4])).

tff(c_4209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_34,c_4201])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:00:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.55/2.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.55/2.04  
% 5.55/2.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.55/2.04  %$ r2_hidden > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 5.55/2.04  
% 5.55/2.04  %Foreground sorts:
% 5.55/2.04  
% 5.55/2.04  
% 5.55/2.04  %Background operators:
% 5.55/2.04  
% 5.55/2.04  
% 5.55/2.04  %Foreground operators:
% 5.55/2.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.55/2.04  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.55/2.04  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.55/2.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.55/2.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.55/2.04  tff('#skF_5', type, '#skF_5': $i).
% 5.55/2.04  tff('#skF_6', type, '#skF_6': $i).
% 5.55/2.04  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.55/2.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.55/2.04  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.55/2.04  tff('#skF_4', type, '#skF_4': $i).
% 5.55/2.04  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.55/2.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.55/2.04  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.55/2.04  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.55/2.04  
% 5.65/2.06  tff(f_61, negated_conjecture, ~(![A, B, C]: ~((~(A = k1_xboole_0) & (r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(C, A)) | r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(A, C)))) & ~r1_tarski(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_zfmisc_1)).
% 5.65/2.06  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.65/2.06  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.65/2.06  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 5.65/2.06  tff(f_49, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 5.65/2.06  tff(c_34, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.65/2.06  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.65/2.06  tff(c_38, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.65/2.06  tff(c_26, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.65/2.06  tff(c_2197, plain, (![A_269, B_270, C_271]: (r2_hidden('#skF_2'(A_269, B_270, C_271), B_270) | r2_hidden('#skF_3'(A_269, B_270, C_271), C_271) | k3_xboole_0(A_269, B_270)=C_271)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.65/2.06  tff(c_20, plain, (![A_6, B_7, C_8]: (~r2_hidden('#skF_2'(A_6, B_7, C_8), C_8) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k3_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.65/2.06  tff(c_2335, plain, (![A_284, B_285]: (r2_hidden('#skF_3'(A_284, B_285, B_285), B_285) | k3_xboole_0(A_284, B_285)=B_285)), inference(resolution, [status(thm)], [c_2197, c_20])).
% 5.65/2.06  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.65/2.06  tff(c_2457, plain, (![A_294, B_295, B_296]: (r2_hidden('#skF_3'(A_294, B_295, B_295), B_296) | ~r1_tarski(B_295, B_296) | k3_xboole_0(A_294, B_295)=B_295)), inference(resolution, [status(thm)], [c_2335, c_2])).
% 5.65/2.06  tff(c_10, plain, (![D_11, B_7, A_6]: (r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.65/2.06  tff(c_3134, plain, (![A_366, B_367, B_368, A_369]: (r2_hidden('#skF_3'(A_366, B_367, B_367), B_368) | ~r1_tarski(B_367, k3_xboole_0(A_369, B_368)) | k3_xboole_0(A_366, B_367)=B_367)), inference(resolution, [status(thm)], [c_2457, c_10])).
% 5.65/2.06  tff(c_3174, plain, (![A_366, B_368]: (r2_hidden('#skF_3'(A_366, k1_xboole_0, k1_xboole_0), B_368) | k3_xboole_0(A_366, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_3134])).
% 5.65/2.06  tff(c_22, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), B_7) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k3_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.65/2.06  tff(c_469, plain, (![A_101, B_102, C_103]: (~r2_hidden('#skF_2'(A_101, B_102, C_103), C_103) | r2_hidden('#skF_3'(A_101, B_102, C_103), C_103) | k3_xboole_0(A_101, B_102)=C_103)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.65/2.06  tff(c_492, plain, (![A_105, B_106]: (r2_hidden('#skF_3'(A_105, B_106, B_106), B_106) | k3_xboole_0(A_105, B_106)=B_106)), inference(resolution, [status(thm)], [c_22, c_469])).
% 5.65/2.06  tff(c_569, plain, (![A_115, B_116, B_117]: (r2_hidden('#skF_3'(A_115, B_116, B_116), B_117) | ~r1_tarski(B_116, B_117) | k3_xboole_0(A_115, B_116)=B_116)), inference(resolution, [status(thm)], [c_492, c_2])).
% 5.65/2.06  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.65/2.06  tff(c_1245, plain, (![A_187, B_188, A_189, B_190]: (r2_hidden('#skF_3'(A_187, B_188, B_188), A_189) | ~r1_tarski(B_188, k3_xboole_0(A_189, B_190)) | k3_xboole_0(A_187, B_188)=B_188)), inference(resolution, [status(thm)], [c_569, c_12])).
% 5.65/2.06  tff(c_1285, plain, (![A_187, A_189]: (r2_hidden('#skF_3'(A_187, k1_xboole_0, k1_xboole_0), A_189) | k3_xboole_0(A_187, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_1245])).
% 5.65/2.06  tff(c_36, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_4', '#skF_6')) | r1_tarski(k2_zfmisc_1('#skF_5', '#skF_4'), k2_zfmisc_1('#skF_6', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.65/2.06  tff(c_64, plain, (r1_tarski(k2_zfmisc_1('#skF_5', '#skF_4'), k2_zfmisc_1('#skF_6', '#skF_4'))), inference(splitLeft, [status(thm)], [c_36])).
% 5.65/2.06  tff(c_103, plain, (![A_46, B_47, C_48, D_49]: (r2_hidden(k4_tarski(A_46, B_47), k2_zfmisc_1(C_48, D_49)) | ~r2_hidden(B_47, D_49) | ~r2_hidden(A_46, C_48))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.65/2.06  tff(c_1405, plain, (![C_203, B_204, A_205, D_202, B_201]: (r2_hidden(k4_tarski(A_205, B_201), B_204) | ~r1_tarski(k2_zfmisc_1(C_203, D_202), B_204) | ~r2_hidden(B_201, D_202) | ~r2_hidden(A_205, C_203))), inference(resolution, [status(thm)], [c_103, c_2])).
% 5.65/2.06  tff(c_1413, plain, (![A_206, B_207]: (r2_hidden(k4_tarski(A_206, B_207), k2_zfmisc_1('#skF_6', '#skF_4')) | ~r2_hidden(B_207, '#skF_4') | ~r2_hidden(A_206, '#skF_5'))), inference(resolution, [status(thm)], [c_64, c_1405])).
% 5.65/2.06  tff(c_32, plain, (![A_13, C_15, B_14, D_16]: (r2_hidden(A_13, C_15) | ~r2_hidden(k4_tarski(A_13, B_14), k2_zfmisc_1(C_15, D_16)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.65/2.06  tff(c_1428, plain, (![A_206, B_207]: (r2_hidden(A_206, '#skF_6') | ~r2_hidden(B_207, '#skF_4') | ~r2_hidden(A_206, '#skF_5'))), inference(resolution, [status(thm)], [c_1413, c_32])).
% 5.65/2.06  tff(c_1432, plain, (![B_208]: (~r2_hidden(B_208, '#skF_4'))), inference(splitLeft, [status(thm)], [c_1428])).
% 5.65/2.06  tff(c_1773, plain, (![A_212]: (k3_xboole_0(A_212, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1285, c_1432])).
% 5.65/2.06  tff(c_24, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_2'(A_6, B_7, C_8), A_6) | r2_hidden('#skF_3'(A_6, B_7, C_8), C_8) | k3_xboole_0(A_6, B_7)=C_8)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.65/2.06  tff(c_483, plain, (![A_6, B_7]: (r2_hidden('#skF_3'(A_6, B_7, A_6), A_6) | k3_xboole_0(A_6, B_7)=A_6)), inference(resolution, [status(thm)], [c_24, c_469])).
% 5.65/2.06  tff(c_1502, plain, (![B_7]: (k3_xboole_0('#skF_4', B_7)='#skF_4')), inference(resolution, [status(thm)], [c_483, c_1432])).
% 5.65/2.06  tff(c_1778, plain, (k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1773, c_1502])).
% 5.65/2.06  tff(c_1853, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_1778])).
% 5.65/2.06  tff(c_1855, plain, (![A_213]: (r2_hidden(A_213, '#skF_6') | ~r2_hidden(A_213, '#skF_5'))), inference(splitRight, [status(thm)], [c_1428])).
% 5.65/2.06  tff(c_1977, plain, (![B_216]: (r2_hidden('#skF_1'('#skF_5', B_216), '#skF_6') | r1_tarski('#skF_5', B_216))), inference(resolution, [status(thm)], [c_6, c_1855])).
% 5.65/2.06  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.65/2.06  tff(c_1989, plain, (r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_1977, c_4])).
% 5.65/2.06  tff(c_1997, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_34, c_1989])).
% 5.65/2.06  tff(c_1998, plain, (r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), k2_zfmisc_1('#skF_4', '#skF_6'))), inference(splitRight, [status(thm)], [c_36])).
% 5.65/2.06  tff(c_2058, plain, (![A_236, B_237, C_238, D_239]: (r2_hidden(k4_tarski(A_236, B_237), k2_zfmisc_1(C_238, D_239)) | ~r2_hidden(B_237, D_239) | ~r2_hidden(A_236, C_238))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.65/2.06  tff(c_3531, plain, (![D_390, A_389, C_393, B_392, B_391]: (r2_hidden(k4_tarski(A_389, B_392), B_391) | ~r1_tarski(k2_zfmisc_1(C_393, D_390), B_391) | ~r2_hidden(B_392, D_390) | ~r2_hidden(A_389, C_393))), inference(resolution, [status(thm)], [c_2058, c_2])).
% 5.65/2.06  tff(c_3539, plain, (![A_394, B_395]: (r2_hidden(k4_tarski(A_394, B_395), k2_zfmisc_1('#skF_4', '#skF_6')) | ~r2_hidden(B_395, '#skF_5') | ~r2_hidden(A_394, '#skF_4'))), inference(resolution, [status(thm)], [c_1998, c_3531])).
% 5.65/2.06  tff(c_30, plain, (![B_14, D_16, A_13, C_15]: (r2_hidden(B_14, D_16) | ~r2_hidden(k4_tarski(A_13, B_14), k2_zfmisc_1(C_15, D_16)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.65/2.06  tff(c_3554, plain, (![B_395, A_394]: (r2_hidden(B_395, '#skF_6') | ~r2_hidden(B_395, '#skF_5') | ~r2_hidden(A_394, '#skF_4'))), inference(resolution, [status(thm)], [c_3539, c_30])).
% 5.65/2.06  tff(c_3624, plain, (![A_400]: (~r2_hidden(A_400, '#skF_4'))), inference(splitLeft, [status(thm)], [c_3554])).
% 5.65/2.06  tff(c_4002, plain, (![A_404]: (k3_xboole_0(A_404, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3174, c_3624])).
% 5.65/2.06  tff(c_2402, plain, (![A_289, B_290, C_291]: (r2_hidden('#skF_2'(A_289, B_290, C_291), A_289) | r2_hidden('#skF_3'(A_289, B_290, C_291), C_291) | k3_xboole_0(A_289, B_290)=C_291)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.65/2.06  tff(c_2432, plain, (![A_289, B_290]: (r2_hidden('#skF_3'(A_289, B_290, A_289), A_289) | k3_xboole_0(A_289, B_290)=A_289)), inference(resolution, [status(thm)], [c_2402, c_20])).
% 5.65/2.06  tff(c_3711, plain, (![B_290]: (k3_xboole_0('#skF_4', B_290)='#skF_4')), inference(resolution, [status(thm)], [c_2432, c_3624])).
% 5.65/2.06  tff(c_4007, plain, (k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_4002, c_3711])).
% 5.65/2.06  tff(c_4090, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_4007])).
% 5.65/2.06  tff(c_4092, plain, (![B_405]: (r2_hidden(B_405, '#skF_6') | ~r2_hidden(B_405, '#skF_5'))), inference(splitRight, [status(thm)], [c_3554])).
% 5.65/2.06  tff(c_4189, plain, (![B_406]: (r2_hidden('#skF_1'('#skF_5', B_406), '#skF_6') | r1_tarski('#skF_5', B_406))), inference(resolution, [status(thm)], [c_6, c_4092])).
% 5.65/2.06  tff(c_4201, plain, (r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_4189, c_4])).
% 5.65/2.06  tff(c_4209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_34, c_4201])).
% 5.65/2.06  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.65/2.06  
% 5.65/2.06  Inference rules
% 5.65/2.06  ----------------------
% 5.65/2.06  #Ref     : 0
% 5.65/2.06  #Sup     : 1012
% 5.65/2.06  #Fact    : 0
% 5.65/2.06  #Define  : 0
% 5.65/2.06  #Split   : 5
% 5.65/2.06  #Chain   : 0
% 5.65/2.06  #Close   : 0
% 5.65/2.06  
% 5.65/2.06  Ordering : KBO
% 5.65/2.06  
% 5.65/2.06  Simplification rules
% 5.65/2.06  ----------------------
% 5.65/2.06  #Subsume      : 176
% 5.65/2.06  #Demod        : 196
% 5.65/2.06  #Tautology    : 184
% 5.65/2.06  #SimpNegUnit  : 28
% 5.65/2.06  #BackRed      : 4
% 5.65/2.06  
% 5.65/2.06  #Partial instantiations: 0
% 5.65/2.06  #Strategies tried      : 1
% 5.65/2.06  
% 5.65/2.06  Timing (in seconds)
% 5.65/2.06  ----------------------
% 5.65/2.07  Preprocessing        : 0.30
% 5.65/2.07  Parsing              : 0.15
% 5.65/2.07  CNF conversion       : 0.02
% 5.65/2.07  Main loop            : 0.99
% 5.65/2.07  Inferencing          : 0.33
% 5.65/2.07  Reduction            : 0.25
% 5.65/2.07  Demodulation         : 0.17
% 5.65/2.07  BG Simplification    : 0.04
% 5.65/2.07  Subsumption          : 0.28
% 5.65/2.07  Abstraction          : 0.05
% 5.65/2.07  MUC search           : 0.00
% 5.65/2.07  Cooper               : 0.00
% 5.65/2.07  Total                : 1.33
% 5.65/2.07  Index Insertion      : 0.00
% 5.65/2.07  Index Deletion       : 0.00
% 5.65/2.07  Index Matching       : 0.00
% 5.65/2.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
