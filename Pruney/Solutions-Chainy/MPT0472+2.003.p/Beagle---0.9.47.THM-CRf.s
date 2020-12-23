%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:25 EST 2020

% Result     : Theorem 4.26s
% Output     : CNFRefutation 4.26s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 170 expanded)
%              Number of leaves         :   37 (  74 expanded)
%              Depth                    :   12
%              Number of atoms          :   93 ( 278 expanded)
%              Number of equality atoms :   42 ( 107 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k1_enumset1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_1 > #skF_4 > #skF_2 > #skF_6 > #skF_8 > #skF_5 > #skF_3 > #skF_7 > #skF_9 > #skF_12 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_11',type,(
    '#skF_11': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_87,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( ( k1_relat_1(A) = k1_xboole_0
            | k2_relat_1(A) = k1_xboole_0 )
         => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_78,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_31,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k2_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_56,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3311,plain,(
    ! [A_339,B_340] :
      ( r2_hidden(k4_tarski('#skF_8'(A_339,B_340),'#skF_7'(A_339,B_340)),A_339)
      | r2_hidden('#skF_9'(A_339,B_340),B_340)
      | k2_relat_1(A_339) = B_340 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2256,plain,(
    ! [A_229,C_230,B_231] :
      ( ~ r2_hidden(A_229,C_230)
      | ~ r1_xboole_0(k2_tarski(A_229,B_231),C_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2266,plain,(
    ! [A_229] : ~ r2_hidden(A_229,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_2256])).

tff(c_3414,plain,(
    ! [B_340] :
      ( r2_hidden('#skF_9'(k1_xboole_0,B_340),B_340)
      | k2_relat_1(k1_xboole_0) = B_340 ) ),
    inference(resolution,[status(thm)],[c_3311,c_2266])).

tff(c_3442,plain,(
    ! [B_341] :
      ( r2_hidden('#skF_9'(k1_xboole_0,B_341),B_341)
      | k1_xboole_0 = B_341 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3414])).

tff(c_2347,plain,(
    ! [A_253,B_254,D_255] :
      ( r2_hidden('#skF_6'(A_253,B_254,k2_zfmisc_1(A_253,B_254),D_255),B_254)
      | ~ r2_hidden(D_255,k2_zfmisc_1(A_253,B_254)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2352,plain,(
    ! [D_255,A_253] : ~ r2_hidden(D_255,k2_zfmisc_1(A_253,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_2347,c_2266])).

tff(c_3566,plain,(
    ! [A_253] : k2_zfmisc_1(A_253,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3442,c_2352])).

tff(c_64,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_876,plain,(
    ! [A_194,B_195,C_196] :
      ( r2_hidden('#skF_2'(A_194,B_195,C_196),A_194)
      | r2_hidden('#skF_4'(A_194,B_195,C_196),C_196)
      | k2_zfmisc_1(A_194,B_195) = C_196 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_114,plain,(
    ! [A_81,C_82,B_83] :
      ( ~ r2_hidden(A_81,C_82)
      | ~ r1_xboole_0(k2_tarski(A_81,B_83),C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_124,plain,(
    ! [A_81] : ~ r2_hidden(A_81,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_114])).

tff(c_62,plain,
    ( k2_relat_1('#skF_12') = k1_xboole_0
    | k1_relat_1('#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_74,plain,(
    k1_relat_1('#skF_12') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_154,plain,(
    ! [A_89,B_90] :
      ( r2_hidden('#skF_11'(A_89,B_90),k1_relat_1(B_90))
      | ~ r2_hidden(A_89,k2_relat_1(B_90))
      | ~ v1_relat_1(B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_157,plain,(
    ! [A_89] :
      ( r2_hidden('#skF_11'(A_89,'#skF_12'),k1_xboole_0)
      | ~ r2_hidden(A_89,k2_relat_1('#skF_12'))
      | ~ v1_relat_1('#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_154])).

tff(c_162,plain,(
    ! [A_89] :
      ( r2_hidden('#skF_11'(A_89,'#skF_12'),k1_xboole_0)
      | ~ r2_hidden(A_89,k2_relat_1('#skF_12')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_157])).

tff(c_163,plain,(
    ! [A_89] : ~ r2_hidden(A_89,k2_relat_1('#skF_12')) ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_162])).

tff(c_1328,plain,(
    ! [A_205,B_206] :
      ( r2_hidden('#skF_2'(A_205,B_206,k2_relat_1('#skF_12')),A_205)
      | k2_zfmisc_1(A_205,B_206) = k2_relat_1('#skF_12') ) ),
    inference(resolution,[status(thm)],[c_876,c_163])).

tff(c_1525,plain,(
    ! [B_206] : k2_zfmisc_1(k2_relat_1('#skF_12'),B_206) = k2_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_1328,c_163])).

tff(c_1202,plain,(
    ! [B_195,C_196] :
      ( r2_hidden('#skF_4'(k2_relat_1('#skF_12'),B_195,C_196),C_196)
      | k2_zfmisc_1(k2_relat_1('#skF_12'),B_195) = C_196 ) ),
    inference(resolution,[status(thm)],[c_876,c_163])).

tff(c_1990,plain,(
    ! [B_217,C_218] :
      ( r2_hidden('#skF_4'(k2_relat_1('#skF_12'),B_217,C_218),C_218)
      | k2_relat_1('#skF_12') = C_218 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1525,c_1202])).

tff(c_2104,plain,(
    k2_relat_1('#skF_12') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1990,c_124])).

tff(c_1526,plain,(
    ! [B_206] : k2_zfmisc_1(k1_xboole_0,B_206) = k2_relat_1('#skF_12') ),
    inference(resolution,[status(thm)],[c_1328,c_124])).

tff(c_127,plain,(
    ! [A_88] :
      ( k3_xboole_0(A_88,k2_zfmisc_1(k1_relat_1(A_88),k2_relat_1(A_88))) = A_88
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_136,plain,
    ( k3_xboole_0('#skF_12',k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_12'))) = '#skF_12'
    | ~ v1_relat_1('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_127])).

tff(c_146,plain,(
    k3_xboole_0('#skF_12',k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_12'))) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_136])).

tff(c_1536,plain,(
    k3_xboole_0('#skF_12',k2_relat_1('#skF_12')) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1526,c_146])).

tff(c_2110,plain,(
    k3_xboole_0('#skF_12',k1_xboole_0) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2104,c_1536])).

tff(c_79,plain,(
    ! [A_72,B_73] :
      ( k3_xboole_0(A_72,B_73) = k1_xboole_0
      | ~ r1_xboole_0(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_83,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_79])).

tff(c_2208,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_2110,c_83])).

tff(c_2214,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_2208])).

tff(c_2215,plain,(
    k2_relat_1('#skF_12') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_2275,plain,(
    ! [A_239] :
      ( k3_xboole_0(A_239,k2_zfmisc_1(k1_relat_1(A_239),k2_relat_1(A_239))) = A_239
      | ~ v1_relat_1(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2288,plain,
    ( k3_xboole_0('#skF_12',k2_zfmisc_1(k1_relat_1('#skF_12'),k1_xboole_0)) = '#skF_12'
    | ~ v1_relat_1('#skF_12') ),
    inference(superposition,[status(thm),theory(equality)],[c_2215,c_2275])).

tff(c_2298,plain,(
    k3_xboole_0('#skF_12',k2_zfmisc_1(k1_relat_1('#skF_12'),k1_xboole_0)) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2288])).

tff(c_3679,plain,(
    k3_xboole_0('#skF_12',k1_xboole_0) = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3566,c_2298])).

tff(c_2230,plain,(
    ! [A_222,B_223] :
      ( k3_xboole_0(A_222,B_223) = k1_xboole_0
      | ~ r1_xboole_0(A_222,B_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2234,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_2230])).

tff(c_3719,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(superposition,[status(thm),theory(equality)],[c_3679,c_2234])).

tff(c_3725,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_3719])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n008.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:47:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.26/1.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.26/1.84  
% 4.26/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.26/1.84  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k1_enumset1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_1 > #skF_4 > #skF_2 > #skF_6 > #skF_8 > #skF_5 > #skF_3 > #skF_7 > #skF_9 > #skF_12 > #skF_10
% 4.26/1.84  
% 4.26/1.84  %Foreground sorts:
% 4.26/1.84  
% 4.26/1.84  
% 4.26/1.84  %Background operators:
% 4.26/1.84  
% 4.26/1.84  
% 4.26/1.84  %Foreground operators:
% 4.26/1.84  tff('#skF_11', type, '#skF_11': ($i * $i) > $i).
% 4.26/1.84  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.26/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.26/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.26/1.84  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.26/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.26/1.84  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.26/1.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.26/1.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.26/1.84  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.26/1.84  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.26/1.84  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.26/1.84  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 4.26/1.84  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 4.26/1.84  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.26/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.26/1.84  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 4.26/1.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.26/1.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.26/1.84  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.26/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.26/1.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.26/1.84  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 4.26/1.84  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 4.26/1.84  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.26/1.84  tff('#skF_12', type, '#skF_12': $i).
% 4.26/1.84  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 4.26/1.84  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.26/1.84  
% 4.26/1.85  tff(f_87, negated_conjecture, ~(![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 4.26/1.85  tff(f_78, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 4.26/1.85  tff(f_62, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_relat_1)).
% 4.26/1.85  tff(f_31, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.26/1.85  tff(f_52, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 4.26/1.85  tff(f_47, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 4.26/1.85  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k2_relat_1(B)) & (![C]: ~r2_hidden(C, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_relat_1)).
% 4.26/1.85  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 4.26/1.85  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.26/1.85  tff(c_60, plain, (k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.26/1.85  tff(c_56, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.26/1.85  tff(c_3311, plain, (![A_339, B_340]: (r2_hidden(k4_tarski('#skF_8'(A_339, B_340), '#skF_7'(A_339, B_340)), A_339) | r2_hidden('#skF_9'(A_339, B_340), B_340) | k2_relat_1(A_339)=B_340)), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.26/1.85  tff(c_6, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.26/1.85  tff(c_2256, plain, (![A_229, C_230, B_231]: (~r2_hidden(A_229, C_230) | ~r1_xboole_0(k2_tarski(A_229, B_231), C_230))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.26/1.85  tff(c_2266, plain, (![A_229]: (~r2_hidden(A_229, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_2256])).
% 4.26/1.85  tff(c_3414, plain, (![B_340]: (r2_hidden('#skF_9'(k1_xboole_0, B_340), B_340) | k2_relat_1(k1_xboole_0)=B_340)), inference(resolution, [status(thm)], [c_3311, c_2266])).
% 4.26/1.85  tff(c_3442, plain, (![B_341]: (r2_hidden('#skF_9'(k1_xboole_0, B_341), B_341) | k1_xboole_0=B_341)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_3414])).
% 4.26/1.85  tff(c_2347, plain, (![A_253, B_254, D_255]: (r2_hidden('#skF_6'(A_253, B_254, k2_zfmisc_1(A_253, B_254), D_255), B_254) | ~r2_hidden(D_255, k2_zfmisc_1(A_253, B_254)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.26/1.85  tff(c_2352, plain, (![D_255, A_253]: (~r2_hidden(D_255, k2_zfmisc_1(A_253, k1_xboole_0)))), inference(resolution, [status(thm)], [c_2347, c_2266])).
% 4.26/1.85  tff(c_3566, plain, (![A_253]: (k2_zfmisc_1(A_253, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_3442, c_2352])).
% 4.26/1.85  tff(c_64, plain, (v1_relat_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.26/1.85  tff(c_876, plain, (![A_194, B_195, C_196]: (r2_hidden('#skF_2'(A_194, B_195, C_196), A_194) | r2_hidden('#skF_4'(A_194, B_195, C_196), C_196) | k2_zfmisc_1(A_194, B_195)=C_196)), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.26/1.85  tff(c_114, plain, (![A_81, C_82, B_83]: (~r2_hidden(A_81, C_82) | ~r1_xboole_0(k2_tarski(A_81, B_83), C_82))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.26/1.85  tff(c_124, plain, (![A_81]: (~r2_hidden(A_81, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_114])).
% 4.26/1.85  tff(c_62, plain, (k2_relat_1('#skF_12')=k1_xboole_0 | k1_relat_1('#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.26/1.85  tff(c_74, plain, (k1_relat_1('#skF_12')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_62])).
% 4.26/1.85  tff(c_154, plain, (![A_89, B_90]: (r2_hidden('#skF_11'(A_89, B_90), k1_relat_1(B_90)) | ~r2_hidden(A_89, k2_relat_1(B_90)) | ~v1_relat_1(B_90))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.26/1.85  tff(c_157, plain, (![A_89]: (r2_hidden('#skF_11'(A_89, '#skF_12'), k1_xboole_0) | ~r2_hidden(A_89, k2_relat_1('#skF_12')) | ~v1_relat_1('#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_154])).
% 4.26/1.85  tff(c_162, plain, (![A_89]: (r2_hidden('#skF_11'(A_89, '#skF_12'), k1_xboole_0) | ~r2_hidden(A_89, k2_relat_1('#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_157])).
% 4.26/1.85  tff(c_163, plain, (![A_89]: (~r2_hidden(A_89, k2_relat_1('#skF_12')))), inference(negUnitSimplification, [status(thm)], [c_124, c_162])).
% 4.26/1.85  tff(c_1328, plain, (![A_205, B_206]: (r2_hidden('#skF_2'(A_205, B_206, k2_relat_1('#skF_12')), A_205) | k2_zfmisc_1(A_205, B_206)=k2_relat_1('#skF_12'))), inference(resolution, [status(thm)], [c_876, c_163])).
% 4.26/1.85  tff(c_1525, plain, (![B_206]: (k2_zfmisc_1(k2_relat_1('#skF_12'), B_206)=k2_relat_1('#skF_12'))), inference(resolution, [status(thm)], [c_1328, c_163])).
% 4.26/1.85  tff(c_1202, plain, (![B_195, C_196]: (r2_hidden('#skF_4'(k2_relat_1('#skF_12'), B_195, C_196), C_196) | k2_zfmisc_1(k2_relat_1('#skF_12'), B_195)=C_196)), inference(resolution, [status(thm)], [c_876, c_163])).
% 4.26/1.85  tff(c_1990, plain, (![B_217, C_218]: (r2_hidden('#skF_4'(k2_relat_1('#skF_12'), B_217, C_218), C_218) | k2_relat_1('#skF_12')=C_218)), inference(demodulation, [status(thm), theory('equality')], [c_1525, c_1202])).
% 4.26/1.85  tff(c_2104, plain, (k2_relat_1('#skF_12')=k1_xboole_0), inference(resolution, [status(thm)], [c_1990, c_124])).
% 4.26/1.85  tff(c_1526, plain, (![B_206]: (k2_zfmisc_1(k1_xboole_0, B_206)=k2_relat_1('#skF_12'))), inference(resolution, [status(thm)], [c_1328, c_124])).
% 4.26/1.85  tff(c_127, plain, (![A_88]: (k3_xboole_0(A_88, k2_zfmisc_1(k1_relat_1(A_88), k2_relat_1(A_88)))=A_88 | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.26/1.85  tff(c_136, plain, (k3_xboole_0('#skF_12', k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_12')))='#skF_12' | ~v1_relat_1('#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_74, c_127])).
% 4.26/1.85  tff(c_146, plain, (k3_xboole_0('#skF_12', k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_12')))='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_136])).
% 4.26/1.85  tff(c_1536, plain, (k3_xboole_0('#skF_12', k2_relat_1('#skF_12'))='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_1526, c_146])).
% 4.26/1.85  tff(c_2110, plain, (k3_xboole_0('#skF_12', k1_xboole_0)='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_2104, c_1536])).
% 4.26/1.85  tff(c_79, plain, (![A_72, B_73]: (k3_xboole_0(A_72, B_73)=k1_xboole_0 | ~r1_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.26/1.85  tff(c_83, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_79])).
% 4.26/1.85  tff(c_2208, plain, (k1_xboole_0='#skF_12'), inference(superposition, [status(thm), theory('equality')], [c_2110, c_83])).
% 4.26/1.85  tff(c_2214, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_2208])).
% 4.26/1.85  tff(c_2215, plain, (k2_relat_1('#skF_12')=k1_xboole_0), inference(splitRight, [status(thm)], [c_62])).
% 4.26/1.85  tff(c_2275, plain, (![A_239]: (k3_xboole_0(A_239, k2_zfmisc_1(k1_relat_1(A_239), k2_relat_1(A_239)))=A_239 | ~v1_relat_1(A_239))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.26/1.85  tff(c_2288, plain, (k3_xboole_0('#skF_12', k2_zfmisc_1(k1_relat_1('#skF_12'), k1_xboole_0))='#skF_12' | ~v1_relat_1('#skF_12')), inference(superposition, [status(thm), theory('equality')], [c_2215, c_2275])).
% 4.26/1.85  tff(c_2298, plain, (k3_xboole_0('#skF_12', k2_zfmisc_1(k1_relat_1('#skF_12'), k1_xboole_0))='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2288])).
% 4.26/1.85  tff(c_3679, plain, (k3_xboole_0('#skF_12', k1_xboole_0)='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_3566, c_2298])).
% 4.26/1.85  tff(c_2230, plain, (![A_222, B_223]: (k3_xboole_0(A_222, B_223)=k1_xboole_0 | ~r1_xboole_0(A_222, B_223))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.26/1.85  tff(c_2234, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_2230])).
% 4.26/1.85  tff(c_3719, plain, (k1_xboole_0='#skF_12'), inference(superposition, [status(thm), theory('equality')], [c_3679, c_2234])).
% 4.26/1.85  tff(c_3725, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_3719])).
% 4.26/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.26/1.85  
% 4.26/1.85  Inference rules
% 4.26/1.85  ----------------------
% 4.26/1.85  #Ref     : 0
% 4.26/1.85  #Sup     : 769
% 4.26/1.85  #Fact    : 0
% 4.26/1.85  #Define  : 0
% 4.26/1.85  #Split   : 3
% 4.26/1.85  #Chain   : 0
% 4.26/1.85  #Close   : 0
% 4.26/1.85  
% 4.26/1.85  Ordering : KBO
% 4.26/1.85  
% 4.26/1.85  Simplification rules
% 4.26/1.85  ----------------------
% 4.26/1.85  #Subsume      : 244
% 4.26/1.85  #Demod        : 218
% 4.26/1.85  #Tautology    : 77
% 4.26/1.85  #SimpNegUnit  : 23
% 4.26/1.85  #BackRed      : 65
% 4.26/1.85  
% 4.26/1.86  #Partial instantiations: 0
% 4.26/1.86  #Strategies tried      : 1
% 4.26/1.86  
% 4.26/1.86  Timing (in seconds)
% 4.26/1.86  ----------------------
% 4.26/1.86  Preprocessing        : 0.39
% 4.26/1.86  Parsing              : 0.18
% 4.26/1.86  CNF conversion       : 0.03
% 4.26/1.86  Main loop            : 0.65
% 4.26/1.86  Inferencing          : 0.22
% 4.26/1.86  Reduction            : 0.19
% 4.26/1.86  Demodulation         : 0.12
% 4.26/1.86  BG Simplification    : 0.03
% 4.26/1.86  Subsumption          : 0.15
% 4.26/1.86  Abstraction          : 0.04
% 4.26/1.86  MUC search           : 0.00
% 4.26/1.86  Cooper               : 0.00
% 4.26/1.86  Total                : 1.07
% 4.26/1.86  Index Insertion      : 0.00
% 4.26/1.86  Index Deletion       : 0.00
% 4.26/1.86  Index Matching       : 0.00
% 4.26/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
