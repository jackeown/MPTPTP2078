%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:15 EST 2020

% Result     : Theorem 23.92s
% Output     : CNFRefutation 23.92s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 416 expanded)
%              Number of leaves         :   23 ( 151 expanded)
%              Depth                    :   17
%              Number of atoms          :  122 (1078 expanded)
%              Number of equality atoms :   30 ( 232 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_54,axiom,(
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

tff(f_63,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_50,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_110,plain,(
    ! [A_35,B_36] :
      ( r2_hidden('#skF_3'(A_35,B_36),A_35)
      | r1_xboole_0(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_30,plain,(
    ! [C_20,A_16] :
      ( C_20 = A_16
      | ~ r2_hidden(C_20,k1_tarski(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_181,plain,(
    ! [A_53,B_54] :
      ( '#skF_3'(k1_tarski(A_53),B_54) = A_53
      | r1_xboole_0(k1_tarski(A_53),B_54) ) ),
    inference(resolution,[status(thm)],[c_110,c_30])).

tff(c_188,plain,(
    '#skF_3'(k1_tarski('#skF_6'),'#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_181,c_50])).

tff(c_24,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),B_10)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_192,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | r1_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_24])).

tff(c_198,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_192])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_48,plain,(
    k3_xboole_0(k1_tarski('#skF_6'),'#skF_7') != k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_51,plain,(
    k3_xboole_0('#skF_7',k1_tarski('#skF_6')) != k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_48])).

tff(c_32,plain,(
    ! [C_20] : r2_hidden(C_20,k1_tarski(C_20)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_18,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),B_4)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k3_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_743,plain,(
    ! [A_112,B_113,C_114] :
      ( ~ r2_hidden('#skF_1'(A_112,B_113,C_114),C_114)
      | r2_hidden('#skF_2'(A_112,B_113,C_114),C_114)
      | k3_xboole_0(A_112,B_113) = C_114 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_782,plain,(
    ! [A_117,B_118] :
      ( r2_hidden('#skF_2'(A_117,B_118,B_118),B_118)
      | k3_xboole_0(A_117,B_118) = B_118 ) ),
    inference(resolution,[status(thm)],[c_18,c_743])).

tff(c_804,plain,(
    ! [A_117,A_16] :
      ( '#skF_2'(A_117,k1_tarski(A_16),k1_tarski(A_16)) = A_16
      | k3_xboole_0(A_117,k1_tarski(A_16)) = k1_tarski(A_16) ) ),
    inference(resolution,[status(thm)],[c_782,c_30])).

tff(c_757,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_2'(A_3,B_4,B_4),B_4)
      | k3_xboole_0(A_3,B_4) = B_4 ) ),
    inference(resolution,[status(thm)],[c_18,c_743])).

tff(c_22,plain,(
    ! [A_9,B_10,C_13] :
      ( ~ r1_xboole_0(A_9,B_10)
      | ~ r2_hidden(C_13,B_10)
      | ~ r2_hidden(C_13,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_398,plain,(
    ! [C_84,B_85,A_86] :
      ( ~ r2_hidden(C_84,B_85)
      | ~ r2_hidden(C_84,k1_tarski(A_86))
      | '#skF_3'(k1_tarski(A_86),B_85) = A_86 ) ),
    inference(resolution,[status(thm)],[c_181,c_22])).

tff(c_476,plain,(
    ! [C_91,A_92] :
      ( ~ r2_hidden(C_91,k1_tarski(A_92))
      | '#skF_3'(k1_tarski(A_92),k1_tarski(C_91)) = A_92 ) ),
    inference(resolution,[status(thm)],[c_32,c_398])).

tff(c_2007,plain,(
    ! [A_186,C_187] :
      ( r2_hidden(A_186,k1_tarski(C_187))
      | r1_xboole_0(k1_tarski(A_186),k1_tarski(C_187))
      | ~ r2_hidden(C_187,k1_tarski(A_186)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_476,c_24])).

tff(c_33983,plain,(
    ! [C_1065,C_1066,A_1067] :
      ( ~ r2_hidden(C_1065,k1_tarski(C_1066))
      | ~ r2_hidden(C_1065,k1_tarski(A_1067))
      | r2_hidden(A_1067,k1_tarski(C_1066))
      | ~ r2_hidden(C_1066,k1_tarski(A_1067)) ) ),
    inference(resolution,[status(thm)],[c_2007,c_22])).

tff(c_34375,plain,(
    ! [A_1068,C_1069] :
      ( r2_hidden(A_1068,k1_tarski(C_1069))
      | ~ r2_hidden(C_1069,k1_tarski(A_1068)) ) ),
    inference(resolution,[status(thm)],[c_32,c_33983])).

tff(c_34749,plain,(
    ! [A_1068,A_3] :
      ( r2_hidden(A_1068,k1_tarski('#skF_2'(A_3,k1_tarski(A_1068),k1_tarski(A_1068))))
      | k3_xboole_0(A_3,k1_tarski(A_1068)) = k1_tarski(A_1068) ) ),
    inference(resolution,[status(thm)],[c_757,c_34375])).

tff(c_4,plain,(
    ! [D_8,A_3,B_4] :
      ( r2_hidden(D_8,k3_xboole_0(A_3,B_4))
      | ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_154,plain,(
    ! [D_44,A_45,B_46] :
      ( r2_hidden(D_44,A_45)
      | ~ r2_hidden(D_44,k3_xboole_0(A_45,B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_169,plain,(
    ! [A_9,A_45,B_46] :
      ( r2_hidden('#skF_3'(A_9,k3_xboole_0(A_45,B_46)),A_45)
      | r1_xboole_0(A_9,k3_xboole_0(A_45,B_46)) ) ),
    inference(resolution,[status(thm)],[c_24,c_154])).

tff(c_2280,plain,(
    ! [A_196,B_197,A_198] :
      ( ~ r2_hidden('#skF_3'(A_196,B_197),k1_tarski(A_198))
      | '#skF_3'(k1_tarski(A_198),B_197) = A_198
      | r1_xboole_0(A_196,B_197) ) ),
    inference(resolution,[status(thm)],[c_24,c_398])).

tff(c_3626,plain,(
    ! [A_251,B_252,A_253] :
      ( '#skF_3'(k1_tarski(A_251),k3_xboole_0(k1_tarski(A_251),B_252)) = A_251
      | r1_xboole_0(A_253,k3_xboole_0(k1_tarski(A_251),B_252)) ) ),
    inference(resolution,[status(thm)],[c_169,c_2280])).

tff(c_122,plain,(
    ! [D_39,B_40,A_41] :
      ( r2_hidden(D_39,B_40)
      | ~ r2_hidden(D_39,k3_xboole_0(A_41,B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_137,plain,(
    ! [A_9,A_41,B_40] :
      ( r2_hidden('#skF_3'(A_9,k3_xboole_0(A_41,B_40)),B_40)
      | r1_xboole_0(A_9,k3_xboole_0(A_41,B_40)) ) ),
    inference(resolution,[status(thm)],[c_24,c_122])).

tff(c_3656,plain,(
    ! [A_251,B_252,A_253] :
      ( r2_hidden(A_251,B_252)
      | r1_xboole_0(k1_tarski(A_251),k3_xboole_0(k1_tarski(A_251),B_252))
      | r1_xboole_0(A_253,k3_xboole_0(k1_tarski(A_251),B_252)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3626,c_137])).

tff(c_58024,plain,(
    ! [A_1254,B_1255] :
      ( r2_hidden(A_1254,B_1255)
      | r1_xboole_0(k1_tarski(A_1254),k3_xboole_0(k1_tarski(A_1254),B_1255)) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_3656])).

tff(c_58314,plain,(
    ! [C_1260,A_1261,B_1262] :
      ( ~ r2_hidden(C_1260,k3_xboole_0(k1_tarski(A_1261),B_1262))
      | ~ r2_hidden(C_1260,k1_tarski(A_1261))
      | r2_hidden(A_1261,B_1262) ) ),
    inference(resolution,[status(thm)],[c_58024,c_22])).

tff(c_58964,plain,(
    ! [A_1263,B_1264,D_1265] :
      ( r2_hidden(A_1263,B_1264)
      | ~ r2_hidden(D_1265,B_1264)
      | ~ r2_hidden(D_1265,k1_tarski(A_1263)) ) ),
    inference(resolution,[status(thm)],[c_4,c_58314])).

tff(c_59376,plain,(
    ! [A_1266] :
      ( r2_hidden(A_1266,'#skF_7')
      | ~ r2_hidden('#skF_6',k1_tarski(A_1266)) ) ),
    inference(resolution,[status(thm)],[c_198,c_58964])).

tff(c_61939,plain,(
    ! [A_1314] :
      ( r2_hidden('#skF_2'(A_1314,k1_tarski('#skF_6'),k1_tarski('#skF_6')),'#skF_7')
      | k3_xboole_0(A_1314,k1_tarski('#skF_6')) = k1_tarski('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_34749,c_59376])).

tff(c_12,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),B_4)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),B_4)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),A_3)
      | k3_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_61955,plain,
    ( r2_hidden('#skF_1'('#skF_7',k1_tarski('#skF_6'),k1_tarski('#skF_6')),k1_tarski('#skF_6'))
    | ~ r2_hidden('#skF_2'('#skF_7',k1_tarski('#skF_6'),k1_tarski('#skF_6')),k1_tarski('#skF_6'))
    | k3_xboole_0('#skF_7',k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(resolution,[status(thm)],[c_61939,c_12])).

tff(c_61973,plain,
    ( r2_hidden('#skF_1'('#skF_7',k1_tarski('#skF_6'),k1_tarski('#skF_6')),k1_tarski('#skF_6'))
    | ~ r2_hidden('#skF_2'('#skF_7',k1_tarski('#skF_6'),k1_tarski('#skF_6')),k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_51,c_61955])).

tff(c_63078,plain,(
    ~ r2_hidden('#skF_2'('#skF_7',k1_tarski('#skF_6'),k1_tarski('#skF_6')),k1_tarski('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_61973])).

tff(c_63145,plain,
    ( ~ r2_hidden('#skF_6',k1_tarski('#skF_6'))
    | k3_xboole_0('#skF_7',k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_804,c_63078])).

tff(c_63157,plain,(
    k3_xboole_0('#skF_7',k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_63145])).

tff(c_63159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_63157])).

tff(c_63161,plain,(
    r2_hidden('#skF_2'('#skF_7',k1_tarski('#skF_6'),k1_tarski('#skF_6')),k1_tarski('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_61973])).

tff(c_63380,plain,(
    '#skF_2'('#skF_7',k1_tarski('#skF_6'),k1_tarski('#skF_6')) = '#skF_6' ),
    inference(resolution,[status(thm)],[c_63161,c_30])).

tff(c_63160,plain,(
    r2_hidden('#skF_1'('#skF_7',k1_tarski('#skF_6'),k1_tarski('#skF_6')),k1_tarski('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_61973])).

tff(c_10,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),B_4)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),A_3)
      | k3_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_63210,plain,
    ( ~ r2_hidden('#skF_2'('#skF_7',k1_tarski('#skF_6'),k1_tarski('#skF_6')),k1_tarski('#skF_6'))
    | ~ r2_hidden('#skF_2'('#skF_7',k1_tarski('#skF_6'),k1_tarski('#skF_6')),'#skF_7')
    | k3_xboole_0('#skF_7',k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(resolution,[status(thm)],[c_63160,c_10])).

tff(c_63235,plain,
    ( ~ r2_hidden('#skF_2'('#skF_7',k1_tarski('#skF_6'),k1_tarski('#skF_6')),k1_tarski('#skF_6'))
    | ~ r2_hidden('#skF_2'('#skF_7',k1_tarski('#skF_6'),k1_tarski('#skF_6')),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_63210])).

tff(c_64316,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_63380,c_32,c_63380,c_63235])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:22:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.92/14.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.92/14.75  
% 23.92/14.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.92/14.75  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4
% 23.92/14.75  
% 23.92/14.75  %Foreground sorts:
% 23.92/14.75  
% 23.92/14.75  
% 23.92/14.75  %Background operators:
% 23.92/14.75  
% 23.92/14.75  
% 23.92/14.75  %Foreground operators:
% 23.92/14.75  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 23.92/14.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.92/14.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 23.92/14.75  tff(k1_tarski, type, k1_tarski: $i > $i).
% 23.92/14.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 23.92/14.75  tff('#skF_7', type, '#skF_7': $i).
% 23.92/14.75  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 23.92/14.75  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 23.92/14.75  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 23.92/14.75  tff('#skF_6', type, '#skF_6': $i).
% 23.92/14.75  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 23.92/14.75  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 23.92/14.75  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 23.92/14.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.92/14.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.92/14.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 23.92/14.75  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 23.92/14.75  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 23.92/14.75  
% 23.92/14.77  tff(f_74, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 23.92/14.77  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 23.92/14.77  tff(f_63, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 23.92/14.77  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 23.92/14.77  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 23.92/14.77  tff(c_50, plain, (~r1_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_74])).
% 23.92/14.77  tff(c_110, plain, (![A_35, B_36]: (r2_hidden('#skF_3'(A_35, B_36), A_35) | r1_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_54])).
% 23.92/14.77  tff(c_30, plain, (![C_20, A_16]: (C_20=A_16 | ~r2_hidden(C_20, k1_tarski(A_16)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 23.92/14.77  tff(c_181, plain, (![A_53, B_54]: ('#skF_3'(k1_tarski(A_53), B_54)=A_53 | r1_xboole_0(k1_tarski(A_53), B_54))), inference(resolution, [status(thm)], [c_110, c_30])).
% 23.92/14.77  tff(c_188, plain, ('#skF_3'(k1_tarski('#skF_6'), '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_181, c_50])).
% 23.92/14.77  tff(c_24, plain, (![A_9, B_10]: (r2_hidden('#skF_3'(A_9, B_10), B_10) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 23.92/14.77  tff(c_192, plain, (r2_hidden('#skF_6', '#skF_7') | r1_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_188, c_24])).
% 23.92/14.77  tff(c_198, plain, (r2_hidden('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_50, c_192])).
% 23.92/14.77  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 23.92/14.77  tff(c_48, plain, (k3_xboole_0(k1_tarski('#skF_6'), '#skF_7')!=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_74])).
% 23.92/14.77  tff(c_51, plain, (k3_xboole_0('#skF_7', k1_tarski('#skF_6'))!=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_48])).
% 23.92/14.77  tff(c_32, plain, (![C_20]: (r2_hidden(C_20, k1_tarski(C_20)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 23.92/14.77  tff(c_18, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), B_4) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k3_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 23.92/14.77  tff(c_743, plain, (![A_112, B_113, C_114]: (~r2_hidden('#skF_1'(A_112, B_113, C_114), C_114) | r2_hidden('#skF_2'(A_112, B_113, C_114), C_114) | k3_xboole_0(A_112, B_113)=C_114)), inference(cnfTransformation, [status(thm)], [f_36])).
% 23.92/14.77  tff(c_782, plain, (![A_117, B_118]: (r2_hidden('#skF_2'(A_117, B_118, B_118), B_118) | k3_xboole_0(A_117, B_118)=B_118)), inference(resolution, [status(thm)], [c_18, c_743])).
% 23.92/14.77  tff(c_804, plain, (![A_117, A_16]: ('#skF_2'(A_117, k1_tarski(A_16), k1_tarski(A_16))=A_16 | k3_xboole_0(A_117, k1_tarski(A_16))=k1_tarski(A_16))), inference(resolution, [status(thm)], [c_782, c_30])).
% 23.92/14.77  tff(c_757, plain, (![A_3, B_4]: (r2_hidden('#skF_2'(A_3, B_4, B_4), B_4) | k3_xboole_0(A_3, B_4)=B_4)), inference(resolution, [status(thm)], [c_18, c_743])).
% 23.92/14.77  tff(c_22, plain, (![A_9, B_10, C_13]: (~r1_xboole_0(A_9, B_10) | ~r2_hidden(C_13, B_10) | ~r2_hidden(C_13, A_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 23.92/14.77  tff(c_398, plain, (![C_84, B_85, A_86]: (~r2_hidden(C_84, B_85) | ~r2_hidden(C_84, k1_tarski(A_86)) | '#skF_3'(k1_tarski(A_86), B_85)=A_86)), inference(resolution, [status(thm)], [c_181, c_22])).
% 23.92/14.77  tff(c_476, plain, (![C_91, A_92]: (~r2_hidden(C_91, k1_tarski(A_92)) | '#skF_3'(k1_tarski(A_92), k1_tarski(C_91))=A_92)), inference(resolution, [status(thm)], [c_32, c_398])).
% 23.92/14.77  tff(c_2007, plain, (![A_186, C_187]: (r2_hidden(A_186, k1_tarski(C_187)) | r1_xboole_0(k1_tarski(A_186), k1_tarski(C_187)) | ~r2_hidden(C_187, k1_tarski(A_186)))), inference(superposition, [status(thm), theory('equality')], [c_476, c_24])).
% 23.92/14.77  tff(c_33983, plain, (![C_1065, C_1066, A_1067]: (~r2_hidden(C_1065, k1_tarski(C_1066)) | ~r2_hidden(C_1065, k1_tarski(A_1067)) | r2_hidden(A_1067, k1_tarski(C_1066)) | ~r2_hidden(C_1066, k1_tarski(A_1067)))), inference(resolution, [status(thm)], [c_2007, c_22])).
% 23.92/14.77  tff(c_34375, plain, (![A_1068, C_1069]: (r2_hidden(A_1068, k1_tarski(C_1069)) | ~r2_hidden(C_1069, k1_tarski(A_1068)))), inference(resolution, [status(thm)], [c_32, c_33983])).
% 23.92/14.77  tff(c_34749, plain, (![A_1068, A_3]: (r2_hidden(A_1068, k1_tarski('#skF_2'(A_3, k1_tarski(A_1068), k1_tarski(A_1068)))) | k3_xboole_0(A_3, k1_tarski(A_1068))=k1_tarski(A_1068))), inference(resolution, [status(thm)], [c_757, c_34375])).
% 23.92/14.77  tff(c_4, plain, (![D_8, A_3, B_4]: (r2_hidden(D_8, k3_xboole_0(A_3, B_4)) | ~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 23.92/14.77  tff(c_154, plain, (![D_44, A_45, B_46]: (r2_hidden(D_44, A_45) | ~r2_hidden(D_44, k3_xboole_0(A_45, B_46)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 23.92/14.77  tff(c_169, plain, (![A_9, A_45, B_46]: (r2_hidden('#skF_3'(A_9, k3_xboole_0(A_45, B_46)), A_45) | r1_xboole_0(A_9, k3_xboole_0(A_45, B_46)))), inference(resolution, [status(thm)], [c_24, c_154])).
% 23.92/14.77  tff(c_2280, plain, (![A_196, B_197, A_198]: (~r2_hidden('#skF_3'(A_196, B_197), k1_tarski(A_198)) | '#skF_3'(k1_tarski(A_198), B_197)=A_198 | r1_xboole_0(A_196, B_197))), inference(resolution, [status(thm)], [c_24, c_398])).
% 23.92/14.77  tff(c_3626, plain, (![A_251, B_252, A_253]: ('#skF_3'(k1_tarski(A_251), k3_xboole_0(k1_tarski(A_251), B_252))=A_251 | r1_xboole_0(A_253, k3_xboole_0(k1_tarski(A_251), B_252)))), inference(resolution, [status(thm)], [c_169, c_2280])).
% 23.92/14.77  tff(c_122, plain, (![D_39, B_40, A_41]: (r2_hidden(D_39, B_40) | ~r2_hidden(D_39, k3_xboole_0(A_41, B_40)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 23.92/14.77  tff(c_137, plain, (![A_9, A_41, B_40]: (r2_hidden('#skF_3'(A_9, k3_xboole_0(A_41, B_40)), B_40) | r1_xboole_0(A_9, k3_xboole_0(A_41, B_40)))), inference(resolution, [status(thm)], [c_24, c_122])).
% 23.92/14.77  tff(c_3656, plain, (![A_251, B_252, A_253]: (r2_hidden(A_251, B_252) | r1_xboole_0(k1_tarski(A_251), k3_xboole_0(k1_tarski(A_251), B_252)) | r1_xboole_0(A_253, k3_xboole_0(k1_tarski(A_251), B_252)))), inference(superposition, [status(thm), theory('equality')], [c_3626, c_137])).
% 23.92/14.77  tff(c_58024, plain, (![A_1254, B_1255]: (r2_hidden(A_1254, B_1255) | r1_xboole_0(k1_tarski(A_1254), k3_xboole_0(k1_tarski(A_1254), B_1255)))), inference(factorization, [status(thm), theory('equality')], [c_3656])).
% 23.92/14.77  tff(c_58314, plain, (![C_1260, A_1261, B_1262]: (~r2_hidden(C_1260, k3_xboole_0(k1_tarski(A_1261), B_1262)) | ~r2_hidden(C_1260, k1_tarski(A_1261)) | r2_hidden(A_1261, B_1262))), inference(resolution, [status(thm)], [c_58024, c_22])).
% 23.92/14.77  tff(c_58964, plain, (![A_1263, B_1264, D_1265]: (r2_hidden(A_1263, B_1264) | ~r2_hidden(D_1265, B_1264) | ~r2_hidden(D_1265, k1_tarski(A_1263)))), inference(resolution, [status(thm)], [c_4, c_58314])).
% 23.92/14.77  tff(c_59376, plain, (![A_1266]: (r2_hidden(A_1266, '#skF_7') | ~r2_hidden('#skF_6', k1_tarski(A_1266)))), inference(resolution, [status(thm)], [c_198, c_58964])).
% 23.92/14.77  tff(c_61939, plain, (![A_1314]: (r2_hidden('#skF_2'(A_1314, k1_tarski('#skF_6'), k1_tarski('#skF_6')), '#skF_7') | k3_xboole_0(A_1314, k1_tarski('#skF_6'))=k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_34749, c_59376])).
% 23.92/14.77  tff(c_12, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), B_4) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), B_4) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), A_3) | k3_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 23.92/14.77  tff(c_61955, plain, (r2_hidden('#skF_1'('#skF_7', k1_tarski('#skF_6'), k1_tarski('#skF_6')), k1_tarski('#skF_6')) | ~r2_hidden('#skF_2'('#skF_7', k1_tarski('#skF_6'), k1_tarski('#skF_6')), k1_tarski('#skF_6')) | k3_xboole_0('#skF_7', k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(resolution, [status(thm)], [c_61939, c_12])).
% 23.92/14.77  tff(c_61973, plain, (r2_hidden('#skF_1'('#skF_7', k1_tarski('#skF_6'), k1_tarski('#skF_6')), k1_tarski('#skF_6')) | ~r2_hidden('#skF_2'('#skF_7', k1_tarski('#skF_6'), k1_tarski('#skF_6')), k1_tarski('#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_51, c_51, c_61955])).
% 23.92/14.77  tff(c_63078, plain, (~r2_hidden('#skF_2'('#skF_7', k1_tarski('#skF_6'), k1_tarski('#skF_6')), k1_tarski('#skF_6'))), inference(splitLeft, [status(thm)], [c_61973])).
% 23.92/14.77  tff(c_63145, plain, (~r2_hidden('#skF_6', k1_tarski('#skF_6')) | k3_xboole_0('#skF_7', k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_804, c_63078])).
% 23.92/14.77  tff(c_63157, plain, (k3_xboole_0('#skF_7', k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_63145])).
% 23.92/14.77  tff(c_63159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_63157])).
% 23.92/14.77  tff(c_63161, plain, (r2_hidden('#skF_2'('#skF_7', k1_tarski('#skF_6'), k1_tarski('#skF_6')), k1_tarski('#skF_6'))), inference(splitRight, [status(thm)], [c_61973])).
% 23.92/14.77  tff(c_63380, plain, ('#skF_2'('#skF_7', k1_tarski('#skF_6'), k1_tarski('#skF_6'))='#skF_6'), inference(resolution, [status(thm)], [c_63161, c_30])).
% 23.92/14.77  tff(c_63160, plain, (r2_hidden('#skF_1'('#skF_7', k1_tarski('#skF_6'), k1_tarski('#skF_6')), k1_tarski('#skF_6'))), inference(splitRight, [status(thm)], [c_61973])).
% 23.92/14.77  tff(c_10, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), B_4) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), A_3) | k3_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 23.92/14.77  tff(c_63210, plain, (~r2_hidden('#skF_2'('#skF_7', k1_tarski('#skF_6'), k1_tarski('#skF_6')), k1_tarski('#skF_6')) | ~r2_hidden('#skF_2'('#skF_7', k1_tarski('#skF_6'), k1_tarski('#skF_6')), '#skF_7') | k3_xboole_0('#skF_7', k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(resolution, [status(thm)], [c_63160, c_10])).
% 23.92/14.77  tff(c_63235, plain, (~r2_hidden('#skF_2'('#skF_7', k1_tarski('#skF_6'), k1_tarski('#skF_6')), k1_tarski('#skF_6')) | ~r2_hidden('#skF_2'('#skF_7', k1_tarski('#skF_6'), k1_tarski('#skF_6')), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_51, c_63210])).
% 23.92/14.77  tff(c_64316, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_198, c_63380, c_32, c_63380, c_63235])).
% 23.92/14.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.92/14.77  
% 23.92/14.77  Inference rules
% 23.92/14.77  ----------------------
% 23.92/14.77  #Ref     : 0
% 23.92/14.77  #Sup     : 15264
% 23.92/14.77  #Fact    : 2
% 23.92/14.77  #Define  : 0
% 23.92/14.77  #Split   : 1
% 23.92/14.77  #Chain   : 0
% 23.92/14.77  #Close   : 0
% 23.92/14.77  
% 23.92/14.77  Ordering : KBO
% 23.92/14.77  
% 23.92/14.77  Simplification rules
% 23.92/14.77  ----------------------
% 23.92/14.77  #Subsume      : 2623
% 23.92/14.77  #Demod        : 3697
% 23.92/14.77  #Tautology    : 1134
% 23.92/14.77  #SimpNegUnit  : 47
% 23.92/14.77  #BackRed      : 2
% 23.92/14.77  
% 23.92/14.77  #Partial instantiations: 0
% 23.92/14.77  #Strategies tried      : 1
% 23.92/14.77  
% 23.92/14.77  Timing (in seconds)
% 23.92/14.77  ----------------------
% 23.92/14.77  Preprocessing        : 0.31
% 23.92/14.77  Parsing              : 0.16
% 23.92/14.77  CNF conversion       : 0.02
% 23.92/14.77  Main loop            : 13.67
% 23.92/14.77  Inferencing          : 2.19
% 23.92/14.77  Reduction            : 3.86
% 23.92/14.77  Demodulation         : 3.29
% 23.92/14.77  BG Simplification    : 0.36
% 23.92/14.77  Subsumption          : 6.39
% 23.92/14.77  Abstraction          : 0.73
% 23.92/14.77  MUC search           : 0.00
% 23.92/14.77  Cooper               : 0.00
% 23.92/14.77  Total                : 14.02
% 23.92/14.77  Index Insertion      : 0.00
% 23.92/14.77  Index Deletion       : 0.00
% 23.92/14.78  Index Matching       : 0.00
% 23.92/14.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------
