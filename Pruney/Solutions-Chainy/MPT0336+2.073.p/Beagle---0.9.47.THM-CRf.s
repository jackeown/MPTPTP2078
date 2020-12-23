%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:10 EST 2020

% Result     : Theorem 9.60s
% Output     : CNFRefutation 9.60s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 139 expanded)
%              Number of leaves         :   27 (  58 expanded)
%              Depth                    :   15
%              Number of atoms          :  110 ( 218 expanded)
%              Number of equality atoms :   25 (  49 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_49,axiom,(
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

tff(c_38,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_54,plain,(
    ! [B_30,A_31] :
      ( r1_xboole_0(B_30,A_31)
      | ~ r1_xboole_0(A_31,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_54])).

tff(c_750,plain,(
    ! [A_90,C_91,B_92] :
      ( ~ r1_xboole_0(A_90,C_91)
      | ~ r1_xboole_0(A_90,B_92)
      | r1_xboole_0(A_90,k2_xboole_0(B_92,C_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3307,plain,(
    ! [B_212,C_213,A_214] :
      ( r1_xboole_0(k2_xboole_0(B_212,C_213),A_214)
      | ~ r1_xboole_0(A_214,C_213)
      | ~ r1_xboole_0(A_214,B_212) ) ),
    inference(resolution,[status(thm)],[c_750,c_4])).

tff(c_36,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_3325,plain,
    ( ~ r1_xboole_0('#skF_3','#skF_4')
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_3307,c_36])).

tff(c_3333,plain,(
    ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_3325])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_42,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_43,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_42])).

tff(c_112,plain,(
    ! [A_38,B_39] :
      ( k4_xboole_0(A_38,B_39) = A_38
      | ~ r1_xboole_0(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_124,plain,(
    k4_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_112])).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_tarski(k4_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_258,plain,(
    ! [A_59,C_60,B_61] :
      ( r1_xboole_0(A_59,C_60)
      | ~ r1_tarski(A_59,k4_xboole_0(B_61,C_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_372,plain,(
    ! [B_69,C_70,B_71] : r1_xboole_0(k4_xboole_0(k4_xboole_0(B_69,C_70),B_71),C_70) ),
    inference(resolution,[status(thm)],[c_16,c_258])).

tff(c_407,plain,(
    ! [B_72] : r1_xboole_0(k4_xboole_0('#skF_4',B_72),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_372])).

tff(c_26,plain,(
    ! [A_20,B_21] :
      ( k4_xboole_0(A_20,B_21) = A_20
      | ~ r1_xboole_0(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3899,plain,(
    ! [B_237] : k4_xboole_0(k4_xboole_0('#skF_4',B_237),'#skF_3') = k4_xboole_0('#skF_4',B_237) ),
    inference(resolution,[status(thm)],[c_407,c_26])).

tff(c_406,plain,(
    ! [C_70,B_69,B_71] : r1_xboole_0(C_70,k4_xboole_0(k4_xboole_0(B_69,C_70),B_71)) ),
    inference(resolution,[status(thm)],[c_372,c_4])).

tff(c_4004,plain,(
    ! [B_238] : r1_xboole_0(B_238,k4_xboole_0('#skF_4',B_238)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3899,c_406])).

tff(c_4102,plain,(
    ! [B_240] : k4_xboole_0(B_240,k4_xboole_0('#skF_4',B_240)) = B_240 ),
    inference(resolution,[status(thm)],[c_4004,c_26])).

tff(c_4504,plain,(
    ! [C_245,B_246] : r1_xboole_0(C_245,k4_xboole_0(B_246,C_245)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4102,c_406])).

tff(c_4561,plain,(
    ! [C_245,B_246] : k4_xboole_0(C_245,k4_xboole_0(B_246,C_245)) = C_245 ),
    inference(resolution,[status(thm)],[c_4504,c_26])).

tff(c_18,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_139,plain,(
    ! [A_40,B_41] :
      ( r1_xboole_0(k1_tarski(A_40),B_41)
      | r2_hidden(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1928,plain,(
    ! [A_155,B_156] :
      ( k4_xboole_0(k1_tarski(A_155),B_156) = k1_tarski(A_155)
      | r2_hidden(A_155,B_156) ) ),
    inference(resolution,[status(thm)],[c_139,c_26])).

tff(c_10922,plain,(
    ! [A_461,B_462] :
      ( k3_xboole_0(k1_tarski(A_461),B_462) = k1_tarski(A_461)
      | r2_hidden(A_461,k4_xboole_0(k1_tarski(A_461),B_462)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1928])).

tff(c_40,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_104,plain,(
    ! [A_36,B_37] :
      ( r1_xboole_0(A_36,B_37)
      | k4_xboole_0(A_36,B_37) != A_36 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_110,plain,(
    ! [B_37,A_36] :
      ( r1_xboole_0(B_37,A_36)
      | k4_xboole_0(A_36,B_37) != A_36 ) ),
    inference(resolution,[status(thm)],[c_104,c_4])).

tff(c_599,plain,(
    ! [A_83,B_84,C_85] :
      ( ~ r1_xboole_0(A_83,B_84)
      | ~ r2_hidden(C_85,B_84)
      | ~ r2_hidden(C_85,A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_9086,plain,(
    ! [C_396,A_397,B_398] :
      ( ~ r2_hidden(C_396,A_397)
      | ~ r2_hidden(C_396,B_398)
      | k4_xboole_0(A_397,B_398) != A_397 ) ),
    inference(resolution,[status(thm)],[c_110,c_599])).

tff(c_9101,plain,(
    ! [B_398] :
      ( ~ r2_hidden('#skF_5',B_398)
      | k4_xboole_0('#skF_4',B_398) != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_40,c_9086])).

tff(c_10969,plain,(
    ! [B_463] :
      ( k4_xboole_0('#skF_4',k4_xboole_0(k1_tarski('#skF_5'),B_463)) != '#skF_4'
      | k3_xboole_0(k1_tarski('#skF_5'),B_463) = k1_tarski('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_10922,c_9101])).

tff(c_11002,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),'#skF_4') = k1_tarski('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_4561,c_10969])).

tff(c_312,plain,(
    ! [A_64,B_65,C_66] :
      ( r1_tarski(A_64,B_65)
      | ~ r1_tarski(A_64,k4_xboole_0(B_65,C_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1146,plain,(
    ! [A_103,A_104,B_105] :
      ( r1_tarski(A_103,A_104)
      | ~ r1_tarski(A_103,k3_xboole_0(A_104,B_105)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_312])).

tff(c_1164,plain,(
    ! [A_103,A_1,B_2] :
      ( r1_tarski(A_103,A_1)
      | ~ r1_tarski(A_103,k3_xboole_0(B_2,A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1146])).

tff(c_16207,plain,(
    ! [A_600] :
      ( r1_tarski(A_600,'#skF_4')
      | ~ r1_tarski(A_600,k1_tarski('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11002,c_1164])).

tff(c_16288,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_43,c_16207])).

tff(c_292,plain,(
    ! [A_62] :
      ( r1_xboole_0(A_62,'#skF_3')
      | ~ r1_tarski(A_62,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_258])).

tff(c_346,plain,(
    ! [A_67] :
      ( r1_xboole_0('#skF_3',A_67)
      | ~ r1_tarski(A_67,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_292,c_4])).

tff(c_357,plain,(
    ! [A_67] :
      ( k4_xboole_0('#skF_3',A_67) = '#skF_3'
      | ~ r1_tarski(A_67,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_346,c_26])).

tff(c_16297,plain,(
    k4_xboole_0('#skF_3',k3_xboole_0('#skF_3','#skF_2')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_16288,c_357])).

tff(c_184,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k4_xboole_0(A_51,B_52)) = k3_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_187,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k3_xboole_0(A_51,B_52)) = k3_xboole_0(A_51,k4_xboole_0(A_51,B_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_18])).

tff(c_16397,plain,(
    k3_xboole_0('#skF_3',k4_xboole_0('#skF_3','#skF_2')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_16297,c_187])).

tff(c_193,plain,(
    ! [A_51,B_52] : r1_tarski(k3_xboole_0(A_51,B_52),A_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_16])).

tff(c_1309,plain,(
    ! [B_111,C_112,B_113] : r1_xboole_0(k3_xboole_0(k4_xboole_0(B_111,C_112),B_113),C_112) ),
    inference(resolution,[status(thm)],[c_193,c_258])).

tff(c_1361,plain,(
    ! [B_2,B_111,C_112] : r1_xboole_0(k3_xboole_0(B_2,k4_xboole_0(B_111,C_112)),C_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1309])).

tff(c_16621,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_16397,c_1361])).

tff(c_16672,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3333,c_16621])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:35:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.60/3.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.60/3.87  
% 9.60/3.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.60/3.87  %$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 9.60/3.87  
% 9.60/3.87  %Foreground sorts:
% 9.60/3.87  
% 9.60/3.87  
% 9.60/3.87  %Background operators:
% 9.60/3.87  
% 9.60/3.87  
% 9.60/3.87  %Foreground operators:
% 9.60/3.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.60/3.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.60/3.87  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.60/3.87  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.60/3.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.60/3.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.60/3.87  tff('#skF_5', type, '#skF_5': $i).
% 9.60/3.87  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.60/3.87  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.60/3.87  tff('#skF_2', type, '#skF_2': $i).
% 9.60/3.87  tff('#skF_3', type, '#skF_3': $i).
% 9.60/3.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.60/3.87  tff('#skF_4', type, '#skF_4': $i).
% 9.60/3.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.60/3.87  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.60/3.87  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.60/3.87  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.60/3.87  
% 9.60/3.89  tff(f_97, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 9.60/3.89  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 9.60/3.89  tff(f_75, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 9.60/3.89  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.60/3.89  tff(f_79, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 9.60/3.89  tff(f_57, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 9.60/3.89  tff(f_55, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 9.60/3.89  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.60/3.89  tff(f_88, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 9.60/3.89  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 9.60/3.89  tff(c_38, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.60/3.89  tff(c_54, plain, (![B_30, A_31]: (r1_xboole_0(B_30, A_31) | ~r1_xboole_0(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.60/3.89  tff(c_57, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_54])).
% 9.60/3.89  tff(c_750, plain, (![A_90, C_91, B_92]: (~r1_xboole_0(A_90, C_91) | ~r1_xboole_0(A_90, B_92) | r1_xboole_0(A_90, k2_xboole_0(B_92, C_91)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.60/3.89  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.60/3.89  tff(c_3307, plain, (![B_212, C_213, A_214]: (r1_xboole_0(k2_xboole_0(B_212, C_213), A_214) | ~r1_xboole_0(A_214, C_213) | ~r1_xboole_0(A_214, B_212))), inference(resolution, [status(thm)], [c_750, c_4])).
% 9.60/3.89  tff(c_36, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.60/3.89  tff(c_3325, plain, (~r1_xboole_0('#skF_3', '#skF_4') | ~r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_3307, c_36])).
% 9.60/3.89  tff(c_3333, plain, (~r1_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_3325])).
% 9.60/3.89  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.60/3.89  tff(c_42, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.60/3.89  tff(c_43, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_42])).
% 9.60/3.89  tff(c_112, plain, (![A_38, B_39]: (k4_xboole_0(A_38, B_39)=A_38 | ~r1_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.60/3.89  tff(c_124, plain, (k4_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_38, c_112])).
% 9.60/3.89  tff(c_16, plain, (![A_13, B_14]: (r1_tarski(k4_xboole_0(A_13, B_14), A_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.60/3.89  tff(c_258, plain, (![A_59, C_60, B_61]: (r1_xboole_0(A_59, C_60) | ~r1_tarski(A_59, k4_xboole_0(B_61, C_60)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.60/3.89  tff(c_372, plain, (![B_69, C_70, B_71]: (r1_xboole_0(k4_xboole_0(k4_xboole_0(B_69, C_70), B_71), C_70))), inference(resolution, [status(thm)], [c_16, c_258])).
% 9.60/3.89  tff(c_407, plain, (![B_72]: (r1_xboole_0(k4_xboole_0('#skF_4', B_72), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_124, c_372])).
% 9.60/3.89  tff(c_26, plain, (![A_20, B_21]: (k4_xboole_0(A_20, B_21)=A_20 | ~r1_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.60/3.89  tff(c_3899, plain, (![B_237]: (k4_xboole_0(k4_xboole_0('#skF_4', B_237), '#skF_3')=k4_xboole_0('#skF_4', B_237))), inference(resolution, [status(thm)], [c_407, c_26])).
% 9.60/3.89  tff(c_406, plain, (![C_70, B_69, B_71]: (r1_xboole_0(C_70, k4_xboole_0(k4_xboole_0(B_69, C_70), B_71)))), inference(resolution, [status(thm)], [c_372, c_4])).
% 9.60/3.89  tff(c_4004, plain, (![B_238]: (r1_xboole_0(B_238, k4_xboole_0('#skF_4', B_238)))), inference(superposition, [status(thm), theory('equality')], [c_3899, c_406])).
% 9.60/3.89  tff(c_4102, plain, (![B_240]: (k4_xboole_0(B_240, k4_xboole_0('#skF_4', B_240))=B_240)), inference(resolution, [status(thm)], [c_4004, c_26])).
% 9.60/3.89  tff(c_4504, plain, (![C_245, B_246]: (r1_xboole_0(C_245, k4_xboole_0(B_246, C_245)))), inference(superposition, [status(thm), theory('equality')], [c_4102, c_406])).
% 9.60/3.89  tff(c_4561, plain, (![C_245, B_246]: (k4_xboole_0(C_245, k4_xboole_0(B_246, C_245))=C_245)), inference(resolution, [status(thm)], [c_4504, c_26])).
% 9.60/3.89  tff(c_18, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.60/3.89  tff(c_139, plain, (![A_40, B_41]: (r1_xboole_0(k1_tarski(A_40), B_41) | r2_hidden(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.60/3.89  tff(c_1928, plain, (![A_155, B_156]: (k4_xboole_0(k1_tarski(A_155), B_156)=k1_tarski(A_155) | r2_hidden(A_155, B_156))), inference(resolution, [status(thm)], [c_139, c_26])).
% 9.60/3.89  tff(c_10922, plain, (![A_461, B_462]: (k3_xboole_0(k1_tarski(A_461), B_462)=k1_tarski(A_461) | r2_hidden(A_461, k4_xboole_0(k1_tarski(A_461), B_462)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1928])).
% 9.60/3.89  tff(c_40, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.60/3.89  tff(c_104, plain, (![A_36, B_37]: (r1_xboole_0(A_36, B_37) | k4_xboole_0(A_36, B_37)!=A_36)), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.60/3.89  tff(c_110, plain, (![B_37, A_36]: (r1_xboole_0(B_37, A_36) | k4_xboole_0(A_36, B_37)!=A_36)), inference(resolution, [status(thm)], [c_104, c_4])).
% 9.60/3.89  tff(c_599, plain, (![A_83, B_84, C_85]: (~r1_xboole_0(A_83, B_84) | ~r2_hidden(C_85, B_84) | ~r2_hidden(C_85, A_83))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.60/3.89  tff(c_9086, plain, (![C_396, A_397, B_398]: (~r2_hidden(C_396, A_397) | ~r2_hidden(C_396, B_398) | k4_xboole_0(A_397, B_398)!=A_397)), inference(resolution, [status(thm)], [c_110, c_599])).
% 9.60/3.89  tff(c_9101, plain, (![B_398]: (~r2_hidden('#skF_5', B_398) | k4_xboole_0('#skF_4', B_398)!='#skF_4')), inference(resolution, [status(thm)], [c_40, c_9086])).
% 9.60/3.89  tff(c_10969, plain, (![B_463]: (k4_xboole_0('#skF_4', k4_xboole_0(k1_tarski('#skF_5'), B_463))!='#skF_4' | k3_xboole_0(k1_tarski('#skF_5'), B_463)=k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_10922, c_9101])).
% 9.60/3.89  tff(c_11002, plain, (k3_xboole_0(k1_tarski('#skF_5'), '#skF_4')=k1_tarski('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_4561, c_10969])).
% 9.60/3.89  tff(c_312, plain, (![A_64, B_65, C_66]: (r1_tarski(A_64, B_65) | ~r1_tarski(A_64, k4_xboole_0(B_65, C_66)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.60/3.89  tff(c_1146, plain, (![A_103, A_104, B_105]: (r1_tarski(A_103, A_104) | ~r1_tarski(A_103, k3_xboole_0(A_104, B_105)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_312])).
% 9.60/3.89  tff(c_1164, plain, (![A_103, A_1, B_2]: (r1_tarski(A_103, A_1) | ~r1_tarski(A_103, k3_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1146])).
% 9.60/3.89  tff(c_16207, plain, (![A_600]: (r1_tarski(A_600, '#skF_4') | ~r1_tarski(A_600, k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_11002, c_1164])).
% 9.60/3.89  tff(c_16288, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_43, c_16207])).
% 9.60/3.89  tff(c_292, plain, (![A_62]: (r1_xboole_0(A_62, '#skF_3') | ~r1_tarski(A_62, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_124, c_258])).
% 9.60/3.89  tff(c_346, plain, (![A_67]: (r1_xboole_0('#skF_3', A_67) | ~r1_tarski(A_67, '#skF_4'))), inference(resolution, [status(thm)], [c_292, c_4])).
% 9.60/3.89  tff(c_357, plain, (![A_67]: (k4_xboole_0('#skF_3', A_67)='#skF_3' | ~r1_tarski(A_67, '#skF_4'))), inference(resolution, [status(thm)], [c_346, c_26])).
% 9.60/3.89  tff(c_16297, plain, (k4_xboole_0('#skF_3', k3_xboole_0('#skF_3', '#skF_2'))='#skF_3'), inference(resolution, [status(thm)], [c_16288, c_357])).
% 9.60/3.89  tff(c_184, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k4_xboole_0(A_51, B_52))=k3_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.60/3.89  tff(c_187, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k3_xboole_0(A_51, B_52))=k3_xboole_0(A_51, k4_xboole_0(A_51, B_52)))), inference(superposition, [status(thm), theory('equality')], [c_184, c_18])).
% 9.60/3.89  tff(c_16397, plain, (k3_xboole_0('#skF_3', k4_xboole_0('#skF_3', '#skF_2'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_16297, c_187])).
% 9.60/3.89  tff(c_193, plain, (![A_51, B_52]: (r1_tarski(k3_xboole_0(A_51, B_52), A_51))), inference(superposition, [status(thm), theory('equality')], [c_184, c_16])).
% 9.60/3.89  tff(c_1309, plain, (![B_111, C_112, B_113]: (r1_xboole_0(k3_xboole_0(k4_xboole_0(B_111, C_112), B_113), C_112))), inference(resolution, [status(thm)], [c_193, c_258])).
% 9.60/3.89  tff(c_1361, plain, (![B_2, B_111, C_112]: (r1_xboole_0(k3_xboole_0(B_2, k4_xboole_0(B_111, C_112)), C_112))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1309])).
% 9.60/3.89  tff(c_16621, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_16397, c_1361])).
% 9.60/3.89  tff(c_16672, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3333, c_16621])).
% 9.60/3.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.60/3.89  
% 9.60/3.89  Inference rules
% 9.60/3.89  ----------------------
% 9.60/3.89  #Ref     : 0
% 9.60/3.89  #Sup     : 4090
% 9.60/3.89  #Fact    : 0
% 9.60/3.89  #Define  : 0
% 9.60/3.89  #Split   : 2
% 9.60/3.89  #Chain   : 0
% 9.60/3.89  #Close   : 0
% 9.60/3.89  
% 9.60/3.89  Ordering : KBO
% 9.60/3.89  
% 9.60/3.89  Simplification rules
% 9.82/3.89  ----------------------
% 9.82/3.89  #Subsume      : 133
% 9.82/3.89  #Demod        : 2329
% 9.82/3.89  #Tautology    : 2180
% 9.82/3.89  #SimpNegUnit  : 26
% 9.82/3.89  #BackRed      : 25
% 9.82/3.89  
% 9.82/3.89  #Partial instantiations: 0
% 9.82/3.89  #Strategies tried      : 1
% 9.82/3.89  
% 9.82/3.89  Timing (in seconds)
% 9.82/3.89  ----------------------
% 9.82/3.89  Preprocessing        : 0.32
% 9.82/3.89  Parsing              : 0.17
% 9.82/3.89  CNF conversion       : 0.02
% 9.82/3.89  Main loop            : 2.81
% 9.82/3.89  Inferencing          : 0.60
% 9.82/3.89  Reduction            : 1.36
% 9.82/3.89  Demodulation         : 1.13
% 9.82/3.89  BG Simplification    : 0.07
% 9.82/3.89  Subsumption          : 0.59
% 9.82/3.89  Abstraction          : 0.08
% 9.82/3.89  MUC search           : 0.00
% 9.82/3.89  Cooper               : 0.00
% 9.82/3.89  Total                : 3.17
% 9.82/3.89  Index Insertion      : 0.00
% 9.82/3.89  Index Deletion       : 0.00
% 9.82/3.89  Index Matching       : 0.00
% 9.82/3.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
