%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:32 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 163 expanded)
%              Number of leaves         :   34 (  71 expanded)
%              Depth                    :    8
%              Number of atoms          :  106 ( 302 expanded)
%              Number of equality atoms :   12 (  36 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k1_enumset1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_11 > #skF_3 > #skF_10 > #skF_5 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_48,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_48,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_180,plain,(
    ! [A_76] :
      ( k2_xboole_0(k1_relat_1(A_76),k2_relat_1(A_76)) = k3_relat_1(A_76)
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,k2_xboole_0(C_8,B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_186,plain,(
    ! [A_6,A_76] :
      ( r1_tarski(A_6,k3_relat_1(A_76))
      | ~ r1_tarski(A_6,k2_relat_1(A_76))
      | ~ v1_relat_1(A_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_8])).

tff(c_42,plain,(
    ! [A_56] :
      ( k2_xboole_0(k1_relat_1(A_56),k2_relat_1(A_56)) = k3_relat_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_12,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_84,plain,(
    ! [A_60,B_61] : k3_tarski(k2_tarski(A_60,B_61)) = k2_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_108,plain,(
    ! [B_64,A_65] : k3_tarski(k2_tarski(B_64,A_65)) = k2_xboole_0(A_65,B_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_84])).

tff(c_16,plain,(
    ! [A_16,B_17] : k3_tarski(k2_tarski(A_16,B_17)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_114,plain,(
    ! [B_64,A_65] : k2_xboole_0(B_64,A_65) = k2_xboole_0(A_65,B_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_16])).

tff(c_166,plain,(
    ! [A_70,C_71,B_72] :
      ( r1_tarski(A_70,k2_xboole_0(C_71,B_72))
      | ~ r1_tarski(A_70,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_192,plain,(
    ! [A_77,B_78,A_79] :
      ( r1_tarski(A_77,k2_xboole_0(B_78,A_79))
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_166])).

tff(c_195,plain,(
    ! [A_77,A_56] :
      ( r1_tarski(A_77,k3_relat_1(A_56))
      | ~ r1_tarski(A_77,k1_relat_1(A_56))
      | ~ v1_relat_1(A_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_192])).

tff(c_50,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_222,plain,(
    ! [A_93,C_94,B_95] :
      ( r1_tarski(k2_xboole_0(A_93,C_94),B_95)
      | ~ r1_tarski(C_94,B_95)
      | ~ r1_tarski(A_93,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_275,plain,(
    ! [A_111,B_112] :
      ( r1_tarski(k3_relat_1(A_111),B_112)
      | ~ r1_tarski(k2_relat_1(A_111),B_112)
      | ~ r1_tarski(k1_relat_1(A_111),B_112)
      | ~ v1_relat_1(A_111) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_222])).

tff(c_44,plain,(
    ~ r1_tarski(k3_relat_1('#skF_10'),k3_relat_1('#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_284,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_10'),k3_relat_1('#skF_11'))
    | ~ r1_tarski(k1_relat_1('#skF_10'),k3_relat_1('#skF_11'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_275,c_44])).

tff(c_293,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_10'),k3_relat_1('#skF_11'))
    | ~ r1_tarski(k1_relat_1('#skF_10'),k3_relat_1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_284])).

tff(c_294,plain,(
    ~ r1_tarski(k1_relat_1('#skF_10'),k3_relat_1('#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_293])).

tff(c_298,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_10'),k1_relat_1('#skF_11'))
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_195,c_294])).

tff(c_304,plain,(
    ~ r1_tarski(k1_relat_1('#skF_10'),k1_relat_1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_298])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_46,plain,(
    r1_tarski('#skF_10','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_243,plain,(
    ! [C_103,A_104] :
      ( r2_hidden(k4_tarski(C_103,'#skF_5'(A_104,k1_relat_1(A_104),C_103)),A_104)
      | ~ r2_hidden(C_103,k1_relat_1(A_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_530,plain,(
    ! [C_160,A_161,B_162] :
      ( r2_hidden(k4_tarski(C_160,'#skF_5'(A_161,k1_relat_1(A_161),C_160)),B_162)
      | ~ r1_tarski(A_161,B_162)
      | ~ r2_hidden(C_160,k1_relat_1(A_161)) ) ),
    inference(resolution,[status(thm)],[c_243,c_2])).

tff(c_20,plain,(
    ! [C_33,A_18,D_36] :
      ( r2_hidden(C_33,k1_relat_1(A_18))
      | ~ r2_hidden(k4_tarski(C_33,D_36),A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_554,plain,(
    ! [C_165,B_166,A_167] :
      ( r2_hidden(C_165,k1_relat_1(B_166))
      | ~ r1_tarski(A_167,B_166)
      | ~ r2_hidden(C_165,k1_relat_1(A_167)) ) ),
    inference(resolution,[status(thm)],[c_530,c_20])).

tff(c_588,plain,(
    ! [C_168] :
      ( r2_hidden(C_168,k1_relat_1('#skF_11'))
      | ~ r2_hidden(C_168,k1_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_46,c_554])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_721,plain,(
    ! [A_174] :
      ( r1_tarski(A_174,k1_relat_1('#skF_11'))
      | ~ r2_hidden('#skF_1'(A_174,k1_relat_1('#skF_11')),k1_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_588,c_4])).

tff(c_733,plain,(
    r1_tarski(k1_relat_1('#skF_10'),k1_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_6,c_721])).

tff(c_739,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_304,c_304,c_733])).

tff(c_740,plain,(
    ~ r1_tarski(k2_relat_1('#skF_10'),k3_relat_1('#skF_11')) ),
    inference(splitRight,[status(thm)],[c_293])).

tff(c_747,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_10'),k2_relat_1('#skF_11'))
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_186,c_740])).

tff(c_753,plain,(
    ~ r1_tarski(k2_relat_1('#skF_10'),k2_relat_1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_747])).

tff(c_259,plain,(
    ! [A_107,C_108] :
      ( r2_hidden(k4_tarski('#skF_9'(A_107,k2_relat_1(A_107),C_108),C_108),A_107)
      | ~ r2_hidden(C_108,k2_relat_1(A_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1078,plain,(
    ! [A_237,C_238,B_239] :
      ( r2_hidden(k4_tarski('#skF_9'(A_237,k2_relat_1(A_237),C_238),C_238),B_239)
      | ~ r1_tarski(A_237,B_239)
      | ~ r2_hidden(C_238,k2_relat_1(A_237)) ) ),
    inference(resolution,[status(thm)],[c_259,c_2])).

tff(c_32,plain,(
    ! [C_52,A_37,D_55] :
      ( r2_hidden(C_52,k2_relat_1(A_37))
      | ~ r2_hidden(k4_tarski(D_55,C_52),A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1094,plain,(
    ! [C_240,B_241,A_242] :
      ( r2_hidden(C_240,k2_relat_1(B_241))
      | ~ r1_tarski(A_242,B_241)
      | ~ r2_hidden(C_240,k2_relat_1(A_242)) ) ),
    inference(resolution,[status(thm)],[c_1078,c_32])).

tff(c_1134,plain,(
    ! [C_243] :
      ( r2_hidden(C_243,k2_relat_1('#skF_11'))
      | ~ r2_hidden(C_243,k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_46,c_1094])).

tff(c_1295,plain,(
    ! [A_248] :
      ( r1_tarski(A_248,k2_relat_1('#skF_11'))
      | ~ r2_hidden('#skF_1'(A_248,k2_relat_1('#skF_11')),k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_1134,c_4])).

tff(c_1307,plain,(
    r1_tarski(k2_relat_1('#skF_10'),k2_relat_1('#skF_11')) ),
    inference(resolution,[status(thm)],[c_6,c_1295])).

tff(c_1313,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_753,c_753,c_1307])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:59:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.55/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.57  
% 3.55/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.57  %$ r2_hidden > r1_tarski > v1_relat_1 > k1_enumset1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_6 > #skF_11 > #skF_3 > #skF_10 > #skF_5 > #skF_8 > #skF_9 > #skF_2 > #skF_7 > #skF_1 > #skF_4
% 3.55/1.57  
% 3.55/1.57  %Foreground sorts:
% 3.55/1.57  
% 3.55/1.57  
% 3.55/1.57  %Background operators:
% 3.55/1.57  
% 3.55/1.57  
% 3.55/1.57  %Foreground operators:
% 3.55/1.57  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 3.55/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.55/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.55/1.57  tff('#skF_11', type, '#skF_11': $i).
% 3.55/1.57  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.55/1.57  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.55/1.57  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.55/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.55/1.57  tff('#skF_10', type, '#skF_10': $i).
% 3.55/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.55/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.55/1.57  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.55/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.55/1.57  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 3.55/1.57  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 3.55/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.55/1.57  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.55/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.55/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.55/1.57  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.55/1.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.55/1.57  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 3.55/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.55/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.55/1.57  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.55/1.57  
% 3.55/1.58  tff(f_78, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 3.55/1.58  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 3.55/1.58  tff(f_36, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 3.55/1.58  tff(f_44, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.55/1.58  tff(f_48, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.55/1.58  tff(f_42, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.55/1.58  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.55/1.58  tff(f_56, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 3.55/1.58  tff(f_64, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 3.55/1.58  tff(c_48, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.55/1.58  tff(c_180, plain, (![A_76]: (k2_xboole_0(k1_relat_1(A_76), k2_relat_1(A_76))=k3_relat_1(A_76) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.55/1.58  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, k2_xboole_0(C_8, B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.55/1.58  tff(c_186, plain, (![A_6, A_76]: (r1_tarski(A_6, k3_relat_1(A_76)) | ~r1_tarski(A_6, k2_relat_1(A_76)) | ~v1_relat_1(A_76))), inference(superposition, [status(thm), theory('equality')], [c_180, c_8])).
% 3.55/1.58  tff(c_42, plain, (![A_56]: (k2_xboole_0(k1_relat_1(A_56), k2_relat_1(A_56))=k3_relat_1(A_56) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.55/1.58  tff(c_12, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.55/1.58  tff(c_84, plain, (![A_60, B_61]: (k3_tarski(k2_tarski(A_60, B_61))=k2_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.55/1.58  tff(c_108, plain, (![B_64, A_65]: (k3_tarski(k2_tarski(B_64, A_65))=k2_xboole_0(A_65, B_64))), inference(superposition, [status(thm), theory('equality')], [c_12, c_84])).
% 3.55/1.58  tff(c_16, plain, (![A_16, B_17]: (k3_tarski(k2_tarski(A_16, B_17))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.55/1.58  tff(c_114, plain, (![B_64, A_65]: (k2_xboole_0(B_64, A_65)=k2_xboole_0(A_65, B_64))), inference(superposition, [status(thm), theory('equality')], [c_108, c_16])).
% 3.55/1.58  tff(c_166, plain, (![A_70, C_71, B_72]: (r1_tarski(A_70, k2_xboole_0(C_71, B_72)) | ~r1_tarski(A_70, B_72))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.55/1.58  tff(c_192, plain, (![A_77, B_78, A_79]: (r1_tarski(A_77, k2_xboole_0(B_78, A_79)) | ~r1_tarski(A_77, B_78))), inference(superposition, [status(thm), theory('equality')], [c_114, c_166])).
% 3.55/1.58  tff(c_195, plain, (![A_77, A_56]: (r1_tarski(A_77, k3_relat_1(A_56)) | ~r1_tarski(A_77, k1_relat_1(A_56)) | ~v1_relat_1(A_56))), inference(superposition, [status(thm), theory('equality')], [c_42, c_192])).
% 3.55/1.58  tff(c_50, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.55/1.58  tff(c_222, plain, (![A_93, C_94, B_95]: (r1_tarski(k2_xboole_0(A_93, C_94), B_95) | ~r1_tarski(C_94, B_95) | ~r1_tarski(A_93, B_95))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.55/1.58  tff(c_275, plain, (![A_111, B_112]: (r1_tarski(k3_relat_1(A_111), B_112) | ~r1_tarski(k2_relat_1(A_111), B_112) | ~r1_tarski(k1_relat_1(A_111), B_112) | ~v1_relat_1(A_111))), inference(superposition, [status(thm), theory('equality')], [c_42, c_222])).
% 3.55/1.58  tff(c_44, plain, (~r1_tarski(k3_relat_1('#skF_10'), k3_relat_1('#skF_11'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.55/1.58  tff(c_284, plain, (~r1_tarski(k2_relat_1('#skF_10'), k3_relat_1('#skF_11')) | ~r1_tarski(k1_relat_1('#skF_10'), k3_relat_1('#skF_11')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_275, c_44])).
% 3.55/1.58  tff(c_293, plain, (~r1_tarski(k2_relat_1('#skF_10'), k3_relat_1('#skF_11')) | ~r1_tarski(k1_relat_1('#skF_10'), k3_relat_1('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_284])).
% 3.55/1.58  tff(c_294, plain, (~r1_tarski(k1_relat_1('#skF_10'), k3_relat_1('#skF_11'))), inference(splitLeft, [status(thm)], [c_293])).
% 3.55/1.58  tff(c_298, plain, (~r1_tarski(k1_relat_1('#skF_10'), k1_relat_1('#skF_11')) | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_195, c_294])).
% 3.55/1.58  tff(c_304, plain, (~r1_tarski(k1_relat_1('#skF_10'), k1_relat_1('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_298])).
% 3.55/1.58  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.55/1.58  tff(c_46, plain, (r1_tarski('#skF_10', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.55/1.58  tff(c_243, plain, (![C_103, A_104]: (r2_hidden(k4_tarski(C_103, '#skF_5'(A_104, k1_relat_1(A_104), C_103)), A_104) | ~r2_hidden(C_103, k1_relat_1(A_104)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.55/1.58  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.55/1.58  tff(c_530, plain, (![C_160, A_161, B_162]: (r2_hidden(k4_tarski(C_160, '#skF_5'(A_161, k1_relat_1(A_161), C_160)), B_162) | ~r1_tarski(A_161, B_162) | ~r2_hidden(C_160, k1_relat_1(A_161)))), inference(resolution, [status(thm)], [c_243, c_2])).
% 3.55/1.58  tff(c_20, plain, (![C_33, A_18, D_36]: (r2_hidden(C_33, k1_relat_1(A_18)) | ~r2_hidden(k4_tarski(C_33, D_36), A_18))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.55/1.58  tff(c_554, plain, (![C_165, B_166, A_167]: (r2_hidden(C_165, k1_relat_1(B_166)) | ~r1_tarski(A_167, B_166) | ~r2_hidden(C_165, k1_relat_1(A_167)))), inference(resolution, [status(thm)], [c_530, c_20])).
% 3.55/1.58  tff(c_588, plain, (![C_168]: (r2_hidden(C_168, k1_relat_1('#skF_11')) | ~r2_hidden(C_168, k1_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_46, c_554])).
% 3.55/1.58  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.55/1.58  tff(c_721, plain, (![A_174]: (r1_tarski(A_174, k1_relat_1('#skF_11')) | ~r2_hidden('#skF_1'(A_174, k1_relat_1('#skF_11')), k1_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_588, c_4])).
% 3.55/1.58  tff(c_733, plain, (r1_tarski(k1_relat_1('#skF_10'), k1_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_6, c_721])).
% 3.55/1.58  tff(c_739, plain, $false, inference(negUnitSimplification, [status(thm)], [c_304, c_304, c_733])).
% 3.55/1.58  tff(c_740, plain, (~r1_tarski(k2_relat_1('#skF_10'), k3_relat_1('#skF_11'))), inference(splitRight, [status(thm)], [c_293])).
% 3.55/1.58  tff(c_747, plain, (~r1_tarski(k2_relat_1('#skF_10'), k2_relat_1('#skF_11')) | ~v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_186, c_740])).
% 3.55/1.58  tff(c_753, plain, (~r1_tarski(k2_relat_1('#skF_10'), k2_relat_1('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_747])).
% 3.55/1.58  tff(c_259, plain, (![A_107, C_108]: (r2_hidden(k4_tarski('#skF_9'(A_107, k2_relat_1(A_107), C_108), C_108), A_107) | ~r2_hidden(C_108, k2_relat_1(A_107)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.55/1.58  tff(c_1078, plain, (![A_237, C_238, B_239]: (r2_hidden(k4_tarski('#skF_9'(A_237, k2_relat_1(A_237), C_238), C_238), B_239) | ~r1_tarski(A_237, B_239) | ~r2_hidden(C_238, k2_relat_1(A_237)))), inference(resolution, [status(thm)], [c_259, c_2])).
% 3.55/1.58  tff(c_32, plain, (![C_52, A_37, D_55]: (r2_hidden(C_52, k2_relat_1(A_37)) | ~r2_hidden(k4_tarski(D_55, C_52), A_37))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.55/1.58  tff(c_1094, plain, (![C_240, B_241, A_242]: (r2_hidden(C_240, k2_relat_1(B_241)) | ~r1_tarski(A_242, B_241) | ~r2_hidden(C_240, k2_relat_1(A_242)))), inference(resolution, [status(thm)], [c_1078, c_32])).
% 3.55/1.58  tff(c_1134, plain, (![C_243]: (r2_hidden(C_243, k2_relat_1('#skF_11')) | ~r2_hidden(C_243, k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_46, c_1094])).
% 3.55/1.58  tff(c_1295, plain, (![A_248]: (r1_tarski(A_248, k2_relat_1('#skF_11')) | ~r2_hidden('#skF_1'(A_248, k2_relat_1('#skF_11')), k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_1134, c_4])).
% 3.55/1.58  tff(c_1307, plain, (r1_tarski(k2_relat_1('#skF_10'), k2_relat_1('#skF_11'))), inference(resolution, [status(thm)], [c_6, c_1295])).
% 3.55/1.58  tff(c_1313, plain, $false, inference(negUnitSimplification, [status(thm)], [c_753, c_753, c_1307])).
% 3.55/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.55/1.58  
% 3.55/1.58  Inference rules
% 3.55/1.58  ----------------------
% 3.55/1.58  #Ref     : 0
% 3.55/1.58  #Sup     : 312
% 3.55/1.58  #Fact    : 0
% 3.55/1.58  #Define  : 0
% 3.55/1.58  #Split   : 6
% 3.55/1.58  #Chain   : 0
% 3.55/1.58  #Close   : 0
% 3.55/1.58  
% 3.55/1.58  Ordering : KBO
% 3.55/1.58  
% 3.55/1.58  Simplification rules
% 3.55/1.58  ----------------------
% 3.55/1.58  #Subsume      : 52
% 3.55/1.58  #Demod        : 15
% 3.55/1.58  #Tautology    : 35
% 3.55/1.58  #SimpNegUnit  : 2
% 3.55/1.58  #BackRed      : 0
% 3.55/1.58  
% 3.55/1.58  #Partial instantiations: 0
% 3.55/1.58  #Strategies tried      : 1
% 3.55/1.58  
% 3.55/1.58  Timing (in seconds)
% 3.55/1.58  ----------------------
% 3.55/1.58  Preprocessing        : 0.31
% 3.55/1.59  Parsing              : 0.16
% 3.55/1.59  CNF conversion       : 0.03
% 3.55/1.59  Main loop            : 0.51
% 3.55/1.59  Inferencing          : 0.18
% 3.55/1.59  Reduction            : 0.14
% 3.55/1.59  Demodulation         : 0.10
% 3.55/1.59  BG Simplification    : 0.02
% 3.55/1.59  Subsumption          : 0.13
% 3.55/1.59  Abstraction          : 0.03
% 3.55/1.59  MUC search           : 0.00
% 3.55/1.59  Cooper               : 0.00
% 3.55/1.59  Total                : 0.85
% 3.55/1.59  Index Insertion      : 0.00
% 3.55/1.59  Index Deletion       : 0.00
% 3.55/1.59  Index Matching       : 0.00
% 3.55/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
