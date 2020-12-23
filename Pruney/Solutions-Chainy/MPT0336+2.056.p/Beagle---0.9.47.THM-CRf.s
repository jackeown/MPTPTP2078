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
% DateTime   : Thu Dec  3 09:55:08 EST 2020

% Result     : Theorem 3.91s
% Output     : CNFRefutation 3.91s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 133 expanded)
%              Number of leaves         :   31 (  58 expanded)
%              Depth                    :    8
%              Number of atoms          :  106 ( 212 expanded)
%              Number of equality atoms :   27 (  59 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_105,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_71,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

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

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_163,plain,(
    ! [A_53,B_54] :
      ( k3_xboole_0(A_53,B_54) = k1_xboole_0
      | ~ r1_xboole_0(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_175,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_163])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_214,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_2])).

tff(c_1401,plain,(
    ! [A_121,B_122,C_123] :
      ( k3_xboole_0(A_121,k2_xboole_0(B_122,C_123)) = k3_xboole_0(A_121,C_123)
      | ~ r1_xboole_0(A_121,B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_135,plain,(
    ! [A_47,B_48] :
      ( r1_xboole_0(A_47,B_48)
      | k3_xboole_0(A_47,B_48) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_138,plain,(
    k3_xboole_0(k2_xboole_0('#skF_3','#skF_5'),'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_135,c_38])).

tff(c_140,plain,(
    k3_xboole_0('#skF_4',k2_xboole_0('#skF_3','#skF_5')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_138])).

tff(c_1461,plain,
    ( k3_xboole_0('#skF_4','#skF_5') != k1_xboole_0
    | ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1401,c_140])).

tff(c_1507,plain,(
    ~ r1_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_1461])).

tff(c_1529,plain,(
    k3_xboole_0('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_1507])).

tff(c_18,plain,(
    ! [A_15,B_16] : r1_tarski(k3_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_22,plain,(
    ! [A_19] : r1_xboole_0(A_19,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1234,plain,(
    ! [A_111,B_112,C_113] :
      ( ~ r1_xboole_0(A_111,k3_xboole_0(B_112,C_113))
      | ~ r1_tarski(A_111,C_113)
      | r1_xboole_0(A_111,B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1284,plain,(
    ! [A_111] :
      ( ~ r1_xboole_0(A_111,k1_xboole_0)
      | ~ r1_tarski(A_111,'#skF_4')
      | r1_xboole_0(A_111,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_1234])).

tff(c_1318,plain,(
    ! [A_114] :
      ( ~ r1_tarski(A_114,'#skF_4')
      | r1_xboole_0(A_114,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1284])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1551,plain,(
    ! [A_125] :
      ( k3_xboole_0(A_125,'#skF_5') = k1_xboole_0
      | ~ r1_tarski(A_125,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1318,c_4])).

tff(c_1906,plain,(
    ! [B_133] : k3_xboole_0(k3_xboole_0('#skF_4',B_133),'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_1551])).

tff(c_1965,plain,(
    ! [B_133] : k3_xboole_0('#skF_5',k3_xboole_0('#skF_4',B_133)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1906,c_2])).

tff(c_34,plain,(
    ! [A_32,B_33] :
      ( r1_xboole_0(k1_tarski(A_32),B_33)
      | r2_hidden(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1070,plain,(
    ! [A_100,B_101] :
      ( r2_hidden('#skF_2'(A_100,B_101),k3_xboole_0(A_100,B_101))
      | r1_xboole_0(A_100,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_304,plain,(
    ! [A_62,B_63,C_64] :
      ( ~ r1_xboole_0(A_62,B_63)
      | ~ r2_hidden(C_64,k3_xboole_0(A_62,B_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_326,plain,(
    ! [B_2,A_1,C_64] :
      ( ~ r1_xboole_0(B_2,A_1)
      | ~ r2_hidden(C_64,k3_xboole_0(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_304])).

tff(c_1121,plain,(
    ! [B_102,A_103] :
      ( ~ r1_xboole_0(B_102,A_103)
      | r1_xboole_0(A_103,B_102) ) ),
    inference(resolution,[status(thm)],[c_1070,c_326])).

tff(c_1147,plain,(
    ! [B_33,A_32] :
      ( r1_xboole_0(B_33,k1_tarski(A_32))
      | r2_hidden(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_34,c_1121])).

tff(c_44,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_4'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_45,plain,(
    r1_tarski(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_44])).

tff(c_141,plain,(
    ! [A_49,B_50] :
      ( k3_xboole_0(A_49,B_50) = A_49
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_152,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_45,c_141])).

tff(c_332,plain,(
    ! [A_65,B_66] :
      ( r2_hidden('#skF_1'(A_65,B_66),B_66)
      | r1_xboole_0(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16,plain,(
    ! [A_10,B_11,C_14] :
      ( ~ r1_xboole_0(A_10,B_11)
      | ~ r2_hidden(C_14,k3_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_839,plain,(
    ! [A_90,B_91,A_92] :
      ( ~ r1_xboole_0(A_90,B_91)
      | r1_xboole_0(A_92,k3_xboole_0(A_90,B_91)) ) ),
    inference(resolution,[status(thm)],[c_332,c_16])).

tff(c_856,plain,(
    ! [A_92] :
      ( ~ r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6'))
      | r1_xboole_0(A_92,k3_xboole_0('#skF_4','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_839])).

tff(c_2036,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_tarski('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_856])).

tff(c_2063,plain,(
    r2_hidden('#skF_6',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1147,c_2036])).

tff(c_42,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_805,plain,(
    ! [A_86,B_87,C_88] :
      ( ~ r1_xboole_0(A_86,B_87)
      | ~ r2_hidden(C_88,B_87)
      | ~ r2_hidden(C_88,A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2360,plain,(
    ! [C_140,B_141,A_142] :
      ( ~ r2_hidden(C_140,B_141)
      | ~ r2_hidden(C_140,A_142)
      | k3_xboole_0(A_142,B_141) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_805])).

tff(c_2382,plain,(
    ! [A_143] :
      ( ~ r2_hidden('#skF_6',A_143)
      | k3_xboole_0(A_143,'#skF_5') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_42,c_2360])).

tff(c_2385,plain,(
    k3_xboole_0(k3_xboole_0('#skF_4','#skF_3'),'#skF_5') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2063,c_2382])).

tff(c_2392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1965,c_2,c_2385])).

tff(c_2395,plain,(
    ! [A_144] : r1_xboole_0(A_144,k3_xboole_0('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_856])).

tff(c_2409,plain,(
    ! [A_144] : k3_xboole_0(A_144,k3_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2395,c_4])).

tff(c_375,plain,(
    k3_xboole_0(k1_tarski('#skF_6'),k3_xboole_0('#skF_4','#skF_3')) = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_152])).

tff(c_2460,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2409,c_375])).

tff(c_2462,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1529,c_2460])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:25:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.91/1.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.69  
% 3.91/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.69  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.91/1.69  
% 3.91/1.69  %Foreground sorts:
% 3.91/1.69  
% 3.91/1.69  
% 3.91/1.69  %Background operators:
% 3.91/1.69  
% 3.91/1.69  
% 3.91/1.69  %Foreground operators:
% 3.91/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.91/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.91/1.69  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.91/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.91/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.91/1.69  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.91/1.69  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.91/1.69  tff('#skF_5', type, '#skF_5': $i).
% 3.91/1.69  tff('#skF_6', type, '#skF_6': $i).
% 3.91/1.69  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.91/1.69  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.91/1.69  tff('#skF_3', type, '#skF_3': $i).
% 3.91/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.91/1.69  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.91/1.69  tff('#skF_4', type, '#skF_4': $i).
% 3.91/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.91/1.69  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.91/1.69  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.91/1.69  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.91/1.69  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.91/1.69  
% 3.91/1.71  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.91/1.71  tff(f_105, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 3.91/1.71  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.91/1.71  tff(f_83, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_xboole_1)).
% 3.91/1.71  tff(f_65, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.91/1.71  tff(f_71, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.91/1.71  tff(f_79, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 3.91/1.71  tff(f_94, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.91/1.71  tff(f_63, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.91/1.71  tff(f_69, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.91/1.71  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.91/1.71  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.91/1.71  tff(c_40, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.91/1.71  tff(c_163, plain, (![A_53, B_54]: (k3_xboole_0(A_53, B_54)=k1_xboole_0 | ~r1_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.91/1.71  tff(c_175, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_163])).
% 3.91/1.71  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.91/1.71  tff(c_214, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_175, c_2])).
% 3.91/1.71  tff(c_1401, plain, (![A_121, B_122, C_123]: (k3_xboole_0(A_121, k2_xboole_0(B_122, C_123))=k3_xboole_0(A_121, C_123) | ~r1_xboole_0(A_121, B_122))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.91/1.71  tff(c_135, plain, (![A_47, B_48]: (r1_xboole_0(A_47, B_48) | k3_xboole_0(A_47, B_48)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.91/1.71  tff(c_38, plain, (~r1_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.91/1.71  tff(c_138, plain, (k3_xboole_0(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_135, c_38])).
% 3.91/1.71  tff(c_140, plain, (k3_xboole_0('#skF_4', k2_xboole_0('#skF_3', '#skF_5'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_138])).
% 3.91/1.71  tff(c_1461, plain, (k3_xboole_0('#skF_4', '#skF_5')!=k1_xboole_0 | ~r1_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1401, c_140])).
% 3.91/1.71  tff(c_1507, plain, (~r1_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_214, c_1461])).
% 3.91/1.71  tff(c_1529, plain, (k3_xboole_0('#skF_4', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_1507])).
% 3.91/1.71  tff(c_18, plain, (![A_15, B_16]: (r1_tarski(k3_xboole_0(A_15, B_16), A_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.91/1.71  tff(c_22, plain, (![A_19]: (r1_xboole_0(A_19, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.91/1.71  tff(c_1234, plain, (![A_111, B_112, C_113]: (~r1_xboole_0(A_111, k3_xboole_0(B_112, C_113)) | ~r1_tarski(A_111, C_113) | r1_xboole_0(A_111, B_112))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.91/1.71  tff(c_1284, plain, (![A_111]: (~r1_xboole_0(A_111, k1_xboole_0) | ~r1_tarski(A_111, '#skF_4') | r1_xboole_0(A_111, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_175, c_1234])).
% 3.91/1.71  tff(c_1318, plain, (![A_114]: (~r1_tarski(A_114, '#skF_4') | r1_xboole_0(A_114, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1284])).
% 3.91/1.71  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.91/1.71  tff(c_1551, plain, (![A_125]: (k3_xboole_0(A_125, '#skF_5')=k1_xboole_0 | ~r1_tarski(A_125, '#skF_4'))), inference(resolution, [status(thm)], [c_1318, c_4])).
% 3.91/1.71  tff(c_1906, plain, (![B_133]: (k3_xboole_0(k3_xboole_0('#skF_4', B_133), '#skF_5')=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_1551])).
% 3.91/1.71  tff(c_1965, plain, (![B_133]: (k3_xboole_0('#skF_5', k3_xboole_0('#skF_4', B_133))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1906, c_2])).
% 3.91/1.71  tff(c_34, plain, (![A_32, B_33]: (r1_xboole_0(k1_tarski(A_32), B_33) | r2_hidden(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.91/1.71  tff(c_1070, plain, (![A_100, B_101]: (r2_hidden('#skF_2'(A_100, B_101), k3_xboole_0(A_100, B_101)) | r1_xboole_0(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.91/1.71  tff(c_304, plain, (![A_62, B_63, C_64]: (~r1_xboole_0(A_62, B_63) | ~r2_hidden(C_64, k3_xboole_0(A_62, B_63)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.91/1.71  tff(c_326, plain, (![B_2, A_1, C_64]: (~r1_xboole_0(B_2, A_1) | ~r2_hidden(C_64, k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_304])).
% 3.91/1.71  tff(c_1121, plain, (![B_102, A_103]: (~r1_xboole_0(B_102, A_103) | r1_xboole_0(A_103, B_102))), inference(resolution, [status(thm)], [c_1070, c_326])).
% 3.91/1.71  tff(c_1147, plain, (![B_33, A_32]: (r1_xboole_0(B_33, k1_tarski(A_32)) | r2_hidden(A_32, B_33))), inference(resolution, [status(thm)], [c_34, c_1121])).
% 3.91/1.71  tff(c_44, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.91/1.71  tff(c_45, plain, (r1_tarski(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_44])).
% 3.91/1.71  tff(c_141, plain, (![A_49, B_50]: (k3_xboole_0(A_49, B_50)=A_49 | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.91/1.71  tff(c_152, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))=k3_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_45, c_141])).
% 3.91/1.71  tff(c_332, plain, (![A_65, B_66]: (r2_hidden('#skF_1'(A_65, B_66), B_66) | r1_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.91/1.71  tff(c_16, plain, (![A_10, B_11, C_14]: (~r1_xboole_0(A_10, B_11) | ~r2_hidden(C_14, k3_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.91/1.71  tff(c_839, plain, (![A_90, B_91, A_92]: (~r1_xboole_0(A_90, B_91) | r1_xboole_0(A_92, k3_xboole_0(A_90, B_91)))), inference(resolution, [status(thm)], [c_332, c_16])).
% 3.91/1.71  tff(c_856, plain, (![A_92]: (~r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6')) | r1_xboole_0(A_92, k3_xboole_0('#skF_4', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_152, c_839])).
% 3.91/1.71  tff(c_2036, plain, (~r1_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_tarski('#skF_6'))), inference(splitLeft, [status(thm)], [c_856])).
% 3.91/1.71  tff(c_2063, plain, (r2_hidden('#skF_6', k3_xboole_0('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_1147, c_2036])).
% 3.91/1.71  tff(c_42, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.91/1.71  tff(c_805, plain, (![A_86, B_87, C_88]: (~r1_xboole_0(A_86, B_87) | ~r2_hidden(C_88, B_87) | ~r2_hidden(C_88, A_86))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.91/1.71  tff(c_2360, plain, (![C_140, B_141, A_142]: (~r2_hidden(C_140, B_141) | ~r2_hidden(C_140, A_142) | k3_xboole_0(A_142, B_141)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_805])).
% 3.91/1.71  tff(c_2382, plain, (![A_143]: (~r2_hidden('#skF_6', A_143) | k3_xboole_0(A_143, '#skF_5')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_2360])).
% 3.91/1.71  tff(c_2385, plain, (k3_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), '#skF_5')!=k1_xboole_0), inference(resolution, [status(thm)], [c_2063, c_2382])).
% 3.91/1.71  tff(c_2392, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1965, c_2, c_2385])).
% 3.91/1.71  tff(c_2395, plain, (![A_144]: (r1_xboole_0(A_144, k3_xboole_0('#skF_4', '#skF_3')))), inference(splitRight, [status(thm)], [c_856])).
% 3.91/1.71  tff(c_2409, plain, (![A_144]: (k3_xboole_0(A_144, k3_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0)), inference(resolution, [status(thm)], [c_2395, c_4])).
% 3.91/1.71  tff(c_375, plain, (k3_xboole_0(k1_tarski('#skF_6'), k3_xboole_0('#skF_4', '#skF_3'))=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2, c_152])).
% 3.91/1.71  tff(c_2460, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2409, c_375])).
% 3.91/1.71  tff(c_2462, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1529, c_2460])).
% 3.91/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.71  
% 3.91/1.71  Inference rules
% 3.91/1.71  ----------------------
% 3.91/1.71  #Ref     : 0
% 3.91/1.71  #Sup     : 596
% 3.91/1.71  #Fact    : 0
% 3.91/1.71  #Define  : 0
% 3.91/1.71  #Split   : 1
% 3.91/1.71  #Chain   : 0
% 3.91/1.71  #Close   : 0
% 3.91/1.71  
% 3.91/1.71  Ordering : KBO
% 3.91/1.71  
% 3.91/1.71  Simplification rules
% 3.91/1.71  ----------------------
% 3.91/1.71  #Subsume      : 68
% 3.91/1.71  #Demod        : 379
% 3.91/1.71  #Tautology    : 302
% 3.91/1.71  #SimpNegUnit  : 21
% 3.91/1.71  #BackRed      : 1
% 3.91/1.71  
% 3.91/1.71  #Partial instantiations: 0
% 3.91/1.71  #Strategies tried      : 1
% 3.91/1.71  
% 3.91/1.71  Timing (in seconds)
% 3.91/1.71  ----------------------
% 3.91/1.71  Preprocessing        : 0.33
% 3.91/1.71  Parsing              : 0.18
% 3.91/1.71  CNF conversion       : 0.02
% 3.91/1.71  Main loop            : 0.60
% 3.91/1.71  Inferencing          : 0.19
% 3.91/1.71  Reduction            : 0.25
% 3.91/1.71  Demodulation         : 0.19
% 3.91/1.71  BG Simplification    : 0.02
% 3.91/1.71  Subsumption          : 0.10
% 3.91/1.71  Abstraction          : 0.03
% 3.91/1.71  MUC search           : 0.00
% 3.91/1.71  Cooper               : 0.00
% 3.91/1.71  Total                : 0.97
% 3.91/1.71  Index Insertion      : 0.00
% 3.91/1.71  Index Deletion       : 0.00
% 3.91/1.71  Index Matching       : 0.00
% 3.91/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
