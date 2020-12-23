%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:46 EST 2020

% Result     : Theorem 27.78s
% Output     : CNFRefutation 27.78s
% Verified   : 
% Statistics : Number of formulae       :   61 (  70 expanded)
%              Number of leaves         :   29 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :  111 ( 143 expanded)
%              Number of equality atoms :   15 (  23 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_116,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_71,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_143,plain,(
    ! [A_49,B_50] :
      ( r2_hidden('#skF_1'(A_49,B_50),A_49)
      | r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_152,plain,(
    ! [A_49] : r1_tarski(A_49,A_49) ),
    inference(resolution,[status(thm)],[c_143,c_4])).

tff(c_50,plain,(
    r1_tarski('#skF_5',k2_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),A_6)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_163,plain,(
    ! [C_56,B_57,A_58] :
      ( r2_hidden(C_56,B_57)
      | ~ r2_hidden(C_56,A_58)
      | ~ r1_tarski(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_555,plain,(
    ! [A_119,B_120,B_121] :
      ( r2_hidden('#skF_2'(A_119,B_120),B_121)
      | ~ r1_tarski(A_119,B_121)
      | r1_xboole_0(A_119,B_120) ) ),
    inference(resolution,[status(thm)],[c_12,c_163])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_9284,plain,(
    ! [A_649,B_650,B_651,B_652] :
      ( r2_hidden('#skF_2'(A_649,B_650),B_651)
      | ~ r1_tarski(B_652,B_651)
      | ~ r1_tarski(A_649,B_652)
      | r1_xboole_0(A_649,B_650) ) ),
    inference(resolution,[status(thm)],[c_555,c_2])).

tff(c_9356,plain,(
    ! [A_649,B_650] :
      ( r2_hidden('#skF_2'(A_649,B_650),k2_relat_1('#skF_6'))
      | ~ r1_tarski(A_649,'#skF_5')
      | r1_xboole_0(A_649,B_650) ) ),
    inference(resolution,[status(thm)],[c_50,c_9284])).

tff(c_54,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_34,plain,(
    ! [A_22] :
      ( k9_relat_1(A_22,k1_relat_1(A_22)) = k2_relat_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_20,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_87,plain,(
    ! [A_35,B_36] : ~ r2_hidden(A_35,k2_zfmisc_1(A_35,B_36)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_90,plain,(
    ! [A_12] : ~ r2_hidden(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_87])).

tff(c_48,plain,(
    k10_relat_1('#skF_6','#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_30,plain,(
    ! [A_16,B_17,C_18] :
      ( r2_hidden(k4_tarski('#skF_3'(A_16,B_17,C_18),A_16),C_18)
      | ~ r2_hidden(A_16,k9_relat_1(C_18,B_17))
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_625,plain,(
    ! [A_127,C_128,B_129,D_130] :
      ( r2_hidden(A_127,k10_relat_1(C_128,B_129))
      | ~ r2_hidden(D_130,B_129)
      | ~ r2_hidden(k4_tarski(A_127,D_130),C_128)
      | ~ r2_hidden(D_130,k2_relat_1(C_128))
      | ~ v1_relat_1(C_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_4097,plain,(
    ! [A_364,C_365,B_366,A_367] :
      ( r2_hidden(A_364,k10_relat_1(C_365,B_366))
      | ~ r2_hidden(k4_tarski(A_364,'#skF_2'(A_367,B_366)),C_365)
      | ~ r2_hidden('#skF_2'(A_367,B_366),k2_relat_1(C_365))
      | ~ v1_relat_1(C_365)
      | r1_xboole_0(A_367,B_366) ) ),
    inference(resolution,[status(thm)],[c_10,c_625])).

tff(c_68539,plain,(
    ! [A_2290,B_2291,B_2292,C_2293] :
      ( r2_hidden('#skF_3'('#skF_2'(A_2290,B_2291),B_2292,C_2293),k10_relat_1(C_2293,B_2291))
      | ~ r2_hidden('#skF_2'(A_2290,B_2291),k2_relat_1(C_2293))
      | r1_xboole_0(A_2290,B_2291)
      | ~ r2_hidden('#skF_2'(A_2290,B_2291),k9_relat_1(C_2293,B_2292))
      | ~ v1_relat_1(C_2293) ) ),
    inference(resolution,[status(thm)],[c_30,c_4097])).

tff(c_68703,plain,(
    ! [A_2290,B_2292] :
      ( r2_hidden('#skF_3'('#skF_2'(A_2290,'#skF_5'),B_2292,'#skF_6'),k1_xboole_0)
      | ~ r2_hidden('#skF_2'(A_2290,'#skF_5'),k2_relat_1('#skF_6'))
      | r1_xboole_0(A_2290,'#skF_5')
      | ~ r2_hidden('#skF_2'(A_2290,'#skF_5'),k9_relat_1('#skF_6',B_2292))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_68539])).

tff(c_68759,plain,(
    ! [A_2290,B_2292] :
      ( r2_hidden('#skF_3'('#skF_2'(A_2290,'#skF_5'),B_2292,'#skF_6'),k1_xboole_0)
      | ~ r2_hidden('#skF_2'(A_2290,'#skF_5'),k2_relat_1('#skF_6'))
      | r1_xboole_0(A_2290,'#skF_5')
      | ~ r2_hidden('#skF_2'(A_2290,'#skF_5'),k9_relat_1('#skF_6',B_2292)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_68703])).

tff(c_70625,plain,(
    ! [A_2357,B_2358] :
      ( ~ r2_hidden('#skF_2'(A_2357,'#skF_5'),k2_relat_1('#skF_6'))
      | r1_xboole_0(A_2357,'#skF_5')
      | ~ r2_hidden('#skF_2'(A_2357,'#skF_5'),k9_relat_1('#skF_6',B_2358)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_68759])).

tff(c_70703,plain,(
    ! [A_2357] :
      ( ~ r2_hidden('#skF_2'(A_2357,'#skF_5'),k2_relat_1('#skF_6'))
      | r1_xboole_0(A_2357,'#skF_5')
      | ~ r2_hidden('#skF_2'(A_2357,'#skF_5'),k2_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_70625])).

tff(c_70746,plain,(
    ! [A_2359] :
      ( r1_xboole_0(A_2359,'#skF_5')
      | ~ r2_hidden('#skF_2'(A_2359,'#skF_5'),k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_70703])).

tff(c_70797,plain,(
    ! [A_2360] :
      ( ~ r1_tarski(A_2360,'#skF_5')
      | r1_xboole_0(A_2360,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_9356,c_70746])).

tff(c_16,plain,(
    ! [A_11] :
      ( ~ r1_xboole_0(A_11,A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_70803,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_70797,c_16])).

tff(c_70807,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_70803])).

tff(c_70809,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_70807])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:28:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 27.78/18.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.78/18.82  
% 27.78/18.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.78/18.82  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1
% 27.78/18.82  
% 27.78/18.82  %Foreground sorts:
% 27.78/18.82  
% 27.78/18.82  
% 27.78/18.82  %Background operators:
% 27.78/18.82  
% 27.78/18.82  
% 27.78/18.82  %Foreground operators:
% 27.78/18.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 27.78/18.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 27.78/18.82  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 27.78/18.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 27.78/18.82  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 27.78/18.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 27.78/18.82  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 27.78/18.82  tff('#skF_5', type, '#skF_5': $i).
% 27.78/18.82  tff('#skF_6', type, '#skF_6': $i).
% 27.78/18.82  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 27.78/18.82  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 27.78/18.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 27.78/18.82  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 27.78/18.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 27.78/18.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 27.78/18.82  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 27.78/18.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 27.78/18.82  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 27.78/18.82  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 27.78/18.82  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 27.78/18.82  
% 27.78/18.84  tff(f_116, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_relat_1)).
% 27.78/18.84  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 27.78/18.84  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 27.78/18.84  tff(f_86, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 27.78/18.84  tff(f_68, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 27.78/18.84  tff(f_71, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 27.78/18.84  tff(f_82, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 27.78/18.84  tff(f_97, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 27.78/18.84  tff(f_62, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 27.78/18.84  tff(c_52, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_116])).
% 27.78/18.84  tff(c_143, plain, (![A_49, B_50]: (r2_hidden('#skF_1'(A_49, B_50), A_49) | r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_32])).
% 27.78/18.84  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 27.78/18.84  tff(c_152, plain, (![A_49]: (r1_tarski(A_49, A_49))), inference(resolution, [status(thm)], [c_143, c_4])).
% 27.78/18.84  tff(c_50, plain, (r1_tarski('#skF_5', k2_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 27.78/18.84  tff(c_12, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), A_6) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 27.78/18.84  tff(c_163, plain, (![C_56, B_57, A_58]: (r2_hidden(C_56, B_57) | ~r2_hidden(C_56, A_58) | ~r1_tarski(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_32])).
% 27.78/18.84  tff(c_555, plain, (![A_119, B_120, B_121]: (r2_hidden('#skF_2'(A_119, B_120), B_121) | ~r1_tarski(A_119, B_121) | r1_xboole_0(A_119, B_120))), inference(resolution, [status(thm)], [c_12, c_163])).
% 27.78/18.84  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 27.78/18.84  tff(c_9284, plain, (![A_649, B_650, B_651, B_652]: (r2_hidden('#skF_2'(A_649, B_650), B_651) | ~r1_tarski(B_652, B_651) | ~r1_tarski(A_649, B_652) | r1_xboole_0(A_649, B_650))), inference(resolution, [status(thm)], [c_555, c_2])).
% 27.78/18.84  tff(c_9356, plain, (![A_649, B_650]: (r2_hidden('#skF_2'(A_649, B_650), k2_relat_1('#skF_6')) | ~r1_tarski(A_649, '#skF_5') | r1_xboole_0(A_649, B_650))), inference(resolution, [status(thm)], [c_50, c_9284])).
% 27.78/18.84  tff(c_54, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_116])).
% 27.78/18.84  tff(c_34, plain, (![A_22]: (k9_relat_1(A_22, k1_relat_1(A_22))=k2_relat_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_86])).
% 27.78/18.84  tff(c_20, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_68])).
% 27.78/18.84  tff(c_87, plain, (![A_35, B_36]: (~r2_hidden(A_35, k2_zfmisc_1(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 27.78/18.84  tff(c_90, plain, (![A_12]: (~r2_hidden(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_87])).
% 27.78/18.84  tff(c_48, plain, (k10_relat_1('#skF_6', '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_116])).
% 27.78/18.84  tff(c_30, plain, (![A_16, B_17, C_18]: (r2_hidden(k4_tarski('#skF_3'(A_16, B_17, C_18), A_16), C_18) | ~r2_hidden(A_16, k9_relat_1(C_18, B_17)) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_82])).
% 27.78/18.84  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 27.78/18.84  tff(c_625, plain, (![A_127, C_128, B_129, D_130]: (r2_hidden(A_127, k10_relat_1(C_128, B_129)) | ~r2_hidden(D_130, B_129) | ~r2_hidden(k4_tarski(A_127, D_130), C_128) | ~r2_hidden(D_130, k2_relat_1(C_128)) | ~v1_relat_1(C_128))), inference(cnfTransformation, [status(thm)], [f_97])).
% 27.78/18.84  tff(c_4097, plain, (![A_364, C_365, B_366, A_367]: (r2_hidden(A_364, k10_relat_1(C_365, B_366)) | ~r2_hidden(k4_tarski(A_364, '#skF_2'(A_367, B_366)), C_365) | ~r2_hidden('#skF_2'(A_367, B_366), k2_relat_1(C_365)) | ~v1_relat_1(C_365) | r1_xboole_0(A_367, B_366))), inference(resolution, [status(thm)], [c_10, c_625])).
% 27.78/18.84  tff(c_68539, plain, (![A_2290, B_2291, B_2292, C_2293]: (r2_hidden('#skF_3'('#skF_2'(A_2290, B_2291), B_2292, C_2293), k10_relat_1(C_2293, B_2291)) | ~r2_hidden('#skF_2'(A_2290, B_2291), k2_relat_1(C_2293)) | r1_xboole_0(A_2290, B_2291) | ~r2_hidden('#skF_2'(A_2290, B_2291), k9_relat_1(C_2293, B_2292)) | ~v1_relat_1(C_2293))), inference(resolution, [status(thm)], [c_30, c_4097])).
% 27.78/18.84  tff(c_68703, plain, (![A_2290, B_2292]: (r2_hidden('#skF_3'('#skF_2'(A_2290, '#skF_5'), B_2292, '#skF_6'), k1_xboole_0) | ~r2_hidden('#skF_2'(A_2290, '#skF_5'), k2_relat_1('#skF_6')) | r1_xboole_0(A_2290, '#skF_5') | ~r2_hidden('#skF_2'(A_2290, '#skF_5'), k9_relat_1('#skF_6', B_2292)) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_68539])).
% 27.78/18.84  tff(c_68759, plain, (![A_2290, B_2292]: (r2_hidden('#skF_3'('#skF_2'(A_2290, '#skF_5'), B_2292, '#skF_6'), k1_xboole_0) | ~r2_hidden('#skF_2'(A_2290, '#skF_5'), k2_relat_1('#skF_6')) | r1_xboole_0(A_2290, '#skF_5') | ~r2_hidden('#skF_2'(A_2290, '#skF_5'), k9_relat_1('#skF_6', B_2292)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_68703])).
% 27.78/18.84  tff(c_70625, plain, (![A_2357, B_2358]: (~r2_hidden('#skF_2'(A_2357, '#skF_5'), k2_relat_1('#skF_6')) | r1_xboole_0(A_2357, '#skF_5') | ~r2_hidden('#skF_2'(A_2357, '#skF_5'), k9_relat_1('#skF_6', B_2358)))), inference(negUnitSimplification, [status(thm)], [c_90, c_68759])).
% 27.78/18.84  tff(c_70703, plain, (![A_2357]: (~r2_hidden('#skF_2'(A_2357, '#skF_5'), k2_relat_1('#skF_6')) | r1_xboole_0(A_2357, '#skF_5') | ~r2_hidden('#skF_2'(A_2357, '#skF_5'), k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_70625])).
% 27.78/18.84  tff(c_70746, plain, (![A_2359]: (r1_xboole_0(A_2359, '#skF_5') | ~r2_hidden('#skF_2'(A_2359, '#skF_5'), k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_70703])).
% 27.78/18.84  tff(c_70797, plain, (![A_2360]: (~r1_tarski(A_2360, '#skF_5') | r1_xboole_0(A_2360, '#skF_5'))), inference(resolution, [status(thm)], [c_9356, c_70746])).
% 27.78/18.84  tff(c_16, plain, (![A_11]: (~r1_xboole_0(A_11, A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_62])).
% 27.78/18.84  tff(c_70803, plain, (k1_xboole_0='#skF_5' | ~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_70797, c_16])).
% 27.78/18.84  tff(c_70807, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_152, c_70803])).
% 27.78/18.84  tff(c_70809, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_70807])).
% 27.78/18.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.78/18.84  
% 27.78/18.84  Inference rules
% 27.78/18.84  ----------------------
% 27.78/18.84  #Ref     : 0
% 27.78/18.84  #Sup     : 17510
% 27.78/18.84  #Fact    : 0
% 27.78/18.84  #Define  : 0
% 27.78/18.84  #Split   : 12
% 27.78/18.84  #Chain   : 0
% 27.78/18.84  #Close   : 0
% 27.78/18.84  
% 27.78/18.84  Ordering : KBO
% 27.78/18.84  
% 27.78/18.84  Simplification rules
% 27.78/18.84  ----------------------
% 27.78/18.84  #Subsume      : 8905
% 27.78/18.84  #Demod        : 2445
% 27.78/18.84  #Tautology    : 1611
% 27.78/18.84  #SimpNegUnit  : 88
% 27.78/18.84  #BackRed      : 0
% 27.78/18.84  
% 27.78/18.84  #Partial instantiations: 0
% 27.78/18.84  #Strategies tried      : 1
% 27.78/18.84  
% 27.78/18.84  Timing (in seconds)
% 27.78/18.84  ----------------------
% 27.78/18.84  Preprocessing        : 0.36
% 27.78/18.84  Parsing              : 0.18
% 27.78/18.84  CNF conversion       : 0.03
% 27.78/18.84  Main loop            : 17.65
% 27.78/18.84  Inferencing          : 2.05
% 27.78/18.84  Reduction            : 2.15
% 27.78/18.84  Demodulation         : 1.37
% 27.78/18.84  BG Simplification    : 0.15
% 27.78/18.85  Subsumption          : 12.67
% 27.78/18.85  Abstraction          : 0.26
% 27.78/18.85  MUC search           : 0.00
% 27.78/18.85  Cooper               : 0.00
% 27.78/18.85  Total                : 18.05
% 27.78/18.85  Index Insertion      : 0.00
% 27.78/18.85  Index Deletion       : 0.00
% 27.78/18.85  Index Matching       : 0.00
% 27.78/18.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
