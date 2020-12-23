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
% DateTime   : Thu Dec  3 09:59:44 EST 2020

% Result     : Theorem 4.01s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 185 expanded)
%              Number of leaves         :   32 (  72 expanded)
%              Depth                    :   14
%              Number of atoms          :  142 ( 419 expanded)
%              Number of equality atoms :   16 (  50 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_108,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_101,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_51,axiom,(
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

tff(f_93,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_xboole_0(B) )
     => ( v1_xboole_0(k7_relat_1(A,B))
        & v1_relat_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc16_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_53,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_81,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_48,plain,
    ( k7_relat_1('#skF_3','#skF_2') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_75,plain,(
    r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_42,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2')
    | k7_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_97,plain,(
    k7_relat_1('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_42])).

tff(c_40,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(k7_relat_1(A_14,B_15))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28,plain,(
    ! [A_18] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_18)),A_18) = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_644,plain,(
    ! [A_112,B_113] :
      ( k5_relat_1(k6_relat_1(A_112),B_113) = k7_relat_1(B_113,A_112)
      | ~ v1_relat_1(B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_766,plain,(
    ! [A_117] :
      ( k7_relat_1(A_117,k1_relat_1(A_117)) = A_117
      | ~ v1_relat_1(A_117)
      | ~ v1_relat_1(A_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_644])).

tff(c_36,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_23,A_22)),k1_relat_1(B_23))
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_779,plain,(
    ! [A_117] :
      ( r1_tarski(k1_relat_1(A_117),k1_relat_1(A_117))
      | ~ v1_relat_1(A_117)
      | ~ v1_relat_1(A_117)
      | ~ v1_relat_1(A_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_766,c_36])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( r2_hidden('#skF_1'(A_4,B_5),B_5)
      | r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_808,plain,(
    ! [A_119,B_120,C_121] :
      ( r2_hidden(A_119,B_120)
      | ~ r2_hidden(A_119,k1_relat_1(k7_relat_1(C_121,B_120)))
      | ~ v1_relat_1(C_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_843,plain,(
    ! [A_4,C_121,B_120] :
      ( r2_hidden('#skF_1'(A_4,k1_relat_1(k7_relat_1(C_121,B_120))),B_120)
      | ~ v1_relat_1(C_121)
      | r1_xboole_0(A_4,k1_relat_1(k7_relat_1(C_121,B_120))) ) ),
    inference(resolution,[status(thm)],[c_8,c_808])).

tff(c_881,plain,(
    ! [A_125,C_126,B_127] :
      ( r2_hidden(A_125,k1_relat_1(C_126))
      | ~ r2_hidden(A_125,k1_relat_1(k7_relat_1(C_126,B_127)))
      | ~ v1_relat_1(C_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1638,plain,(
    ! [A_169,C_170,B_171] :
      ( r2_hidden('#skF_1'(A_169,k1_relat_1(k7_relat_1(C_170,B_171))),k1_relat_1(C_170))
      | ~ v1_relat_1(C_170)
      | r1_xboole_0(A_169,k1_relat_1(k7_relat_1(C_170,B_171))) ) ),
    inference(resolution,[status(thm)],[c_8,c_881])).

tff(c_607,plain,(
    ! [A_106,B_107,C_108] :
      ( ~ r1_xboole_0(A_106,B_107)
      | ~ r2_hidden(C_108,B_107)
      | ~ r2_hidden(C_108,A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_617,plain,(
    ! [C_108] :
      ( ~ r2_hidden(C_108,'#skF_2')
      | ~ r2_hidden(C_108,k1_relat_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_75,c_607])).

tff(c_1654,plain,(
    ! [A_169,B_171] :
      ( ~ r2_hidden('#skF_1'(A_169,k1_relat_1(k7_relat_1('#skF_3',B_171))),'#skF_2')
      | ~ v1_relat_1('#skF_3')
      | r1_xboole_0(A_169,k1_relat_1(k7_relat_1('#skF_3',B_171))) ) ),
    inference(resolution,[status(thm)],[c_1638,c_617])).

tff(c_1868,plain,(
    ! [A_177,B_178] :
      ( ~ r2_hidden('#skF_1'(A_177,k1_relat_1(k7_relat_1('#skF_3',B_178))),'#skF_2')
      | r1_xboole_0(A_177,k1_relat_1(k7_relat_1('#skF_3',B_178))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1654])).

tff(c_1876,plain,(
    ! [A_4] :
      ( ~ v1_relat_1('#skF_3')
      | r1_xboole_0(A_4,k1_relat_1(k7_relat_1('#skF_3','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_843,c_1868])).

tff(c_1908,plain,(
    ! [A_179] : r1_xboole_0(A_179,k1_relat_1(k7_relat_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1876])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( ~ r1_xboole_0(B_11,A_10)
      | ~ r1_tarski(B_11,A_10)
      | v1_xboole_0(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2109,plain,(
    ! [A_187] :
      ( ~ r1_tarski(A_187,k1_relat_1(k7_relat_1('#skF_3','#skF_2')))
      | v1_xboole_0(A_187) ) ),
    inference(resolution,[status(thm)],[c_1908,c_14])).

tff(c_2131,plain,
    ( v1_xboole_0(k1_relat_1(k7_relat_1('#skF_3','#skF_2')))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_779,c_2109])).

tff(c_2256,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2131])).

tff(c_2321,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_2256])).

tff(c_2325,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_2321])).

tff(c_2327,plain,(
    v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2131])).

tff(c_2326,plain,(
    v1_xboole_0(k1_relat_1(k7_relat_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_2131])).

tff(c_22,plain,(
    ! [A_16,B_17] :
      ( v1_xboole_0(k7_relat_1(A_16,B_17))
      | ~ v1_xboole_0(B_17)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_782,plain,(
    ! [A_117] :
      ( v1_xboole_0(A_117)
      | ~ v1_xboole_0(k1_relat_1(A_117))
      | ~ v1_relat_1(A_117)
      | ~ v1_relat_1(A_117)
      | ~ v1_relat_1(A_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_766,c_22])).

tff(c_2334,plain,
    ( v1_xboole_0(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2326,c_782])).

tff(c_2342,plain,(
    v1_xboole_0(k7_relat_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2327,c_2334])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2378,plain,(
    k7_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2342,c_2])).

tff(c_2383,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_97,c_2378])).

tff(c_2385,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r2_hidden('#skF_1'(A_4,B_5),A_4)
      | r1_xboole_0(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_69,plain,(
    ! [A_33,B_34] :
      ( ~ r2_hidden(A_33,B_34)
      | ~ r1_xboole_0(k1_tarski(A_33),B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_74,plain,(
    ! [A_33] : ~ r2_hidden(A_33,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_69])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2384,plain,(
    k7_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_2922,plain,(
    ! [A_242,C_243,B_244] :
      ( r2_hidden(A_242,k1_relat_1(k7_relat_1(C_243,B_244)))
      | ~ r2_hidden(A_242,k1_relat_1(C_243))
      | ~ r2_hidden(A_242,B_244)
      | ~ v1_relat_1(C_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2943,plain,(
    ! [A_242] :
      ( r2_hidden(A_242,k1_relat_1(k1_xboole_0))
      | ~ r2_hidden(A_242,k1_relat_1('#skF_3'))
      | ~ r2_hidden(A_242,'#skF_2')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2384,c_2922])).

tff(c_2955,plain,(
    ! [A_242] :
      ( r2_hidden(A_242,k1_xboole_0)
      | ~ r2_hidden(A_242,k1_relat_1('#skF_3'))
      | ~ r2_hidden(A_242,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_26,c_2943])).

tff(c_2957,plain,(
    ! [A_245] :
      ( ~ r2_hidden(A_245,k1_relat_1('#skF_3'))
      | ~ r2_hidden(A_245,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_2955])).

tff(c_2968,plain,(
    ! [A_246] :
      ( ~ r2_hidden('#skF_1'(A_246,k1_relat_1('#skF_3')),'#skF_2')
      | r1_xboole_0(A_246,k1_relat_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_8,c_2957])).

tff(c_2973,plain,(
    r1_xboole_0('#skF_2',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_10,c_2968])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( r1_xboole_0(B_3,A_2)
      | ~ r1_xboole_0(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2980,plain,(
    r1_xboole_0(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_2973,c_4])).

tff(c_2988,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2385,c_2980])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n010.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 12:27:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.01/1.73  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.74  
% 4.01/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.74  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.01/1.74  
% 4.01/1.74  %Foreground sorts:
% 4.01/1.74  
% 4.01/1.74  
% 4.01/1.74  %Background operators:
% 4.01/1.74  
% 4.01/1.74  
% 4.01/1.74  %Foreground operators:
% 4.01/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.01/1.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.01/1.74  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.01/1.74  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.01/1.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.01/1.74  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.01/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.01/1.74  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.01/1.74  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.01/1.74  tff('#skF_2', type, '#skF_2': $i).
% 4.01/1.74  tff('#skF_3', type, '#skF_3': $i).
% 4.01/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.01/1.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.01/1.74  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.01/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.01/1.74  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.01/1.74  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.01/1.74  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.01/1.74  
% 4.01/1.76  tff(f_108, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 4.01/1.76  tff(f_70, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 4.01/1.76  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 4.01/1.76  tff(f_101, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 4.01/1.76  tff(f_97, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_relat_1)).
% 4.01/1.76  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.01/1.76  tff(f_93, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 4.01/1.76  tff(f_61, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 4.01/1.76  tff(f_78, axiom, (![A, B]: ((v1_relat_1(A) & v1_xboole_0(B)) => (v1_xboole_0(k7_relat_1(A, B)) & v1_relat_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc16_relat_1)).
% 4.01/1.76  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.01/1.76  tff(f_53, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.01/1.76  tff(f_66, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 4.01/1.76  tff(f_81, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 4.01/1.76  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.01/1.76  tff(c_48, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.01/1.76  tff(c_75, plain, (r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_48])).
% 4.01/1.76  tff(c_42, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2') | k7_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.01/1.76  tff(c_97, plain, (k7_relat_1('#skF_3', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_75, c_42])).
% 4.01/1.76  tff(c_40, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.01/1.76  tff(c_18, plain, (![A_14, B_15]: (v1_relat_1(k7_relat_1(A_14, B_15)) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.01/1.76  tff(c_28, plain, (![A_18]: (k5_relat_1(k6_relat_1(k1_relat_1(A_18)), A_18)=A_18 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.01/1.76  tff(c_644, plain, (![A_112, B_113]: (k5_relat_1(k6_relat_1(A_112), B_113)=k7_relat_1(B_113, A_112) | ~v1_relat_1(B_113))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.01/1.76  tff(c_766, plain, (![A_117]: (k7_relat_1(A_117, k1_relat_1(A_117))=A_117 | ~v1_relat_1(A_117) | ~v1_relat_1(A_117))), inference(superposition, [status(thm), theory('equality')], [c_28, c_644])).
% 4.01/1.76  tff(c_36, plain, (![B_23, A_22]: (r1_tarski(k1_relat_1(k7_relat_1(B_23, A_22)), k1_relat_1(B_23)) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.01/1.76  tff(c_779, plain, (![A_117]: (r1_tarski(k1_relat_1(A_117), k1_relat_1(A_117)) | ~v1_relat_1(A_117) | ~v1_relat_1(A_117) | ~v1_relat_1(A_117))), inference(superposition, [status(thm), theory('equality')], [c_766, c_36])).
% 4.01/1.76  tff(c_8, plain, (![A_4, B_5]: (r2_hidden('#skF_1'(A_4, B_5), B_5) | r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.01/1.76  tff(c_808, plain, (![A_119, B_120, C_121]: (r2_hidden(A_119, B_120) | ~r2_hidden(A_119, k1_relat_1(k7_relat_1(C_121, B_120))) | ~v1_relat_1(C_121))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.01/1.76  tff(c_843, plain, (![A_4, C_121, B_120]: (r2_hidden('#skF_1'(A_4, k1_relat_1(k7_relat_1(C_121, B_120))), B_120) | ~v1_relat_1(C_121) | r1_xboole_0(A_4, k1_relat_1(k7_relat_1(C_121, B_120))))), inference(resolution, [status(thm)], [c_8, c_808])).
% 4.01/1.76  tff(c_881, plain, (![A_125, C_126, B_127]: (r2_hidden(A_125, k1_relat_1(C_126)) | ~r2_hidden(A_125, k1_relat_1(k7_relat_1(C_126, B_127))) | ~v1_relat_1(C_126))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.01/1.76  tff(c_1638, plain, (![A_169, C_170, B_171]: (r2_hidden('#skF_1'(A_169, k1_relat_1(k7_relat_1(C_170, B_171))), k1_relat_1(C_170)) | ~v1_relat_1(C_170) | r1_xboole_0(A_169, k1_relat_1(k7_relat_1(C_170, B_171))))), inference(resolution, [status(thm)], [c_8, c_881])).
% 4.01/1.76  tff(c_607, plain, (![A_106, B_107, C_108]: (~r1_xboole_0(A_106, B_107) | ~r2_hidden(C_108, B_107) | ~r2_hidden(C_108, A_106))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.01/1.76  tff(c_617, plain, (![C_108]: (~r2_hidden(C_108, '#skF_2') | ~r2_hidden(C_108, k1_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_75, c_607])).
% 4.01/1.76  tff(c_1654, plain, (![A_169, B_171]: (~r2_hidden('#skF_1'(A_169, k1_relat_1(k7_relat_1('#skF_3', B_171))), '#skF_2') | ~v1_relat_1('#skF_3') | r1_xboole_0(A_169, k1_relat_1(k7_relat_1('#skF_3', B_171))))), inference(resolution, [status(thm)], [c_1638, c_617])).
% 4.01/1.76  tff(c_1868, plain, (![A_177, B_178]: (~r2_hidden('#skF_1'(A_177, k1_relat_1(k7_relat_1('#skF_3', B_178))), '#skF_2') | r1_xboole_0(A_177, k1_relat_1(k7_relat_1('#skF_3', B_178))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1654])).
% 4.01/1.76  tff(c_1876, plain, (![A_4]: (~v1_relat_1('#skF_3') | r1_xboole_0(A_4, k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))))), inference(resolution, [status(thm)], [c_843, c_1868])).
% 4.01/1.76  tff(c_1908, plain, (![A_179]: (r1_xboole_0(A_179, k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1876])).
% 4.01/1.76  tff(c_14, plain, (![B_11, A_10]: (~r1_xboole_0(B_11, A_10) | ~r1_tarski(B_11, A_10) | v1_xboole_0(B_11))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.01/1.76  tff(c_2109, plain, (![A_187]: (~r1_tarski(A_187, k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))) | v1_xboole_0(A_187))), inference(resolution, [status(thm)], [c_1908, c_14])).
% 4.01/1.76  tff(c_2131, plain, (v1_xboole_0(k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_779, c_2109])).
% 4.01/1.76  tff(c_2256, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_2131])).
% 4.01/1.76  tff(c_2321, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_2256])).
% 4.01/1.76  tff(c_2325, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_2321])).
% 4.01/1.76  tff(c_2327, plain, (v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_2131])).
% 4.01/1.76  tff(c_2326, plain, (v1_xboole_0(k1_relat_1(k7_relat_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_2131])).
% 4.01/1.76  tff(c_22, plain, (![A_16, B_17]: (v1_xboole_0(k7_relat_1(A_16, B_17)) | ~v1_xboole_0(B_17) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.01/1.76  tff(c_782, plain, (![A_117]: (v1_xboole_0(A_117) | ~v1_xboole_0(k1_relat_1(A_117)) | ~v1_relat_1(A_117) | ~v1_relat_1(A_117) | ~v1_relat_1(A_117))), inference(superposition, [status(thm), theory('equality')], [c_766, c_22])).
% 4.01/1.76  tff(c_2334, plain, (v1_xboole_0(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_2326, c_782])).
% 4.01/1.76  tff(c_2342, plain, (v1_xboole_0(k7_relat_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2327, c_2334])).
% 4.01/1.76  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.01/1.76  tff(c_2378, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_2342, c_2])).
% 4.01/1.76  tff(c_2383, plain, $false, inference(negUnitSimplification, [status(thm)], [c_97, c_2378])).
% 4.01/1.76  tff(c_2385, plain, (~r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_48])).
% 4.01/1.76  tff(c_10, plain, (![A_4, B_5]: (r2_hidden('#skF_1'(A_4, B_5), A_4) | r1_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.01/1.76  tff(c_12, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.01/1.76  tff(c_69, plain, (![A_33, B_34]: (~r2_hidden(A_33, B_34) | ~r1_xboole_0(k1_tarski(A_33), B_34))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.01/1.76  tff(c_74, plain, (![A_33]: (~r2_hidden(A_33, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_69])).
% 4.01/1.76  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.01/1.76  tff(c_2384, plain, (k7_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 4.01/1.76  tff(c_2922, plain, (![A_242, C_243, B_244]: (r2_hidden(A_242, k1_relat_1(k7_relat_1(C_243, B_244))) | ~r2_hidden(A_242, k1_relat_1(C_243)) | ~r2_hidden(A_242, B_244) | ~v1_relat_1(C_243))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.01/1.76  tff(c_2943, plain, (![A_242]: (r2_hidden(A_242, k1_relat_1(k1_xboole_0)) | ~r2_hidden(A_242, k1_relat_1('#skF_3')) | ~r2_hidden(A_242, '#skF_2') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2384, c_2922])).
% 4.01/1.76  tff(c_2955, plain, (![A_242]: (r2_hidden(A_242, k1_xboole_0) | ~r2_hidden(A_242, k1_relat_1('#skF_3')) | ~r2_hidden(A_242, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_26, c_2943])).
% 4.01/1.76  tff(c_2957, plain, (![A_245]: (~r2_hidden(A_245, k1_relat_1('#skF_3')) | ~r2_hidden(A_245, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_74, c_2955])).
% 4.01/1.76  tff(c_2968, plain, (![A_246]: (~r2_hidden('#skF_1'(A_246, k1_relat_1('#skF_3')), '#skF_2') | r1_xboole_0(A_246, k1_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_8, c_2957])).
% 4.01/1.76  tff(c_2973, plain, (r1_xboole_0('#skF_2', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_10, c_2968])).
% 4.01/1.76  tff(c_4, plain, (![B_3, A_2]: (r1_xboole_0(B_3, A_2) | ~r1_xboole_0(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.01/1.76  tff(c_2980, plain, (r1_xboole_0(k1_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_2973, c_4])).
% 4.01/1.76  tff(c_2988, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2385, c_2980])).
% 4.01/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.76  
% 4.01/1.76  Inference rules
% 4.01/1.76  ----------------------
% 4.01/1.76  #Ref     : 0
% 4.01/1.76  #Sup     : 610
% 4.01/1.76  #Fact    : 0
% 4.01/1.76  #Define  : 0
% 4.01/1.76  #Split   : 16
% 4.01/1.76  #Chain   : 0
% 4.01/1.76  #Close   : 0
% 4.01/1.76  
% 4.01/1.76  Ordering : KBO
% 4.01/1.76  
% 4.01/1.76  Simplification rules
% 4.01/1.76  ----------------------
% 4.01/1.76  #Subsume      : 193
% 4.01/1.76  #Demod        : 633
% 4.01/1.76  #Tautology    : 248
% 4.01/1.76  #SimpNegUnit  : 68
% 4.01/1.76  #BackRed      : 17
% 4.01/1.76  
% 4.01/1.76  #Partial instantiations: 0
% 4.01/1.76  #Strategies tried      : 1
% 4.01/1.76  
% 4.01/1.76  Timing (in seconds)
% 4.01/1.76  ----------------------
% 4.01/1.76  Preprocessing        : 0.31
% 4.01/1.76  Parsing              : 0.18
% 4.01/1.76  CNF conversion       : 0.02
% 4.01/1.76  Main loop            : 0.65
% 4.01/1.76  Inferencing          : 0.24
% 4.01/1.76  Reduction            : 0.20
% 4.01/1.76  Demodulation         : 0.14
% 4.01/1.76  BG Simplification    : 0.03
% 4.01/1.76  Subsumption          : 0.14
% 4.01/1.76  Abstraction          : 0.03
% 4.01/1.76  MUC search           : 0.00
% 4.01/1.76  Cooper               : 0.00
% 4.01/1.76  Total                : 1.00
% 4.01/1.76  Index Insertion      : 0.00
% 4.01/1.76  Index Deletion       : 0.00
% 4.01/1.76  Index Matching       : 0.00
% 4.01/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
