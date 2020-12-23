%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:33 EST 2020

% Result     : Theorem 26.74s
% Output     : CNFRefutation 26.74s
% Verified   : 
% Statistics : Number of formulae       :  194 (4391 expanded)
%              Number of leaves         :   36 (1531 expanded)
%              Depth                    :   24
%              Number of atoms          :  529 (12906 expanded)
%              Number of equality atoms :   58 (1931 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    7 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_wellord1 > r2_hidden > r1_tarski > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k4_tarski > k2_xboole_0 > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(r4_wellord1,type,(
    r4_wellord1: ( $i * $i ) > $o )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_136,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r4_wellord1(k1_wellord2(A),k1_wellord2(B))
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).

tff(f_122,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v2_wellord1(k1_wellord2(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_60,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_56,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_109,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
           => r4_wellord1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

tff(f_126,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_107,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_118,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
           => A = k1_wellord1(k1_wellord2(B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
       => ! [B] :
            ~ ( r2_hidden(B,k3_relat_1(A))
              & r4_wellord1(A,k2_wellord1(A,k1_wellord1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k1_wellord1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( D != B
                & r2_hidden(k4_tarski(D,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

tff(c_72,plain,(
    v3_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_62,plain,(
    ! [A_41] :
      ( v2_wellord1(k1_wellord2(A_41))
      | ~ v3_ordinal1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_10,plain,(
    ! [B_6] : r2_hidden(B_6,k1_ordinal1(B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_66,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_16,plain,(
    ! [A_10] :
      ( v3_ordinal1(k1_ordinal1(A_10))
      | ~ v3_ordinal1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_70,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_14,plain,(
    ! [B_9,A_7] :
      ( r2_hidden(B_9,A_7)
      | B_9 = A_7
      | r2_hidden(A_7,B_9)
      | ~ v3_ordinal1(B_9)
      | ~ v3_ordinal1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_58,plain,(
    ! [A_37] : v1_relat_1(k1_wellord2(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_68,plain,(
    r4_wellord1(k1_wellord2('#skF_5'),k1_wellord2('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_122,plain,(
    ! [B_59,A_60] :
      ( r4_wellord1(B_59,A_60)
      | ~ r4_wellord1(A_60,B_59)
      | ~ v1_relat_1(B_59)
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_124,plain,
    ( r4_wellord1(k1_wellord2('#skF_6'),k1_wellord2('#skF_5'))
    | ~ v1_relat_1(k1_wellord2('#skF_6'))
    | ~ v1_relat_1(k1_wellord2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_68,c_122])).

tff(c_127,plain,(
    r4_wellord1(k1_wellord2('#skF_6'),k1_wellord2('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_58,c_124])).

tff(c_64,plain,(
    ! [B_43,A_42] :
      ( k2_wellord1(k1_wellord2(B_43),A_42) = k1_wellord2(A_42)
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_52,plain,(
    ! [A_29] :
      ( k3_relat_1(k1_wellord2(A_29)) = A_29
      | ~ v1_relat_1(k1_wellord2(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_78,plain,(
    ! [A_29] : k3_relat_1(k1_wellord2(A_29)) = A_29 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_52])).

tff(c_60,plain,(
    ! [B_40,A_38] :
      ( k1_wellord1(k1_wellord2(B_40),A_38) = A_38
      | ~ r2_hidden(A_38,B_40)
      | ~ v3_ordinal1(B_40)
      | ~ v3_ordinal1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_590,plain,(
    ! [A_111,B_112] :
      ( ~ r4_wellord1(A_111,k2_wellord1(A_111,k1_wellord1(A_111,B_112)))
      | ~ r2_hidden(B_112,k3_relat_1(A_111))
      | ~ v2_wellord1(A_111)
      | ~ v1_relat_1(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_593,plain,(
    ! [B_40,A_38] :
      ( ~ r4_wellord1(k1_wellord2(B_40),k2_wellord1(k1_wellord2(B_40),A_38))
      | ~ r2_hidden(A_38,k3_relat_1(k1_wellord2(B_40)))
      | ~ v2_wellord1(k1_wellord2(B_40))
      | ~ v1_relat_1(k1_wellord2(B_40))
      | ~ r2_hidden(A_38,B_40)
      | ~ v3_ordinal1(B_40)
      | ~ v3_ordinal1(A_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_590])).

tff(c_2003,plain,(
    ! [B_183,A_184] :
      ( ~ r4_wellord1(k1_wellord2(B_183),k2_wellord1(k1_wellord2(B_183),A_184))
      | ~ v2_wellord1(k1_wellord2(B_183))
      | ~ r2_hidden(A_184,B_183)
      | ~ v3_ordinal1(B_183)
      | ~ v3_ordinal1(A_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_78,c_593])).

tff(c_3354,plain,(
    ! [B_229,A_230] :
      ( ~ r4_wellord1(k1_wellord2(B_229),k1_wellord2(A_230))
      | ~ v2_wellord1(k1_wellord2(B_229))
      | ~ r2_hidden(A_230,B_229)
      | ~ v3_ordinal1(B_229)
      | ~ v3_ordinal1(A_230)
      | ~ r1_tarski(A_230,B_229) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_2003])).

tff(c_3357,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_6'))
    | ~ r2_hidden('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5')
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_127,c_3354])).

tff(c_3363,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_6'))
    | ~ r2_hidden('#skF_5','#skF_6')
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_3357])).

tff(c_3367,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_3363])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden(A_5,B_6)
      | r2_hidden(A_5,k1_ordinal1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [D_22,B_18,A_11] :
      ( r2_hidden(k4_tarski(D_22,B_18),A_11)
      | ~ r2_hidden(D_22,k1_wellord1(A_11,B_18))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_56,plain,(
    ! [C_35,D_36,A_29] :
      ( r1_tarski(C_35,D_36)
      | ~ r2_hidden(k4_tarski(C_35,D_36),k1_wellord2(A_29))
      | ~ r2_hidden(D_36,A_29)
      | ~ r2_hidden(C_35,A_29)
      | ~ v1_relat_1(k1_wellord2(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_719,plain,(
    ! [C_119,D_120,A_121] :
      ( r1_tarski(C_119,D_120)
      | ~ r2_hidden(k4_tarski(C_119,D_120),k1_wellord2(A_121))
      | ~ r2_hidden(D_120,A_121)
      | ~ r2_hidden(C_119,A_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56])).

tff(c_732,plain,(
    ! [D_22,B_18,A_121] :
      ( r1_tarski(D_22,B_18)
      | ~ r2_hidden(B_18,A_121)
      | ~ r2_hidden(D_22,A_121)
      | ~ r2_hidden(D_22,k1_wellord1(k1_wellord2(A_121),B_18))
      | ~ v1_relat_1(k1_wellord2(A_121)) ) ),
    inference(resolution,[status(thm)],[c_20,c_719])).

tff(c_894,plain,(
    ! [D_130,B_131,A_132] :
      ( r1_tarski(D_130,B_131)
      | ~ r2_hidden(B_131,A_132)
      | ~ r2_hidden(D_130,A_132)
      | ~ r2_hidden(D_130,k1_wellord1(k1_wellord2(A_132),B_131)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_732])).

tff(c_35156,plain,(
    ! [D_568,A_569,B_570] :
      ( r1_tarski(D_568,A_569)
      | ~ r2_hidden(A_569,B_570)
      | ~ r2_hidden(D_568,B_570)
      | ~ r2_hidden(D_568,A_569)
      | ~ r2_hidden(A_569,B_570)
      | ~ v3_ordinal1(B_570)
      | ~ v3_ordinal1(A_569) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_894])).

tff(c_35264,plain,(
    ! [D_568,B_6] :
      ( r1_tarski(D_568,B_6)
      | ~ r2_hidden(D_568,k1_ordinal1(B_6))
      | ~ r2_hidden(D_568,B_6)
      | ~ r2_hidden(B_6,k1_ordinal1(B_6))
      | ~ v3_ordinal1(k1_ordinal1(B_6))
      | ~ v3_ordinal1(B_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_35156])).

tff(c_35321,plain,(
    ! [D_571,B_572] :
      ( r1_tarski(D_571,B_572)
      | ~ r2_hidden(D_571,k1_ordinal1(B_572))
      | ~ r2_hidden(D_571,B_572)
      | ~ v3_ordinal1(k1_ordinal1(B_572))
      | ~ v3_ordinal1(B_572) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_35264])).

tff(c_35446,plain,(
    ! [A_573,B_574] :
      ( r1_tarski(A_573,B_574)
      | ~ v3_ordinal1(k1_ordinal1(B_574))
      | ~ v3_ordinal1(B_574)
      | ~ r2_hidden(A_573,B_574) ) ),
    inference(resolution,[status(thm)],[c_12,c_35321])).

tff(c_35450,plain,(
    ! [A_575,A_576] :
      ( r1_tarski(A_575,A_576)
      | ~ r2_hidden(A_575,A_576)
      | ~ v3_ordinal1(A_576) ) ),
    inference(resolution,[status(thm)],[c_16,c_35446])).

tff(c_36087,plain,(
    ! [A_583,B_584] :
      ( r1_tarski(A_583,B_584)
      | r2_hidden(B_584,A_583)
      | B_584 = A_583
      | ~ v3_ordinal1(B_584)
      | ~ v3_ordinal1(A_583) ) ),
    inference(resolution,[status(thm)],[c_14,c_35450])).

tff(c_3360,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_5'))
    | ~ r2_hidden('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6')
    | ~ r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_3354])).

tff(c_3366,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_5'))
    | ~ r2_hidden('#skF_6','#skF_5')
    | ~ r1_tarski('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_72,c_3360])).

tff(c_3368,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3366])).

tff(c_20104,plain,(
    ! [D_400,A_401,B_402] :
      ( r1_tarski(D_400,A_401)
      | ~ r2_hidden(A_401,B_402)
      | ~ r2_hidden(D_400,B_402)
      | ~ r2_hidden(D_400,A_401)
      | ~ r2_hidden(A_401,B_402)
      | ~ v3_ordinal1(B_402)
      | ~ v3_ordinal1(A_401) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_894])).

tff(c_20216,plain,(
    ! [D_400,B_6] :
      ( r1_tarski(D_400,B_6)
      | ~ r2_hidden(D_400,k1_ordinal1(B_6))
      | ~ r2_hidden(D_400,B_6)
      | ~ r2_hidden(B_6,k1_ordinal1(B_6))
      | ~ v3_ordinal1(k1_ordinal1(B_6))
      | ~ v3_ordinal1(B_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_20104])).

tff(c_20275,plain,(
    ! [D_403,B_404] :
      ( r1_tarski(D_403,B_404)
      | ~ r2_hidden(D_403,k1_ordinal1(B_404))
      | ~ r2_hidden(D_403,B_404)
      | ~ v3_ordinal1(k1_ordinal1(B_404))
      | ~ v3_ordinal1(B_404) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_20216])).

tff(c_20405,plain,(
    ! [A_405,B_406] :
      ( r1_tarski(A_405,B_406)
      | ~ v3_ordinal1(k1_ordinal1(B_406))
      | ~ v3_ordinal1(B_406)
      | ~ r2_hidden(A_405,B_406) ) ),
    inference(resolution,[status(thm)],[c_12,c_20275])).

tff(c_20409,plain,(
    ! [A_407,A_408] :
      ( r1_tarski(A_407,A_408)
      | ~ r2_hidden(A_407,A_408)
      | ~ v3_ordinal1(A_408) ) ),
    inference(resolution,[status(thm)],[c_16,c_20405])).

tff(c_20800,plain,(
    ! [A_413,B_414] :
      ( r1_tarski(A_413,B_414)
      | r2_hidden(B_414,A_413)
      | B_414 = A_413
      | ~ v3_ordinal1(B_414)
      | ~ v3_ordinal1(A_413) ) ),
    inference(resolution,[status(thm)],[c_14,c_20409])).

tff(c_20408,plain,(
    ! [A_405,A_10] :
      ( r1_tarski(A_405,A_10)
      | ~ r2_hidden(A_405,A_10)
      | ~ v3_ordinal1(A_10) ) ),
    inference(resolution,[status(thm)],[c_16,c_20405])).

tff(c_21102,plain,(
    ! [B_416,A_417] :
      ( r1_tarski(B_416,A_417)
      | r1_tarski(A_417,B_416)
      | B_416 = A_417
      | ~ v3_ordinal1(B_416)
      | ~ v3_ordinal1(A_417) ) ),
    inference(resolution,[status(thm)],[c_20800,c_20408])).

tff(c_21109,plain,
    ( r1_tarski('#skF_6','#skF_5')
    | '#skF_5' = '#skF_6'
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_21102,c_3367])).

tff(c_21120,plain,
    ( r1_tarski('#skF_6','#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_72,c_21109])).

tff(c_21122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_3368,c_21120])).

tff(c_21123,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | ~ v2_wellord1(k1_wellord2('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_3366])).

tff(c_21125,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_21123])).

tff(c_21206,plain,(
    ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_21125])).

tff(c_21210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_21206])).

tff(c_21211,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_21123])).

tff(c_36154,plain,
    ( r1_tarski('#skF_5','#skF_6')
    | '#skF_5' = '#skF_6'
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_36087,c_21211])).

tff(c_36317,plain,
    ( r1_tarski('#skF_5','#skF_6')
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_36154])).

tff(c_36319,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_3367,c_36317])).

tff(c_36320,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | ~ v2_wellord1(k1_wellord2('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_3363])).

tff(c_36323,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_36320])).

tff(c_36326,plain,(
    ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_36323])).

tff(c_36330,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_36326])).

tff(c_36331,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_36320])).

tff(c_36338,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | '#skF_5' = '#skF_6'
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_36331])).

tff(c_36345,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_36338])).

tff(c_36346,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_36345])).

tff(c_169,plain,(
    ! [D_69,B_70,A_71] :
      ( r2_hidden(k4_tarski(D_69,B_70),A_71)
      | ~ r2_hidden(D_69,k1_wellord1(A_71,B_70))
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4,plain,(
    ! [A_1,C_3,B_2] :
      ( r2_hidden(A_1,k3_relat_1(C_3))
      | ~ r2_hidden(k4_tarski(A_1,B_2),C_3)
      | ~ v1_relat_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_197,plain,(
    ! [D_74,A_75,B_76] :
      ( r2_hidden(D_74,k3_relat_1(A_75))
      | ~ r2_hidden(D_74,k1_wellord1(A_75,B_76))
      | ~ v1_relat_1(A_75) ) ),
    inference(resolution,[status(thm)],[c_169,c_4])).

tff(c_204,plain,(
    ! [D_74,B_40,A_38] :
      ( r2_hidden(D_74,k3_relat_1(k1_wellord2(B_40)))
      | ~ r2_hidden(D_74,A_38)
      | ~ v1_relat_1(k1_wellord2(B_40))
      | ~ r2_hidden(A_38,B_40)
      | ~ v3_ordinal1(B_40)
      | ~ v3_ordinal1(A_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_197])).

tff(c_528,plain,(
    ! [D_106,B_107,A_108] :
      ( r2_hidden(D_106,B_107)
      | ~ r2_hidden(D_106,A_108)
      | ~ r2_hidden(A_108,B_107)
      | ~ v3_ordinal1(B_107)
      | ~ v3_ordinal1(A_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_78,c_204])).

tff(c_1084,plain,(
    ! [A_148,B_149,B_150] :
      ( r2_hidden(A_148,B_149)
      | ~ r2_hidden(k1_ordinal1(B_150),B_149)
      | ~ v3_ordinal1(B_149)
      | ~ v3_ordinal1(k1_ordinal1(B_150))
      | ~ r2_hidden(A_148,B_150) ) ),
    inference(resolution,[status(thm)],[c_12,c_528])).

tff(c_1127,plain,(
    ! [A_148,B_6,B_150] :
      ( r2_hidden(A_148,k1_ordinal1(B_6))
      | ~ v3_ordinal1(k1_ordinal1(B_6))
      | ~ v3_ordinal1(k1_ordinal1(B_150))
      | ~ r2_hidden(A_148,B_150)
      | ~ r2_hidden(k1_ordinal1(B_150),B_6) ) ),
    inference(resolution,[status(thm)],[c_12,c_1084])).

tff(c_36431,plain,(
    ! [B_6] :
      ( r2_hidden('#skF_6',k1_ordinal1(B_6))
      | ~ v3_ordinal1(k1_ordinal1(B_6))
      | ~ v3_ordinal1(k1_ordinal1('#skF_5'))
      | ~ r2_hidden(k1_ordinal1('#skF_5'),B_6) ) ),
    inference(resolution,[status(thm)],[c_36346,c_1127])).

tff(c_36439,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_36431])).

tff(c_36442,plain,(
    ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_36439])).

tff(c_36446,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_36442])).

tff(c_36448,plain,(
    v3_ordinal1(k1_ordinal1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_36431])).

tff(c_559,plain,(
    ! [B_109,B_110] :
      ( r2_hidden(B_109,B_110)
      | ~ r2_hidden(k1_ordinal1(B_109),B_110)
      | ~ v3_ordinal1(B_110)
      | ~ v3_ordinal1(k1_ordinal1(B_109)) ) ),
    inference(resolution,[status(thm)],[c_10,c_528])).

tff(c_1129,plain,(
    ! [B_151,B_152] :
      ( r2_hidden(B_151,B_152)
      | r2_hidden(B_152,k1_ordinal1(B_151))
      | k1_ordinal1(B_151) = B_152
      | ~ v3_ordinal1(B_152)
      | ~ v3_ordinal1(k1_ordinal1(B_151)) ) ),
    inference(resolution,[status(thm)],[c_14,c_559])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( B_6 = A_5
      | r2_hidden(A_5,B_6)
      | ~ r2_hidden(A_5,k1_ordinal1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1212,plain,(
    ! [B_152,B_151] :
      ( B_152 = B_151
      | r2_hidden(B_152,B_151)
      | r2_hidden(B_151,B_152)
      | k1_ordinal1(B_151) = B_152
      | ~ v3_ordinal1(B_152)
      | ~ v3_ordinal1(k1_ordinal1(B_151)) ) ),
    inference(resolution,[status(thm)],[c_1129,c_8])).

tff(c_37854,plain,(
    ! [B_602] :
      ( B_602 = '#skF_5'
      | r2_hidden(B_602,'#skF_5')
      | r2_hidden('#skF_5',B_602)
      | k1_ordinal1('#skF_5') = B_602
      | ~ v3_ordinal1(B_602) ) ),
    inference(resolution,[status(thm)],[c_36448,c_1212])).

tff(c_558,plain,(
    ! [B_6,B_107] :
      ( r2_hidden(B_6,B_107)
      | ~ r2_hidden(k1_ordinal1(B_6),B_107)
      | ~ v3_ordinal1(B_107)
      | ~ v3_ordinal1(k1_ordinal1(B_6)) ) ),
    inference(resolution,[status(thm)],[c_10,c_528])).

tff(c_37930,plain,(
    ! [B_6] :
      ( r2_hidden(B_6,'#skF_5')
      | ~ v3_ordinal1('#skF_5')
      | k1_ordinal1(B_6) = '#skF_5'
      | r2_hidden('#skF_5',k1_ordinal1(B_6))
      | k1_ordinal1(B_6) = k1_ordinal1('#skF_5')
      | ~ v3_ordinal1(k1_ordinal1(B_6)) ) ),
    inference(resolution,[status(thm)],[c_37854,c_558])).

tff(c_94966,plain,(
    ! [B_837] :
      ( r2_hidden(B_837,'#skF_5')
      | k1_ordinal1(B_837) = '#skF_5'
      | r2_hidden('#skF_5',k1_ordinal1(B_837))
      | k1_ordinal1(B_837) = k1_ordinal1('#skF_5')
      | ~ v3_ordinal1(k1_ordinal1(B_837)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_37930])).

tff(c_555,plain,(
    ! [A_7,B_107,B_9] :
      ( r2_hidden(A_7,B_107)
      | ~ r2_hidden(B_9,B_107)
      | ~ v3_ordinal1(B_107)
      | r2_hidden(B_9,A_7)
      | B_9 = A_7
      | ~ v3_ordinal1(B_9)
      | ~ v3_ordinal1(A_7) ) ),
    inference(resolution,[status(thm)],[c_14,c_528])).

tff(c_36428,plain,(
    ! [A_7] :
      ( r2_hidden(A_7,'#skF_5')
      | ~ v3_ordinal1('#skF_5')
      | r2_hidden('#skF_6',A_7)
      | A_7 = '#skF_6'
      | ~ v3_ordinal1('#skF_6')
      | ~ v3_ordinal1(A_7) ) ),
    inference(resolution,[status(thm)],[c_36346,c_555])).

tff(c_36630,plain,(
    ! [A_591] :
      ( r2_hidden(A_591,'#skF_5')
      | r2_hidden('#skF_6',A_591)
      | A_591 = '#skF_6'
      | ~ v3_ordinal1(A_591) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_72,c_36428])).

tff(c_207,plain,(
    ! [D_74,B_40,A_38] :
      ( r2_hidden(D_74,B_40)
      | ~ r2_hidden(D_74,A_38)
      | ~ r2_hidden(A_38,B_40)
      | ~ v3_ordinal1(B_40)
      | ~ v3_ordinal1(A_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_78,c_204])).

tff(c_40177,plain,(
    ! [B_618,A_619] :
      ( r2_hidden('#skF_6',B_618)
      | ~ r2_hidden(A_619,B_618)
      | ~ v3_ordinal1(B_618)
      | r2_hidden(A_619,'#skF_5')
      | A_619 = '#skF_6'
      | ~ v3_ordinal1(A_619) ) ),
    inference(resolution,[status(thm)],[c_36630,c_207])).

tff(c_40392,plain,(
    ! [B_6,A_5] :
      ( r2_hidden('#skF_6',k1_ordinal1(B_6))
      | ~ v3_ordinal1(k1_ordinal1(B_6))
      | r2_hidden(A_5,'#skF_5')
      | A_5 = '#skF_6'
      | ~ v3_ordinal1(A_5)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(resolution,[status(thm)],[c_12,c_40177])).

tff(c_94968,plain,(
    ! [B_837] :
      ( r2_hidden('#skF_6',k1_ordinal1(k1_ordinal1(B_837)))
      | ~ v3_ordinal1(k1_ordinal1(k1_ordinal1(B_837)))
      | r2_hidden('#skF_5','#skF_5')
      | '#skF_5' = '#skF_6'
      | ~ v3_ordinal1('#skF_5')
      | r2_hidden(B_837,'#skF_5')
      | k1_ordinal1(B_837) = '#skF_5'
      | k1_ordinal1(B_837) = k1_ordinal1('#skF_5')
      | ~ v3_ordinal1(k1_ordinal1(B_837)) ) ),
    inference(resolution,[status(thm)],[c_94966,c_40392])).

tff(c_94997,plain,(
    ! [B_837] :
      ( r2_hidden('#skF_6',k1_ordinal1(k1_ordinal1(B_837)))
      | ~ v3_ordinal1(k1_ordinal1(k1_ordinal1(B_837)))
      | r2_hidden('#skF_5','#skF_5')
      | '#skF_5' = '#skF_6'
      | r2_hidden(B_837,'#skF_5')
      | k1_ordinal1(B_837) = '#skF_5'
      | k1_ordinal1(B_837) = k1_ordinal1('#skF_5')
      | ~ v3_ordinal1(k1_ordinal1(B_837)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_94968])).

tff(c_94998,plain,(
    ! [B_837] :
      ( r2_hidden('#skF_6',k1_ordinal1(k1_ordinal1(B_837)))
      | ~ v3_ordinal1(k1_ordinal1(k1_ordinal1(B_837)))
      | r2_hidden('#skF_5','#skF_5')
      | r2_hidden(B_837,'#skF_5')
      | k1_ordinal1(B_837) = '#skF_5'
      | k1_ordinal1(B_837) = k1_ordinal1('#skF_5')
      | ~ v3_ordinal1(k1_ordinal1(B_837)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_94997])).

tff(c_96239,plain,(
    r2_hidden('#skF_5','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_94998])).

tff(c_155,plain,(
    ! [B_67,A_68] :
      ( k1_wellord1(k1_wellord2(B_67),A_68) = A_68
      | ~ r2_hidden(A_68,B_67)
      | ~ v3_ordinal1(B_67)
      | ~ v3_ordinal1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_22,plain,(
    ! [D_22,A_11] :
      ( ~ r2_hidden(D_22,k1_wellord1(A_11,D_22))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_161,plain,(
    ! [A_68,B_67] :
      ( ~ r2_hidden(A_68,A_68)
      | ~ v1_relat_1(k1_wellord2(B_67))
      | ~ r2_hidden(A_68,B_67)
      | ~ v3_ordinal1(B_67)
      | ~ v3_ordinal1(A_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_22])).

tff(c_167,plain,(
    ! [A_68,B_67] :
      ( ~ r2_hidden(A_68,A_68)
      | ~ r2_hidden(A_68,B_67)
      | ~ v3_ordinal1(B_67)
      | ~ v3_ordinal1(A_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_161])).

tff(c_96266,plain,(
    ! [B_67] :
      ( ~ r2_hidden('#skF_5',B_67)
      | ~ v3_ordinal1(B_67)
      | ~ v3_ordinal1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_96239,c_167])).

tff(c_96309,plain,(
    ! [B_841] :
      ( ~ r2_hidden('#skF_5',B_841)
      | ~ v3_ordinal1(B_841) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_96266])).

tff(c_96312,plain,(
    ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_96239,c_96309])).

tff(c_96755,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_96312])).

tff(c_96757,plain,(
    ~ r2_hidden('#skF_5','#skF_5') ),
    inference(splitRight,[status(thm)],[c_94998])).

tff(c_36322,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_3366])).

tff(c_589,plain,(
    ! [B_109] :
      ( r2_hidden(B_109,k1_ordinal1(k1_ordinal1(B_109)))
      | ~ v3_ordinal1(k1_ordinal1(k1_ordinal1(B_109)))
      | ~ v3_ordinal1(k1_ordinal1(B_109)) ) ),
    inference(resolution,[status(thm)],[c_10,c_559])).

tff(c_36430,plain,(
    ! [B_40] :
      ( r2_hidden('#skF_6',B_40)
      | ~ r2_hidden('#skF_5',B_40)
      | ~ v3_ordinal1(B_40)
      | ~ v3_ordinal1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36346,c_207])).

tff(c_36452,plain,(
    ! [B_588] :
      ( r2_hidden('#skF_6',B_588)
      | ~ r2_hidden('#skF_5',B_588)
      | ~ v3_ordinal1(B_588) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_36430])).

tff(c_36512,plain,
    ( r2_hidden('#skF_6',k1_ordinal1(k1_ordinal1('#skF_5')))
    | ~ v3_ordinal1(k1_ordinal1(k1_ordinal1('#skF_5')))
    | ~ v3_ordinal1(k1_ordinal1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_589,c_36452])).

tff(c_36563,plain,
    ( r2_hidden('#skF_6',k1_ordinal1(k1_ordinal1('#skF_5')))
    | ~ v3_ordinal1(k1_ordinal1(k1_ordinal1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36448,c_36512])).

tff(c_36595,plain,(
    ~ v3_ordinal1(k1_ordinal1(k1_ordinal1('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_36563])).

tff(c_36602,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_16,c_36595])).

tff(c_36606,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36448,c_36602])).

tff(c_36608,plain,(
    v3_ordinal1(k1_ordinal1(k1_ordinal1('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_36563])).

tff(c_94049,plain,(
    ! [B_834,A_835] :
      ( r2_hidden('#skF_6',k1_ordinal1(B_834))
      | ~ v3_ordinal1(k1_ordinal1(B_834))
      | r2_hidden(A_835,'#skF_5')
      | A_835 = '#skF_6'
      | ~ v3_ordinal1(A_835)
      | ~ r2_hidden(A_835,B_834) ) ),
    inference(resolution,[status(thm)],[c_12,c_40177])).

tff(c_94920,plain,(
    ! [B_6] :
      ( r2_hidden('#skF_6',k1_ordinal1(k1_ordinal1(B_6)))
      | ~ v3_ordinal1(k1_ordinal1(k1_ordinal1(B_6)))
      | r2_hidden(B_6,'#skF_5')
      | B_6 = '#skF_6'
      | ~ v3_ordinal1(B_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_94049])).

tff(c_739,plain,(
    ! [B_122,B_123] :
      ( r2_hidden(B_122,k1_ordinal1(B_123))
      | ~ v3_ordinal1(k1_ordinal1(B_123))
      | ~ v3_ordinal1(k1_ordinal1(B_122))
      | ~ r2_hidden(k1_ordinal1(B_122),B_123) ) ),
    inference(resolution,[status(thm)],[c_12,c_559])).

tff(c_784,plain,(
    ! [B_122] :
      ( r2_hidden(B_122,k1_ordinal1(k1_ordinal1(k1_ordinal1(B_122))))
      | ~ v3_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(B_122))))
      | ~ v3_ordinal1(k1_ordinal1(B_122)) ) ),
    inference(resolution,[status(thm)],[c_10,c_739])).

tff(c_36500,plain,
    ( r2_hidden('#skF_6',k1_ordinal1(k1_ordinal1(k1_ordinal1('#skF_5'))))
    | ~ v3_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1('#skF_5'))))
    | ~ v3_ordinal1(k1_ordinal1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_784,c_36452])).

tff(c_36558,plain,
    ( r2_hidden('#skF_6',k1_ordinal1(k1_ordinal1(k1_ordinal1('#skF_5'))))
    | ~ v3_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36448,c_36500])).

tff(c_37451,plain,(
    ~ v3_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1('#skF_5')))) ),
    inference(splitLeft,[status(thm)],[c_36558])).

tff(c_37454,plain,(
    ~ v3_ordinal1(k1_ordinal1(k1_ordinal1('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_16,c_37451])).

tff(c_37458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36608,c_37454])).

tff(c_37460,plain,(
    v3_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1('#skF_5')))) ),
    inference(splitRight,[status(thm)],[c_36558])).

tff(c_785,plain,(
    ! [B_124] :
      ( r2_hidden(B_124,k1_ordinal1(k1_ordinal1(k1_ordinal1(B_124))))
      | ~ v3_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(B_124))))
      | ~ v3_ordinal1(k1_ordinal1(B_124)) ) ),
    inference(resolution,[status(thm)],[c_10,c_739])).

tff(c_825,plain,(
    ! [B_124] :
      ( k1_ordinal1(k1_ordinal1(B_124)) = B_124
      | r2_hidden(B_124,k1_ordinal1(k1_ordinal1(B_124)))
      | ~ v3_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(B_124))))
      | ~ v3_ordinal1(k1_ordinal1(B_124)) ) ),
    inference(resolution,[status(thm)],[c_785,c_8])).

tff(c_37475,plain,
    ( k1_ordinal1(k1_ordinal1('#skF_5')) = '#skF_5'
    | r2_hidden('#skF_5',k1_ordinal1(k1_ordinal1('#skF_5')))
    | ~ v3_ordinal1(k1_ordinal1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_37460,c_825])).

tff(c_37480,plain,
    ( k1_ordinal1(k1_ordinal1('#skF_5')) = '#skF_5'
    | r2_hidden('#skF_5',k1_ordinal1(k1_ordinal1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36448,c_37475])).

tff(c_37807,plain,(
    r2_hidden('#skF_5',k1_ordinal1(k1_ordinal1('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_37480])).

tff(c_106260,plain,(
    ! [D_900,A_901,B_902] :
      ( r1_tarski(D_900,A_901)
      | ~ r2_hidden(A_901,B_902)
      | ~ r2_hidden(D_900,B_902)
      | ~ r2_hidden(D_900,A_901)
      | ~ r2_hidden(A_901,B_902)
      | ~ v3_ordinal1(B_902)
      | ~ v3_ordinal1(A_901) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_894])).

tff(c_106582,plain,(
    ! [D_900] :
      ( r1_tarski(D_900,'#skF_5')
      | ~ r2_hidden(D_900,k1_ordinal1(k1_ordinal1('#skF_5')))
      | ~ r2_hidden(D_900,'#skF_5')
      | ~ r2_hidden('#skF_5',k1_ordinal1(k1_ordinal1('#skF_5')))
      | ~ v3_ordinal1(k1_ordinal1(k1_ordinal1('#skF_5')))
      | ~ v3_ordinal1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_37807,c_106260])).

tff(c_108831,plain,(
    ! [D_911] :
      ( r1_tarski(D_911,'#skF_5')
      | ~ r2_hidden(D_911,k1_ordinal1(k1_ordinal1('#skF_5')))
      | ~ r2_hidden(D_911,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_36608,c_37807,c_106582])).

tff(c_108882,plain,
    ( r1_tarski('#skF_6','#skF_5')
    | ~ r2_hidden('#skF_6','#skF_5')
    | ~ v3_ordinal1(k1_ordinal1(k1_ordinal1('#skF_5')))
    | r2_hidden('#skF_5','#skF_5')
    | '#skF_5' = '#skF_6'
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_94920,c_108831])).

tff(c_109163,plain,
    ( r1_tarski('#skF_6','#skF_5')
    | r2_hidden('#skF_5','#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_36608,c_36346,c_108882])).

tff(c_109165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_96757,c_36322,c_109163])).

tff(c_109166,plain,(
    k1_ordinal1(k1_ordinal1('#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_37480])).

tff(c_188,plain,(
    ! [A_72,B_73] :
      ( ~ r2_hidden(A_72,A_72)
      | ~ r2_hidden(A_72,B_73)
      | ~ v3_ordinal1(B_73)
      | ~ v3_ordinal1(A_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_161])).

tff(c_423,plain,(
    ! [B_97,B_98] :
      ( ~ r2_hidden(k1_ordinal1(B_97),B_98)
      | ~ v3_ordinal1(B_98)
      | ~ v3_ordinal1(k1_ordinal1(B_97))
      | ~ r2_hidden(k1_ordinal1(B_97),B_97) ) ),
    inference(resolution,[status(thm)],[c_12,c_188])).

tff(c_448,plain,(
    ! [B_99] :
      ( ~ v3_ordinal1(k1_ordinal1(k1_ordinal1(B_99)))
      | ~ v3_ordinal1(k1_ordinal1(B_99))
      | ~ r2_hidden(k1_ordinal1(B_99),B_99) ) ),
    inference(resolution,[status(thm)],[c_10,c_423])).

tff(c_453,plain,(
    ! [B_100] :
      ( ~ r2_hidden(k1_ordinal1(B_100),B_100)
      | ~ v3_ordinal1(k1_ordinal1(B_100)) ) ),
    inference(resolution,[status(thm)],[c_16,c_448])).

tff(c_471,plain,(
    ! [B_101] :
      ( ~ v3_ordinal1(k1_ordinal1(k1_ordinal1(B_101)))
      | ~ r2_hidden(k1_ordinal1(k1_ordinal1(B_101)),B_101) ) ),
    inference(resolution,[status(thm)],[c_12,c_453])).

tff(c_512,plain,(
    ! [B_105] :
      ( ~ v3_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(B_105))))
      | ~ r2_hidden(k1_ordinal1(k1_ordinal1(k1_ordinal1(B_105))),B_105) ) ),
    inference(resolution,[status(thm)],[c_12,c_471])).

tff(c_639,plain,(
    ! [B_114] :
      ( ~ v3_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(B_114)))))
      | ~ r2_hidden(k1_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(B_114)))),B_114) ) ),
    inference(resolution,[status(thm)],[c_12,c_512])).

tff(c_654,plain,(
    ! [B_6] :
      ( ~ v3_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(B_6))))))
      | ~ r2_hidden(k1_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(B_6))))),B_6) ) ),
    inference(resolution,[status(thm)],[c_12,c_639])).

tff(c_109231,plain,
    ( ~ v3_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1('#skF_5')))))))
    | ~ r2_hidden(k1_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1('#skF_5')))),k1_ordinal1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_109166,c_654])).

tff(c_109341,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_109166,c_109166,c_72,c_109166,c_109166,c_109166,c_109231])).

tff(c_109342,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | ~ v2_wellord1(k1_wellord2('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_3366])).

tff(c_109344,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_109342])).

tff(c_109347,plain,(
    ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_109344])).

tff(c_109351,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_109347])).

tff(c_109352,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_109342])).

tff(c_109434,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_36320])).

tff(c_109437,plain,(
    ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_109434])).

tff(c_109441,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_109437])).

tff(c_109442,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_36320])).

tff(c_109446,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_14,c_109442])).

tff(c_109452,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_72,c_109446])).

tff(c_109454,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109352,c_66,c_109452])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:22:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 26.74/16.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 26.74/16.38  
% 26.74/16.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 26.74/16.38  %$ r4_wellord1 > r2_hidden > r1_tarski > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k4_tarski > k2_xboole_0 > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 26.74/16.38  
% 26.74/16.38  %Foreground sorts:
% 26.74/16.38  
% 26.74/16.38  
% 26.74/16.38  %Background operators:
% 26.74/16.38  
% 26.74/16.38  
% 26.74/16.38  %Foreground operators:
% 26.74/16.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 26.74/16.38  tff(r4_wellord1, type, r4_wellord1: ($i * $i) > $o).
% 26.74/16.38  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 26.74/16.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 26.74/16.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 26.74/16.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 26.74/16.38  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 26.74/16.38  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 26.74/16.38  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 26.74/16.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 26.74/16.38  tff('#skF_5', type, '#skF_5': $i).
% 26.74/16.38  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 26.74/16.38  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 26.74/16.38  tff('#skF_6', type, '#skF_6': $i).
% 26.74/16.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 26.74/16.38  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 26.74/16.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 26.74/16.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 26.74/16.38  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 26.74/16.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 26.74/16.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 26.74/16.38  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 26.74/16.38  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 26.74/16.38  
% 26.74/16.41  tff(f_136, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r4_wellord1(k1_wellord2(A), k1_wellord2(B)) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_wellord2)).
% 26.74/16.41  tff(f_122, axiom, (![A]: (v3_ordinal1(A) => v2_wellord1(k1_wellord2(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_wellord2)).
% 26.74/16.41  tff(f_41, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 26.74/16.41  tff(f_60, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 26.74/16.41  tff(f_56, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 26.74/16.41  tff(f_109, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 26.74/16.41  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r4_wellord1(A, B) => r4_wellord1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_wellord1)).
% 26.74/16.41  tff(f_126, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_wellord2)).
% 26.74/16.41  tff(f_107, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 26.74/16.41  tff(f_118, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) => (A = k1_wellord1(k1_wellord2(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_wellord2)).
% 26.74/16.41  tff(f_92, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) => (![B]: ~(r2_hidden(B, k3_relat_1(A)) & r4_wellord1(A, k2_wellord1(A, k1_wellord1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_wellord1)).
% 26.74/16.41  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k1_wellord1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (~(D = B) & r2_hidden(k4_tarski(D, B), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord1)).
% 26.74/16.41  tff(f_33, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relat_1)).
% 26.74/16.41  tff(c_72, plain, (v3_ordinal1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_136])).
% 26.74/16.41  tff(c_62, plain, (![A_41]: (v2_wellord1(k1_wellord2(A_41)) | ~v3_ordinal1(A_41))), inference(cnfTransformation, [status(thm)], [f_122])).
% 26.74/16.41  tff(c_10, plain, (![B_6]: (r2_hidden(B_6, k1_ordinal1(B_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 26.74/16.41  tff(c_66, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_136])).
% 26.74/16.41  tff(c_16, plain, (![A_10]: (v3_ordinal1(k1_ordinal1(A_10)) | ~v3_ordinal1(A_10))), inference(cnfTransformation, [status(thm)], [f_60])).
% 26.74/16.41  tff(c_70, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_136])).
% 26.74/16.41  tff(c_14, plain, (![B_9, A_7]: (r2_hidden(B_9, A_7) | B_9=A_7 | r2_hidden(A_7, B_9) | ~v3_ordinal1(B_9) | ~v3_ordinal1(A_7))), inference(cnfTransformation, [status(thm)], [f_56])).
% 26.74/16.41  tff(c_58, plain, (![A_37]: (v1_relat_1(k1_wellord2(A_37)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 26.74/16.41  tff(c_68, plain, (r4_wellord1(k1_wellord2('#skF_5'), k1_wellord2('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 26.74/16.41  tff(c_122, plain, (![B_59, A_60]: (r4_wellord1(B_59, A_60) | ~r4_wellord1(A_60, B_59) | ~v1_relat_1(B_59) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_82])).
% 26.74/16.41  tff(c_124, plain, (r4_wellord1(k1_wellord2('#skF_6'), k1_wellord2('#skF_5')) | ~v1_relat_1(k1_wellord2('#skF_6')) | ~v1_relat_1(k1_wellord2('#skF_5'))), inference(resolution, [status(thm)], [c_68, c_122])).
% 26.74/16.41  tff(c_127, plain, (r4_wellord1(k1_wellord2('#skF_6'), k1_wellord2('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_58, c_124])).
% 26.74/16.41  tff(c_64, plain, (![B_43, A_42]: (k2_wellord1(k1_wellord2(B_43), A_42)=k1_wellord2(A_42) | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_126])).
% 26.74/16.41  tff(c_52, plain, (![A_29]: (k3_relat_1(k1_wellord2(A_29))=A_29 | ~v1_relat_1(k1_wellord2(A_29)))), inference(cnfTransformation, [status(thm)], [f_107])).
% 26.74/16.41  tff(c_78, plain, (![A_29]: (k3_relat_1(k1_wellord2(A_29))=A_29)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_52])).
% 26.74/16.41  tff(c_60, plain, (![B_40, A_38]: (k1_wellord1(k1_wellord2(B_40), A_38)=A_38 | ~r2_hidden(A_38, B_40) | ~v3_ordinal1(B_40) | ~v3_ordinal1(A_38))), inference(cnfTransformation, [status(thm)], [f_118])).
% 26.74/16.41  tff(c_590, plain, (![A_111, B_112]: (~r4_wellord1(A_111, k2_wellord1(A_111, k1_wellord1(A_111, B_112))) | ~r2_hidden(B_112, k3_relat_1(A_111)) | ~v2_wellord1(A_111) | ~v1_relat_1(A_111))), inference(cnfTransformation, [status(thm)], [f_92])).
% 26.74/16.41  tff(c_593, plain, (![B_40, A_38]: (~r4_wellord1(k1_wellord2(B_40), k2_wellord1(k1_wellord2(B_40), A_38)) | ~r2_hidden(A_38, k3_relat_1(k1_wellord2(B_40))) | ~v2_wellord1(k1_wellord2(B_40)) | ~v1_relat_1(k1_wellord2(B_40)) | ~r2_hidden(A_38, B_40) | ~v3_ordinal1(B_40) | ~v3_ordinal1(A_38))), inference(superposition, [status(thm), theory('equality')], [c_60, c_590])).
% 26.74/16.41  tff(c_2003, plain, (![B_183, A_184]: (~r4_wellord1(k1_wellord2(B_183), k2_wellord1(k1_wellord2(B_183), A_184)) | ~v2_wellord1(k1_wellord2(B_183)) | ~r2_hidden(A_184, B_183) | ~v3_ordinal1(B_183) | ~v3_ordinal1(A_184))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_78, c_593])).
% 26.74/16.41  tff(c_3354, plain, (![B_229, A_230]: (~r4_wellord1(k1_wellord2(B_229), k1_wellord2(A_230)) | ~v2_wellord1(k1_wellord2(B_229)) | ~r2_hidden(A_230, B_229) | ~v3_ordinal1(B_229) | ~v3_ordinal1(A_230) | ~r1_tarski(A_230, B_229))), inference(superposition, [status(thm), theory('equality')], [c_64, c_2003])).
% 26.74/16.41  tff(c_3357, plain, (~v2_wellord1(k1_wellord2('#skF_6')) | ~r2_hidden('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5') | ~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_127, c_3354])).
% 26.74/16.41  tff(c_3363, plain, (~v2_wellord1(k1_wellord2('#skF_6')) | ~r2_hidden('#skF_5', '#skF_6') | ~r1_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_3357])).
% 26.74/16.41  tff(c_3367, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_3363])).
% 26.74/16.41  tff(c_12, plain, (![A_5, B_6]: (~r2_hidden(A_5, B_6) | r2_hidden(A_5, k1_ordinal1(B_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 26.74/16.41  tff(c_20, plain, (![D_22, B_18, A_11]: (r2_hidden(k4_tarski(D_22, B_18), A_11) | ~r2_hidden(D_22, k1_wellord1(A_11, B_18)) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_73])).
% 26.74/16.41  tff(c_56, plain, (![C_35, D_36, A_29]: (r1_tarski(C_35, D_36) | ~r2_hidden(k4_tarski(C_35, D_36), k1_wellord2(A_29)) | ~r2_hidden(D_36, A_29) | ~r2_hidden(C_35, A_29) | ~v1_relat_1(k1_wellord2(A_29)))), inference(cnfTransformation, [status(thm)], [f_107])).
% 26.74/16.41  tff(c_719, plain, (![C_119, D_120, A_121]: (r1_tarski(C_119, D_120) | ~r2_hidden(k4_tarski(C_119, D_120), k1_wellord2(A_121)) | ~r2_hidden(D_120, A_121) | ~r2_hidden(C_119, A_121))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56])).
% 26.74/16.41  tff(c_732, plain, (![D_22, B_18, A_121]: (r1_tarski(D_22, B_18) | ~r2_hidden(B_18, A_121) | ~r2_hidden(D_22, A_121) | ~r2_hidden(D_22, k1_wellord1(k1_wellord2(A_121), B_18)) | ~v1_relat_1(k1_wellord2(A_121)))), inference(resolution, [status(thm)], [c_20, c_719])).
% 26.74/16.41  tff(c_894, plain, (![D_130, B_131, A_132]: (r1_tarski(D_130, B_131) | ~r2_hidden(B_131, A_132) | ~r2_hidden(D_130, A_132) | ~r2_hidden(D_130, k1_wellord1(k1_wellord2(A_132), B_131)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_732])).
% 26.74/16.41  tff(c_35156, plain, (![D_568, A_569, B_570]: (r1_tarski(D_568, A_569) | ~r2_hidden(A_569, B_570) | ~r2_hidden(D_568, B_570) | ~r2_hidden(D_568, A_569) | ~r2_hidden(A_569, B_570) | ~v3_ordinal1(B_570) | ~v3_ordinal1(A_569))), inference(superposition, [status(thm), theory('equality')], [c_60, c_894])).
% 26.74/16.41  tff(c_35264, plain, (![D_568, B_6]: (r1_tarski(D_568, B_6) | ~r2_hidden(D_568, k1_ordinal1(B_6)) | ~r2_hidden(D_568, B_6) | ~r2_hidden(B_6, k1_ordinal1(B_6)) | ~v3_ordinal1(k1_ordinal1(B_6)) | ~v3_ordinal1(B_6))), inference(resolution, [status(thm)], [c_10, c_35156])).
% 26.74/16.41  tff(c_35321, plain, (![D_571, B_572]: (r1_tarski(D_571, B_572) | ~r2_hidden(D_571, k1_ordinal1(B_572)) | ~r2_hidden(D_571, B_572) | ~v3_ordinal1(k1_ordinal1(B_572)) | ~v3_ordinal1(B_572))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_35264])).
% 26.74/16.41  tff(c_35446, plain, (![A_573, B_574]: (r1_tarski(A_573, B_574) | ~v3_ordinal1(k1_ordinal1(B_574)) | ~v3_ordinal1(B_574) | ~r2_hidden(A_573, B_574))), inference(resolution, [status(thm)], [c_12, c_35321])).
% 26.74/16.41  tff(c_35450, plain, (![A_575, A_576]: (r1_tarski(A_575, A_576) | ~r2_hidden(A_575, A_576) | ~v3_ordinal1(A_576))), inference(resolution, [status(thm)], [c_16, c_35446])).
% 26.74/16.41  tff(c_36087, plain, (![A_583, B_584]: (r1_tarski(A_583, B_584) | r2_hidden(B_584, A_583) | B_584=A_583 | ~v3_ordinal1(B_584) | ~v3_ordinal1(A_583))), inference(resolution, [status(thm)], [c_14, c_35450])).
% 26.74/16.41  tff(c_3360, plain, (~v2_wellord1(k1_wellord2('#skF_5')) | ~r2_hidden('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6') | ~r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_68, c_3354])).
% 26.74/16.41  tff(c_3366, plain, (~v2_wellord1(k1_wellord2('#skF_5')) | ~r2_hidden('#skF_6', '#skF_5') | ~r1_tarski('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_72, c_3360])).
% 26.74/16.41  tff(c_3368, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_3366])).
% 26.74/16.41  tff(c_20104, plain, (![D_400, A_401, B_402]: (r1_tarski(D_400, A_401) | ~r2_hidden(A_401, B_402) | ~r2_hidden(D_400, B_402) | ~r2_hidden(D_400, A_401) | ~r2_hidden(A_401, B_402) | ~v3_ordinal1(B_402) | ~v3_ordinal1(A_401))), inference(superposition, [status(thm), theory('equality')], [c_60, c_894])).
% 26.74/16.41  tff(c_20216, plain, (![D_400, B_6]: (r1_tarski(D_400, B_6) | ~r2_hidden(D_400, k1_ordinal1(B_6)) | ~r2_hidden(D_400, B_6) | ~r2_hidden(B_6, k1_ordinal1(B_6)) | ~v3_ordinal1(k1_ordinal1(B_6)) | ~v3_ordinal1(B_6))), inference(resolution, [status(thm)], [c_10, c_20104])).
% 26.74/16.41  tff(c_20275, plain, (![D_403, B_404]: (r1_tarski(D_403, B_404) | ~r2_hidden(D_403, k1_ordinal1(B_404)) | ~r2_hidden(D_403, B_404) | ~v3_ordinal1(k1_ordinal1(B_404)) | ~v3_ordinal1(B_404))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_20216])).
% 26.74/16.41  tff(c_20405, plain, (![A_405, B_406]: (r1_tarski(A_405, B_406) | ~v3_ordinal1(k1_ordinal1(B_406)) | ~v3_ordinal1(B_406) | ~r2_hidden(A_405, B_406))), inference(resolution, [status(thm)], [c_12, c_20275])).
% 26.74/16.41  tff(c_20409, plain, (![A_407, A_408]: (r1_tarski(A_407, A_408) | ~r2_hidden(A_407, A_408) | ~v3_ordinal1(A_408))), inference(resolution, [status(thm)], [c_16, c_20405])).
% 26.74/16.41  tff(c_20800, plain, (![A_413, B_414]: (r1_tarski(A_413, B_414) | r2_hidden(B_414, A_413) | B_414=A_413 | ~v3_ordinal1(B_414) | ~v3_ordinal1(A_413))), inference(resolution, [status(thm)], [c_14, c_20409])).
% 26.74/16.41  tff(c_20408, plain, (![A_405, A_10]: (r1_tarski(A_405, A_10) | ~r2_hidden(A_405, A_10) | ~v3_ordinal1(A_10))), inference(resolution, [status(thm)], [c_16, c_20405])).
% 26.74/16.41  tff(c_21102, plain, (![B_416, A_417]: (r1_tarski(B_416, A_417) | r1_tarski(A_417, B_416) | B_416=A_417 | ~v3_ordinal1(B_416) | ~v3_ordinal1(A_417))), inference(resolution, [status(thm)], [c_20800, c_20408])).
% 26.74/16.41  tff(c_21109, plain, (r1_tarski('#skF_6', '#skF_5') | '#skF_5'='#skF_6' | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_21102, c_3367])).
% 26.74/16.41  tff(c_21120, plain, (r1_tarski('#skF_6', '#skF_5') | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_72, c_21109])).
% 26.74/16.41  tff(c_21122, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_3368, c_21120])).
% 26.74/16.41  tff(c_21123, plain, (~r2_hidden('#skF_6', '#skF_5') | ~v2_wellord1(k1_wellord2('#skF_5'))), inference(splitRight, [status(thm)], [c_3366])).
% 26.74/16.41  tff(c_21125, plain, (~v2_wellord1(k1_wellord2('#skF_5'))), inference(splitLeft, [status(thm)], [c_21123])).
% 26.74/16.41  tff(c_21206, plain, (~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_21125])).
% 26.74/16.41  tff(c_21210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_21206])).
% 26.74/16.41  tff(c_21211, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_21123])).
% 26.74/16.41  tff(c_36154, plain, (r1_tarski('#skF_5', '#skF_6') | '#skF_5'='#skF_6' | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_36087, c_21211])).
% 26.74/16.41  tff(c_36317, plain, (r1_tarski('#skF_5', '#skF_6') | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_36154])).
% 26.74/16.41  tff(c_36319, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_3367, c_36317])).
% 26.74/16.41  tff(c_36320, plain, (~r2_hidden('#skF_5', '#skF_6') | ~v2_wellord1(k1_wellord2('#skF_6'))), inference(splitRight, [status(thm)], [c_3363])).
% 26.74/16.41  tff(c_36323, plain, (~v2_wellord1(k1_wellord2('#skF_6'))), inference(splitLeft, [status(thm)], [c_36320])).
% 26.74/16.41  tff(c_36326, plain, (~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_62, c_36323])).
% 26.74/16.41  tff(c_36330, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_36326])).
% 26.74/16.41  tff(c_36331, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_36320])).
% 26.74/16.41  tff(c_36338, plain, (r2_hidden('#skF_6', '#skF_5') | '#skF_5'='#skF_6' | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_14, c_36331])).
% 26.74/16.41  tff(c_36345, plain, (r2_hidden('#skF_6', '#skF_5') | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_36338])).
% 26.74/16.41  tff(c_36346, plain, (r2_hidden('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_66, c_36345])).
% 26.74/16.41  tff(c_169, plain, (![D_69, B_70, A_71]: (r2_hidden(k4_tarski(D_69, B_70), A_71) | ~r2_hidden(D_69, k1_wellord1(A_71, B_70)) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_73])).
% 26.74/16.41  tff(c_4, plain, (![A_1, C_3, B_2]: (r2_hidden(A_1, k3_relat_1(C_3)) | ~r2_hidden(k4_tarski(A_1, B_2), C_3) | ~v1_relat_1(C_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 26.74/16.41  tff(c_197, plain, (![D_74, A_75, B_76]: (r2_hidden(D_74, k3_relat_1(A_75)) | ~r2_hidden(D_74, k1_wellord1(A_75, B_76)) | ~v1_relat_1(A_75))), inference(resolution, [status(thm)], [c_169, c_4])).
% 26.74/16.41  tff(c_204, plain, (![D_74, B_40, A_38]: (r2_hidden(D_74, k3_relat_1(k1_wellord2(B_40))) | ~r2_hidden(D_74, A_38) | ~v1_relat_1(k1_wellord2(B_40)) | ~r2_hidden(A_38, B_40) | ~v3_ordinal1(B_40) | ~v3_ordinal1(A_38))), inference(superposition, [status(thm), theory('equality')], [c_60, c_197])).
% 26.74/16.41  tff(c_528, plain, (![D_106, B_107, A_108]: (r2_hidden(D_106, B_107) | ~r2_hidden(D_106, A_108) | ~r2_hidden(A_108, B_107) | ~v3_ordinal1(B_107) | ~v3_ordinal1(A_108))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_78, c_204])).
% 26.74/16.41  tff(c_1084, plain, (![A_148, B_149, B_150]: (r2_hidden(A_148, B_149) | ~r2_hidden(k1_ordinal1(B_150), B_149) | ~v3_ordinal1(B_149) | ~v3_ordinal1(k1_ordinal1(B_150)) | ~r2_hidden(A_148, B_150))), inference(resolution, [status(thm)], [c_12, c_528])).
% 26.74/16.41  tff(c_1127, plain, (![A_148, B_6, B_150]: (r2_hidden(A_148, k1_ordinal1(B_6)) | ~v3_ordinal1(k1_ordinal1(B_6)) | ~v3_ordinal1(k1_ordinal1(B_150)) | ~r2_hidden(A_148, B_150) | ~r2_hidden(k1_ordinal1(B_150), B_6))), inference(resolution, [status(thm)], [c_12, c_1084])).
% 26.74/16.41  tff(c_36431, plain, (![B_6]: (r2_hidden('#skF_6', k1_ordinal1(B_6)) | ~v3_ordinal1(k1_ordinal1(B_6)) | ~v3_ordinal1(k1_ordinal1('#skF_5')) | ~r2_hidden(k1_ordinal1('#skF_5'), B_6))), inference(resolution, [status(thm)], [c_36346, c_1127])).
% 26.74/16.41  tff(c_36439, plain, (~v3_ordinal1(k1_ordinal1('#skF_5'))), inference(splitLeft, [status(thm)], [c_36431])).
% 26.74/16.41  tff(c_36442, plain, (~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_16, c_36439])).
% 26.74/16.41  tff(c_36446, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_36442])).
% 26.74/16.41  tff(c_36448, plain, (v3_ordinal1(k1_ordinal1('#skF_5'))), inference(splitRight, [status(thm)], [c_36431])).
% 26.74/16.41  tff(c_559, plain, (![B_109, B_110]: (r2_hidden(B_109, B_110) | ~r2_hidden(k1_ordinal1(B_109), B_110) | ~v3_ordinal1(B_110) | ~v3_ordinal1(k1_ordinal1(B_109)))), inference(resolution, [status(thm)], [c_10, c_528])).
% 26.74/16.41  tff(c_1129, plain, (![B_151, B_152]: (r2_hidden(B_151, B_152) | r2_hidden(B_152, k1_ordinal1(B_151)) | k1_ordinal1(B_151)=B_152 | ~v3_ordinal1(B_152) | ~v3_ordinal1(k1_ordinal1(B_151)))), inference(resolution, [status(thm)], [c_14, c_559])).
% 26.74/16.41  tff(c_8, plain, (![B_6, A_5]: (B_6=A_5 | r2_hidden(A_5, B_6) | ~r2_hidden(A_5, k1_ordinal1(B_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 26.74/16.41  tff(c_1212, plain, (![B_152, B_151]: (B_152=B_151 | r2_hidden(B_152, B_151) | r2_hidden(B_151, B_152) | k1_ordinal1(B_151)=B_152 | ~v3_ordinal1(B_152) | ~v3_ordinal1(k1_ordinal1(B_151)))), inference(resolution, [status(thm)], [c_1129, c_8])).
% 26.74/16.41  tff(c_37854, plain, (![B_602]: (B_602='#skF_5' | r2_hidden(B_602, '#skF_5') | r2_hidden('#skF_5', B_602) | k1_ordinal1('#skF_5')=B_602 | ~v3_ordinal1(B_602))), inference(resolution, [status(thm)], [c_36448, c_1212])).
% 26.74/16.41  tff(c_558, plain, (![B_6, B_107]: (r2_hidden(B_6, B_107) | ~r2_hidden(k1_ordinal1(B_6), B_107) | ~v3_ordinal1(B_107) | ~v3_ordinal1(k1_ordinal1(B_6)))), inference(resolution, [status(thm)], [c_10, c_528])).
% 26.74/16.41  tff(c_37930, plain, (![B_6]: (r2_hidden(B_6, '#skF_5') | ~v3_ordinal1('#skF_5') | k1_ordinal1(B_6)='#skF_5' | r2_hidden('#skF_5', k1_ordinal1(B_6)) | k1_ordinal1(B_6)=k1_ordinal1('#skF_5') | ~v3_ordinal1(k1_ordinal1(B_6)))), inference(resolution, [status(thm)], [c_37854, c_558])).
% 26.74/16.41  tff(c_94966, plain, (![B_837]: (r2_hidden(B_837, '#skF_5') | k1_ordinal1(B_837)='#skF_5' | r2_hidden('#skF_5', k1_ordinal1(B_837)) | k1_ordinal1(B_837)=k1_ordinal1('#skF_5') | ~v3_ordinal1(k1_ordinal1(B_837)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_37930])).
% 26.74/16.41  tff(c_555, plain, (![A_7, B_107, B_9]: (r2_hidden(A_7, B_107) | ~r2_hidden(B_9, B_107) | ~v3_ordinal1(B_107) | r2_hidden(B_9, A_7) | B_9=A_7 | ~v3_ordinal1(B_9) | ~v3_ordinal1(A_7))), inference(resolution, [status(thm)], [c_14, c_528])).
% 26.74/16.41  tff(c_36428, plain, (![A_7]: (r2_hidden(A_7, '#skF_5') | ~v3_ordinal1('#skF_5') | r2_hidden('#skF_6', A_7) | A_7='#skF_6' | ~v3_ordinal1('#skF_6') | ~v3_ordinal1(A_7))), inference(resolution, [status(thm)], [c_36346, c_555])).
% 26.74/16.41  tff(c_36630, plain, (![A_591]: (r2_hidden(A_591, '#skF_5') | r2_hidden('#skF_6', A_591) | A_591='#skF_6' | ~v3_ordinal1(A_591))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_72, c_36428])).
% 26.74/16.41  tff(c_207, plain, (![D_74, B_40, A_38]: (r2_hidden(D_74, B_40) | ~r2_hidden(D_74, A_38) | ~r2_hidden(A_38, B_40) | ~v3_ordinal1(B_40) | ~v3_ordinal1(A_38))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_78, c_204])).
% 26.74/16.41  tff(c_40177, plain, (![B_618, A_619]: (r2_hidden('#skF_6', B_618) | ~r2_hidden(A_619, B_618) | ~v3_ordinal1(B_618) | r2_hidden(A_619, '#skF_5') | A_619='#skF_6' | ~v3_ordinal1(A_619))), inference(resolution, [status(thm)], [c_36630, c_207])).
% 26.74/16.41  tff(c_40392, plain, (![B_6, A_5]: (r2_hidden('#skF_6', k1_ordinal1(B_6)) | ~v3_ordinal1(k1_ordinal1(B_6)) | r2_hidden(A_5, '#skF_5') | A_5='#skF_6' | ~v3_ordinal1(A_5) | ~r2_hidden(A_5, B_6))), inference(resolution, [status(thm)], [c_12, c_40177])).
% 26.74/16.41  tff(c_94968, plain, (![B_837]: (r2_hidden('#skF_6', k1_ordinal1(k1_ordinal1(B_837))) | ~v3_ordinal1(k1_ordinal1(k1_ordinal1(B_837))) | r2_hidden('#skF_5', '#skF_5') | '#skF_5'='#skF_6' | ~v3_ordinal1('#skF_5') | r2_hidden(B_837, '#skF_5') | k1_ordinal1(B_837)='#skF_5' | k1_ordinal1(B_837)=k1_ordinal1('#skF_5') | ~v3_ordinal1(k1_ordinal1(B_837)))), inference(resolution, [status(thm)], [c_94966, c_40392])).
% 26.74/16.41  tff(c_94997, plain, (![B_837]: (r2_hidden('#skF_6', k1_ordinal1(k1_ordinal1(B_837))) | ~v3_ordinal1(k1_ordinal1(k1_ordinal1(B_837))) | r2_hidden('#skF_5', '#skF_5') | '#skF_5'='#skF_6' | r2_hidden(B_837, '#skF_5') | k1_ordinal1(B_837)='#skF_5' | k1_ordinal1(B_837)=k1_ordinal1('#skF_5') | ~v3_ordinal1(k1_ordinal1(B_837)))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_94968])).
% 26.74/16.41  tff(c_94998, plain, (![B_837]: (r2_hidden('#skF_6', k1_ordinal1(k1_ordinal1(B_837))) | ~v3_ordinal1(k1_ordinal1(k1_ordinal1(B_837))) | r2_hidden('#skF_5', '#skF_5') | r2_hidden(B_837, '#skF_5') | k1_ordinal1(B_837)='#skF_5' | k1_ordinal1(B_837)=k1_ordinal1('#skF_5') | ~v3_ordinal1(k1_ordinal1(B_837)))), inference(negUnitSimplification, [status(thm)], [c_66, c_94997])).
% 26.74/16.41  tff(c_96239, plain, (r2_hidden('#skF_5', '#skF_5')), inference(splitLeft, [status(thm)], [c_94998])).
% 26.74/16.41  tff(c_155, plain, (![B_67, A_68]: (k1_wellord1(k1_wellord2(B_67), A_68)=A_68 | ~r2_hidden(A_68, B_67) | ~v3_ordinal1(B_67) | ~v3_ordinal1(A_68))), inference(cnfTransformation, [status(thm)], [f_118])).
% 26.74/16.41  tff(c_22, plain, (![D_22, A_11]: (~r2_hidden(D_22, k1_wellord1(A_11, D_22)) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_73])).
% 26.74/16.41  tff(c_161, plain, (![A_68, B_67]: (~r2_hidden(A_68, A_68) | ~v1_relat_1(k1_wellord2(B_67)) | ~r2_hidden(A_68, B_67) | ~v3_ordinal1(B_67) | ~v3_ordinal1(A_68))), inference(superposition, [status(thm), theory('equality')], [c_155, c_22])).
% 26.74/16.41  tff(c_167, plain, (![A_68, B_67]: (~r2_hidden(A_68, A_68) | ~r2_hidden(A_68, B_67) | ~v3_ordinal1(B_67) | ~v3_ordinal1(A_68))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_161])).
% 26.74/16.41  tff(c_96266, plain, (![B_67]: (~r2_hidden('#skF_5', B_67) | ~v3_ordinal1(B_67) | ~v3_ordinal1('#skF_5'))), inference(resolution, [status(thm)], [c_96239, c_167])).
% 26.74/16.41  tff(c_96309, plain, (![B_841]: (~r2_hidden('#skF_5', B_841) | ~v3_ordinal1(B_841))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_96266])).
% 26.74/16.41  tff(c_96312, plain, (~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_96239, c_96309])).
% 26.74/16.41  tff(c_96755, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_96312])).
% 26.74/16.41  tff(c_96757, plain, (~r2_hidden('#skF_5', '#skF_5')), inference(splitRight, [status(thm)], [c_94998])).
% 26.74/16.41  tff(c_36322, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_3366])).
% 26.74/16.41  tff(c_589, plain, (![B_109]: (r2_hidden(B_109, k1_ordinal1(k1_ordinal1(B_109))) | ~v3_ordinal1(k1_ordinal1(k1_ordinal1(B_109))) | ~v3_ordinal1(k1_ordinal1(B_109)))), inference(resolution, [status(thm)], [c_10, c_559])).
% 26.74/16.41  tff(c_36430, plain, (![B_40]: (r2_hidden('#skF_6', B_40) | ~r2_hidden('#skF_5', B_40) | ~v3_ordinal1(B_40) | ~v3_ordinal1('#skF_5'))), inference(resolution, [status(thm)], [c_36346, c_207])).
% 26.74/16.41  tff(c_36452, plain, (![B_588]: (r2_hidden('#skF_6', B_588) | ~r2_hidden('#skF_5', B_588) | ~v3_ordinal1(B_588))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_36430])).
% 26.74/16.41  tff(c_36512, plain, (r2_hidden('#skF_6', k1_ordinal1(k1_ordinal1('#skF_5'))) | ~v3_ordinal1(k1_ordinal1(k1_ordinal1('#skF_5'))) | ~v3_ordinal1(k1_ordinal1('#skF_5'))), inference(resolution, [status(thm)], [c_589, c_36452])).
% 26.74/16.41  tff(c_36563, plain, (r2_hidden('#skF_6', k1_ordinal1(k1_ordinal1('#skF_5'))) | ~v3_ordinal1(k1_ordinal1(k1_ordinal1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_36448, c_36512])).
% 26.74/16.41  tff(c_36595, plain, (~v3_ordinal1(k1_ordinal1(k1_ordinal1('#skF_5')))), inference(splitLeft, [status(thm)], [c_36563])).
% 26.74/16.41  tff(c_36602, plain, (~v3_ordinal1(k1_ordinal1('#skF_5'))), inference(resolution, [status(thm)], [c_16, c_36595])).
% 26.74/16.41  tff(c_36606, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36448, c_36602])).
% 26.74/16.41  tff(c_36608, plain, (v3_ordinal1(k1_ordinal1(k1_ordinal1('#skF_5')))), inference(splitRight, [status(thm)], [c_36563])).
% 26.74/16.41  tff(c_94049, plain, (![B_834, A_835]: (r2_hidden('#skF_6', k1_ordinal1(B_834)) | ~v3_ordinal1(k1_ordinal1(B_834)) | r2_hidden(A_835, '#skF_5') | A_835='#skF_6' | ~v3_ordinal1(A_835) | ~r2_hidden(A_835, B_834))), inference(resolution, [status(thm)], [c_12, c_40177])).
% 26.74/16.41  tff(c_94920, plain, (![B_6]: (r2_hidden('#skF_6', k1_ordinal1(k1_ordinal1(B_6))) | ~v3_ordinal1(k1_ordinal1(k1_ordinal1(B_6))) | r2_hidden(B_6, '#skF_5') | B_6='#skF_6' | ~v3_ordinal1(B_6))), inference(resolution, [status(thm)], [c_10, c_94049])).
% 26.74/16.41  tff(c_739, plain, (![B_122, B_123]: (r2_hidden(B_122, k1_ordinal1(B_123)) | ~v3_ordinal1(k1_ordinal1(B_123)) | ~v3_ordinal1(k1_ordinal1(B_122)) | ~r2_hidden(k1_ordinal1(B_122), B_123))), inference(resolution, [status(thm)], [c_12, c_559])).
% 26.74/16.41  tff(c_784, plain, (![B_122]: (r2_hidden(B_122, k1_ordinal1(k1_ordinal1(k1_ordinal1(B_122)))) | ~v3_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(B_122)))) | ~v3_ordinal1(k1_ordinal1(B_122)))), inference(resolution, [status(thm)], [c_10, c_739])).
% 26.74/16.41  tff(c_36500, plain, (r2_hidden('#skF_6', k1_ordinal1(k1_ordinal1(k1_ordinal1('#skF_5')))) | ~v3_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1('#skF_5')))) | ~v3_ordinal1(k1_ordinal1('#skF_5'))), inference(resolution, [status(thm)], [c_784, c_36452])).
% 26.74/16.41  tff(c_36558, plain, (r2_hidden('#skF_6', k1_ordinal1(k1_ordinal1(k1_ordinal1('#skF_5')))) | ~v3_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_36448, c_36500])).
% 26.74/16.41  tff(c_37451, plain, (~v3_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1('#skF_5'))))), inference(splitLeft, [status(thm)], [c_36558])).
% 26.74/16.41  tff(c_37454, plain, (~v3_ordinal1(k1_ordinal1(k1_ordinal1('#skF_5')))), inference(resolution, [status(thm)], [c_16, c_37451])).
% 26.74/16.41  tff(c_37458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36608, c_37454])).
% 26.74/16.41  tff(c_37460, plain, (v3_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1('#skF_5'))))), inference(splitRight, [status(thm)], [c_36558])).
% 26.74/16.41  tff(c_785, plain, (![B_124]: (r2_hidden(B_124, k1_ordinal1(k1_ordinal1(k1_ordinal1(B_124)))) | ~v3_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(B_124)))) | ~v3_ordinal1(k1_ordinal1(B_124)))), inference(resolution, [status(thm)], [c_10, c_739])).
% 26.74/16.41  tff(c_825, plain, (![B_124]: (k1_ordinal1(k1_ordinal1(B_124))=B_124 | r2_hidden(B_124, k1_ordinal1(k1_ordinal1(B_124))) | ~v3_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(B_124)))) | ~v3_ordinal1(k1_ordinal1(B_124)))), inference(resolution, [status(thm)], [c_785, c_8])).
% 26.74/16.41  tff(c_37475, plain, (k1_ordinal1(k1_ordinal1('#skF_5'))='#skF_5' | r2_hidden('#skF_5', k1_ordinal1(k1_ordinal1('#skF_5'))) | ~v3_ordinal1(k1_ordinal1('#skF_5'))), inference(resolution, [status(thm)], [c_37460, c_825])).
% 26.74/16.41  tff(c_37480, plain, (k1_ordinal1(k1_ordinal1('#skF_5'))='#skF_5' | r2_hidden('#skF_5', k1_ordinal1(k1_ordinal1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_36448, c_37475])).
% 26.74/16.41  tff(c_37807, plain, (r2_hidden('#skF_5', k1_ordinal1(k1_ordinal1('#skF_5')))), inference(splitLeft, [status(thm)], [c_37480])).
% 26.74/16.41  tff(c_106260, plain, (![D_900, A_901, B_902]: (r1_tarski(D_900, A_901) | ~r2_hidden(A_901, B_902) | ~r2_hidden(D_900, B_902) | ~r2_hidden(D_900, A_901) | ~r2_hidden(A_901, B_902) | ~v3_ordinal1(B_902) | ~v3_ordinal1(A_901))), inference(superposition, [status(thm), theory('equality')], [c_60, c_894])).
% 26.74/16.41  tff(c_106582, plain, (![D_900]: (r1_tarski(D_900, '#skF_5') | ~r2_hidden(D_900, k1_ordinal1(k1_ordinal1('#skF_5'))) | ~r2_hidden(D_900, '#skF_5') | ~r2_hidden('#skF_5', k1_ordinal1(k1_ordinal1('#skF_5'))) | ~v3_ordinal1(k1_ordinal1(k1_ordinal1('#skF_5'))) | ~v3_ordinal1('#skF_5'))), inference(resolution, [status(thm)], [c_37807, c_106260])).
% 26.74/16.41  tff(c_108831, plain, (![D_911]: (r1_tarski(D_911, '#skF_5') | ~r2_hidden(D_911, k1_ordinal1(k1_ordinal1('#skF_5'))) | ~r2_hidden(D_911, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_36608, c_37807, c_106582])).
% 26.74/16.41  tff(c_108882, plain, (r1_tarski('#skF_6', '#skF_5') | ~r2_hidden('#skF_6', '#skF_5') | ~v3_ordinal1(k1_ordinal1(k1_ordinal1('#skF_5'))) | r2_hidden('#skF_5', '#skF_5') | '#skF_5'='#skF_6' | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_94920, c_108831])).
% 26.74/16.41  tff(c_109163, plain, (r1_tarski('#skF_6', '#skF_5') | r2_hidden('#skF_5', '#skF_5') | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_36608, c_36346, c_108882])).
% 26.74/16.41  tff(c_109165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_96757, c_36322, c_109163])).
% 26.74/16.41  tff(c_109166, plain, (k1_ordinal1(k1_ordinal1('#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_37480])).
% 26.74/16.41  tff(c_188, plain, (![A_72, B_73]: (~r2_hidden(A_72, A_72) | ~r2_hidden(A_72, B_73) | ~v3_ordinal1(B_73) | ~v3_ordinal1(A_72))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_161])).
% 26.74/16.41  tff(c_423, plain, (![B_97, B_98]: (~r2_hidden(k1_ordinal1(B_97), B_98) | ~v3_ordinal1(B_98) | ~v3_ordinal1(k1_ordinal1(B_97)) | ~r2_hidden(k1_ordinal1(B_97), B_97))), inference(resolution, [status(thm)], [c_12, c_188])).
% 26.74/16.41  tff(c_448, plain, (![B_99]: (~v3_ordinal1(k1_ordinal1(k1_ordinal1(B_99))) | ~v3_ordinal1(k1_ordinal1(B_99)) | ~r2_hidden(k1_ordinal1(B_99), B_99))), inference(resolution, [status(thm)], [c_10, c_423])).
% 26.74/16.41  tff(c_453, plain, (![B_100]: (~r2_hidden(k1_ordinal1(B_100), B_100) | ~v3_ordinal1(k1_ordinal1(B_100)))), inference(resolution, [status(thm)], [c_16, c_448])).
% 26.74/16.41  tff(c_471, plain, (![B_101]: (~v3_ordinal1(k1_ordinal1(k1_ordinal1(B_101))) | ~r2_hidden(k1_ordinal1(k1_ordinal1(B_101)), B_101))), inference(resolution, [status(thm)], [c_12, c_453])).
% 26.74/16.41  tff(c_512, plain, (![B_105]: (~v3_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(B_105)))) | ~r2_hidden(k1_ordinal1(k1_ordinal1(k1_ordinal1(B_105))), B_105))), inference(resolution, [status(thm)], [c_12, c_471])).
% 26.74/16.41  tff(c_639, plain, (![B_114]: (~v3_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(B_114))))) | ~r2_hidden(k1_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(B_114)))), B_114))), inference(resolution, [status(thm)], [c_12, c_512])).
% 26.74/16.41  tff(c_654, plain, (![B_6]: (~v3_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(B_6)))))) | ~r2_hidden(k1_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(B_6))))), B_6))), inference(resolution, [status(thm)], [c_12, c_639])).
% 26.74/16.41  tff(c_109231, plain, (~v3_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1('#skF_5'))))))) | ~r2_hidden(k1_ordinal1(k1_ordinal1(k1_ordinal1(k1_ordinal1('#skF_5')))), k1_ordinal1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_109166, c_654])).
% 26.74/16.41  tff(c_109341, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_109166, c_109166, c_72, c_109166, c_109166, c_109166, c_109231])).
% 26.74/16.41  tff(c_109342, plain, (~r2_hidden('#skF_6', '#skF_5') | ~v2_wellord1(k1_wellord2('#skF_5'))), inference(splitRight, [status(thm)], [c_3366])).
% 26.74/16.41  tff(c_109344, plain, (~v2_wellord1(k1_wellord2('#skF_5'))), inference(splitLeft, [status(thm)], [c_109342])).
% 26.74/16.41  tff(c_109347, plain, (~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_109344])).
% 26.74/16.41  tff(c_109351, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_109347])).
% 26.74/16.41  tff(c_109352, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_109342])).
% 26.74/16.41  tff(c_109434, plain, (~v2_wellord1(k1_wellord2('#skF_6'))), inference(splitLeft, [status(thm)], [c_36320])).
% 26.74/16.41  tff(c_109437, plain, (~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_62, c_109434])).
% 26.74/16.41  tff(c_109441, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_109437])).
% 26.74/16.41  tff(c_109442, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_36320])).
% 26.74/16.41  tff(c_109446, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_14, c_109442])).
% 26.74/16.41  tff(c_109452, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_72, c_109446])).
% 26.74/16.41  tff(c_109454, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109352, c_66, c_109452])).
% 26.74/16.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 26.74/16.41  
% 26.74/16.41  Inference rules
% 26.74/16.41  ----------------------
% 26.74/16.41  #Ref     : 0
% 26.74/16.41  #Sup     : 21250
% 26.74/16.41  #Fact    : 34
% 26.74/16.41  #Define  : 0
% 26.74/16.41  #Split   : 56
% 26.74/16.41  #Chain   : 0
% 26.74/16.41  #Close   : 0
% 26.74/16.41  
% 26.74/16.41  Ordering : KBO
% 26.74/16.41  
% 26.74/16.41  Simplification rules
% 26.74/16.41  ----------------------
% 26.74/16.41  #Subsume      : 6412
% 26.74/16.41  #Demod        : 23147
% 26.74/16.41  #Tautology    : 4580
% 26.74/16.41  #SimpNegUnit  : 332
% 26.74/16.41  #BackRed      : 271
% 26.74/16.41  
% 26.74/16.41  #Partial instantiations: 0
% 26.74/16.41  #Strategies tried      : 1
% 26.74/16.41  
% 26.74/16.41  Timing (in seconds)
% 26.74/16.41  ----------------------
% 26.74/16.41  Preprocessing        : 0.35
% 26.74/16.41  Parsing              : 0.18
% 26.74/16.41  CNF conversion       : 0.03
% 26.74/16.41  Main loop            : 15.26
% 26.74/16.41  Inferencing          : 2.20
% 26.74/16.41  Reduction            : 3.51
% 26.74/16.41  Demodulation         : 2.61
% 26.74/16.41  BG Simplification    : 0.34
% 26.74/16.41  Subsumption          : 8.42
% 26.74/16.41  Abstraction          : 0.65
% 26.74/16.41  MUC search           : 0.00
% 26.74/16.41  Cooper               : 0.00
% 26.74/16.41  Total                : 15.68
% 26.74/16.41  Index Insertion      : 0.00
% 26.74/16.41  Index Deletion       : 0.00
% 26.74/16.41  Index Matching       : 0.00
% 26.74/16.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
