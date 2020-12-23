%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:14 EST 2020

% Result     : Theorem 5.56s
% Output     : CNFRefutation 5.56s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 178 expanded)
%              Number of leaves         :   31 (  72 expanded)
%              Depth                    :   10
%              Number of atoms          :  157 ( 391 expanded)
%              Number of equality atoms :    8 (  15 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_109,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,B)
            <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_94,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_90,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_99,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_65,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_75,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_44,plain,(
    v3_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_42,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_640,plain,(
    ! [B_159,A_160] :
      ( r1_ordinal1(B_159,A_160)
      | r1_ordinal1(A_160,B_159)
      | ~ v3_ordinal1(B_159)
      | ~ v3_ordinal1(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_584,plain,(
    ! [A_154,B_155] :
      ( r1_tarski(A_154,B_155)
      | ~ r1_ordinal1(A_154,B_155)
      | ~ v3_ordinal1(B_155)
      | ~ v3_ordinal1(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_46,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_79,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_38,plain,(
    ! [A_48] :
      ( v3_ordinal1(k1_ordinal1(A_48))
      | ~ v3_ordinal1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_285,plain,(
    ! [B_100,A_101] :
      ( r2_hidden(B_100,A_101)
      | B_100 = A_101
      | r2_hidden(A_101,B_100)
      | ~ v3_ordinal1(B_100)
      | ~ v3_ordinal1(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_40,plain,(
    ! [B_50,A_49] :
      ( ~ r1_tarski(B_50,A_49)
      | ~ r2_hidden(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_369,plain,(
    ! [B_120,A_121] :
      ( ~ r1_tarski(B_120,A_121)
      | r2_hidden(B_120,A_121)
      | B_120 = A_121
      | ~ v3_ordinal1(B_120)
      | ~ v3_ordinal1(A_121) ) ),
    inference(resolution,[status(thm)],[c_285,c_40])).

tff(c_372,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | '#skF_2' = '#skF_1'
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_369,c_79])).

tff(c_378,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_372])).

tff(c_389,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_378])).

tff(c_52,plain,
    ( r2_hidden('#skF_1','#skF_2')
    | r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_80,plain,(
    r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_146,plain,(
    ! [A_78,B_79] :
      ( r1_tarski(A_78,B_79)
      | ~ r1_ordinal1(A_78,B_79)
      | ~ v3_ordinal1(B_79)
      | ~ v3_ordinal1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_28,plain,(
    ! [A_41] : k2_xboole_0(A_41,k1_tarski(A_41)) = k1_ordinal1(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_125,plain,(
    ! [A_68,C_69,B_70] :
      ( r1_tarski(A_68,C_69)
      | ~ r1_tarski(k2_xboole_0(A_68,B_70),C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_131,plain,(
    ! [A_41,C_69] :
      ( r1_tarski(A_41,C_69)
      | ~ r1_tarski(k1_ordinal1(A_41),C_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_125])).

tff(c_424,plain,(
    ! [A_133,B_134] :
      ( r1_tarski(A_133,B_134)
      | ~ r1_ordinal1(k1_ordinal1(A_133),B_134)
      | ~ v3_ordinal1(B_134)
      | ~ v3_ordinal1(k1_ordinal1(A_133)) ) ),
    inference(resolution,[status(thm)],[c_146,c_131])).

tff(c_451,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_80,c_424])).

tff(c_460,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_451])).

tff(c_461,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_389,c_460])).

tff(c_464,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_461])).

tff(c_468,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_464])).

tff(c_469,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_378])).

tff(c_471,plain,(
    r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_80])).

tff(c_34,plain,(
    ! [A_44] : r2_hidden(A_44,k1_ordinal1(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_64,plain,(
    ! [B_55,A_56] :
      ( ~ r1_tarski(B_55,A_56)
      | ~ r2_hidden(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_68,plain,(
    ! [A_44] : ~ r1_tarski(k1_ordinal1(A_44),A_44) ),
    inference(resolution,[status(thm)],[c_34,c_64])).

tff(c_171,plain,(
    ! [B_79] :
      ( ~ r1_ordinal1(k1_ordinal1(B_79),B_79)
      | ~ v3_ordinal1(B_79)
      | ~ v3_ordinal1(k1_ordinal1(B_79)) ) ),
    inference(resolution,[status(thm)],[c_146,c_68])).

tff(c_497,plain,
    ( ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_471,c_171])).

tff(c_500,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_497])).

tff(c_503,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_500])).

tff(c_507,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_503])).

tff(c_508,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_510,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_508])).

tff(c_512,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_516,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_512,c_40])).

tff(c_603,plain,
    ( ~ r1_ordinal1('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_584,c_516])).

tff(c_614,plain,(
    ~ r1_ordinal1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44,c_603])).

tff(c_647,plain,
    ( r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_640,c_614])).

tff(c_664,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_647])).

tff(c_32,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,B_43)
      | ~ r1_ordinal1(A_42,B_43)
      | ~ v3_ordinal1(B_43)
      | ~ v3_ordinal1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_511,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_650,plain,
    ( r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_640,c_511])).

tff(c_667,plain,
    ( r1_ordinal1('#skF_2',k1_ordinal1('#skF_1'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_650])).

tff(c_692,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_667])).

tff(c_695,plain,(
    ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_692])).

tff(c_699,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_695])).

tff(c_701,plain,(
    v3_ordinal1(k1_ordinal1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_667])).

tff(c_22,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(k1_tarski(A_35),B_36)
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_677,plain,(
    ! [A_162,C_163,B_164] :
      ( r1_tarski(k2_xboole_0(A_162,C_163),B_164)
      | ~ r1_tarski(C_163,B_164)
      | ~ r1_tarski(A_162,B_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_715,plain,(
    ! [A_170,B_171] :
      ( r1_tarski(k1_ordinal1(A_170),B_171)
      | ~ r1_tarski(k1_tarski(A_170),B_171)
      | ~ r1_tarski(A_170,B_171) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_677])).

tff(c_750,plain,(
    ! [A_174,B_175] :
      ( r1_tarski(k1_ordinal1(A_174),B_175)
      | ~ r1_tarski(A_174,B_175)
      | ~ r2_hidden(A_174,B_175) ) ),
    inference(resolution,[status(thm)],[c_22,c_715])).

tff(c_30,plain,(
    ! [A_42,B_43] :
      ( r1_ordinal1(A_42,B_43)
      | ~ r1_tarski(A_42,B_43)
      | ~ v3_ordinal1(B_43)
      | ~ v3_ordinal1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3960,plain,(
    ! [A_362,B_363] :
      ( r1_ordinal1(k1_ordinal1(A_362),B_363)
      | ~ v3_ordinal1(B_363)
      | ~ v3_ordinal1(k1_ordinal1(A_362))
      | ~ r1_tarski(A_362,B_363)
      | ~ r2_hidden(A_362,B_363) ) ),
    inference(resolution,[status(thm)],[c_750,c_30])).

tff(c_3980,plain,
    ( ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1(k1_ordinal1('#skF_1'))
    | ~ r1_tarski('#skF_1','#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_3960,c_511])).

tff(c_3988,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_701,c_42,c_3980])).

tff(c_3991,plain,
    ( ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_3988])).

tff(c_3995,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_664,c_3991])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:48:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.56/2.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.56/2.08  
% 5.56/2.08  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.56/2.08  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1
% 5.56/2.08  
% 5.56/2.08  %Foreground sorts:
% 5.56/2.08  
% 5.56/2.08  
% 5.56/2.08  %Background operators:
% 5.56/2.08  
% 5.56/2.08  
% 5.56/2.08  %Foreground operators:
% 5.56/2.08  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 5.56/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.56/2.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.56/2.08  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.56/2.08  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.56/2.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.56/2.08  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.56/2.08  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 5.56/2.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.56/2.08  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.56/2.08  tff('#skF_2', type, '#skF_2': $i).
% 5.56/2.08  tff('#skF_1', type, '#skF_1': $i).
% 5.56/2.08  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 5.56/2.08  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.56/2.08  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.56/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.56/2.08  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.56/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.56/2.08  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.56/2.08  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.56/2.08  
% 5.56/2.10  tff(f_109, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_ordinal1)).
% 5.56/2.10  tff(f_63, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 5.56/2.10  tff(f_73, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 5.56/2.10  tff(f_94, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_ordinal1)).
% 5.56/2.10  tff(f_90, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 5.56/2.10  tff(f_99, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.56/2.10  tff(f_65, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 5.56/2.10  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 5.56/2.10  tff(f_75, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 5.56/2.10  tff(f_53, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 5.56/2.10  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 5.56/2.10  tff(c_44, plain, (v3_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.56/2.10  tff(c_42, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.56/2.10  tff(c_640, plain, (![B_159, A_160]: (r1_ordinal1(B_159, A_160) | r1_ordinal1(A_160, B_159) | ~v3_ordinal1(B_159) | ~v3_ordinal1(A_160))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.56/2.10  tff(c_584, plain, (![A_154, B_155]: (r1_tarski(A_154, B_155) | ~r1_ordinal1(A_154, B_155) | ~v3_ordinal1(B_155) | ~v3_ordinal1(A_154))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.56/2.10  tff(c_46, plain, (~r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.56/2.10  tff(c_79, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_46])).
% 5.56/2.10  tff(c_38, plain, (![A_48]: (v3_ordinal1(k1_ordinal1(A_48)) | ~v3_ordinal1(A_48))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.56/2.10  tff(c_285, plain, (![B_100, A_101]: (r2_hidden(B_100, A_101) | B_100=A_101 | r2_hidden(A_101, B_100) | ~v3_ordinal1(B_100) | ~v3_ordinal1(A_101))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.56/2.10  tff(c_40, plain, (![B_50, A_49]: (~r1_tarski(B_50, A_49) | ~r2_hidden(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.56/2.10  tff(c_369, plain, (![B_120, A_121]: (~r1_tarski(B_120, A_121) | r2_hidden(B_120, A_121) | B_120=A_121 | ~v3_ordinal1(B_120) | ~v3_ordinal1(A_121))), inference(resolution, [status(thm)], [c_285, c_40])).
% 5.56/2.10  tff(c_372, plain, (~r1_tarski('#skF_1', '#skF_2') | '#skF_2'='#skF_1' | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_369, c_79])).
% 5.56/2.10  tff(c_378, plain, (~r1_tarski('#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_372])).
% 5.56/2.10  tff(c_389, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_378])).
% 5.56/2.10  tff(c_52, plain, (r2_hidden('#skF_1', '#skF_2') | r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_109])).
% 5.56/2.10  tff(c_80, plain, (r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_52])).
% 5.56/2.10  tff(c_146, plain, (![A_78, B_79]: (r1_tarski(A_78, B_79) | ~r1_ordinal1(A_78, B_79) | ~v3_ordinal1(B_79) | ~v3_ordinal1(A_78))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.56/2.10  tff(c_28, plain, (![A_41]: (k2_xboole_0(A_41, k1_tarski(A_41))=k1_ordinal1(A_41))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.56/2.10  tff(c_125, plain, (![A_68, C_69, B_70]: (r1_tarski(A_68, C_69) | ~r1_tarski(k2_xboole_0(A_68, B_70), C_69))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.56/2.10  tff(c_131, plain, (![A_41, C_69]: (r1_tarski(A_41, C_69) | ~r1_tarski(k1_ordinal1(A_41), C_69))), inference(superposition, [status(thm), theory('equality')], [c_28, c_125])).
% 5.56/2.10  tff(c_424, plain, (![A_133, B_134]: (r1_tarski(A_133, B_134) | ~r1_ordinal1(k1_ordinal1(A_133), B_134) | ~v3_ordinal1(B_134) | ~v3_ordinal1(k1_ordinal1(A_133)))), inference(resolution, [status(thm)], [c_146, c_131])).
% 5.56/2.10  tff(c_451, plain, (r1_tarski('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_80, c_424])).
% 5.56/2.10  tff(c_460, plain, (r1_tarski('#skF_1', '#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_451])).
% 5.56/2.10  tff(c_461, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_389, c_460])).
% 5.56/2.10  tff(c_464, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_38, c_461])).
% 5.56/2.10  tff(c_468, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_464])).
% 5.56/2.10  tff(c_469, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_378])).
% 5.56/2.10  tff(c_471, plain, (r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_469, c_80])).
% 5.56/2.10  tff(c_34, plain, (![A_44]: (r2_hidden(A_44, k1_ordinal1(A_44)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.56/2.10  tff(c_64, plain, (![B_55, A_56]: (~r1_tarski(B_55, A_56) | ~r2_hidden(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.56/2.10  tff(c_68, plain, (![A_44]: (~r1_tarski(k1_ordinal1(A_44), A_44))), inference(resolution, [status(thm)], [c_34, c_64])).
% 5.56/2.10  tff(c_171, plain, (![B_79]: (~r1_ordinal1(k1_ordinal1(B_79), B_79) | ~v3_ordinal1(B_79) | ~v3_ordinal1(k1_ordinal1(B_79)))), inference(resolution, [status(thm)], [c_146, c_68])).
% 5.56/2.10  tff(c_497, plain, (~v3_ordinal1('#skF_1') | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(resolution, [status(thm)], [c_471, c_171])).
% 5.56/2.10  tff(c_500, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_497])).
% 5.56/2.10  tff(c_503, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_38, c_500])).
% 5.56/2.10  tff(c_507, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_503])).
% 5.56/2.10  tff(c_508, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_52])).
% 5.56/2.10  tff(c_510, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_508])).
% 5.56/2.10  tff(c_512, plain, (r2_hidden('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 5.56/2.10  tff(c_516, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_512, c_40])).
% 5.56/2.10  tff(c_603, plain, (~r1_ordinal1('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_584, c_516])).
% 5.56/2.10  tff(c_614, plain, (~r1_ordinal1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44, c_603])).
% 5.56/2.10  tff(c_647, plain, (r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_640, c_614])).
% 5.56/2.10  tff(c_664, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_647])).
% 5.56/2.10  tff(c_32, plain, (![A_42, B_43]: (r1_tarski(A_42, B_43) | ~r1_ordinal1(A_42, B_43) | ~v3_ordinal1(B_43) | ~v3_ordinal1(A_42))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.56/2.10  tff(c_511, plain, (~r1_ordinal1(k1_ordinal1('#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_46])).
% 5.56/2.10  tff(c_650, plain, (r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1')) | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_640, c_511])).
% 5.56/2.10  tff(c_667, plain, (r1_ordinal1('#skF_2', k1_ordinal1('#skF_1')) | ~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_650])).
% 5.56/2.10  tff(c_692, plain, (~v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitLeft, [status(thm)], [c_667])).
% 5.56/2.10  tff(c_695, plain, (~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_38, c_692])).
% 5.56/2.10  tff(c_699, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_695])).
% 5.56/2.10  tff(c_701, plain, (v3_ordinal1(k1_ordinal1('#skF_1'))), inference(splitRight, [status(thm)], [c_667])).
% 5.56/2.10  tff(c_22, plain, (![A_35, B_36]: (r1_tarski(k1_tarski(A_35), B_36) | ~r2_hidden(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.56/2.10  tff(c_677, plain, (![A_162, C_163, B_164]: (r1_tarski(k2_xboole_0(A_162, C_163), B_164) | ~r1_tarski(C_163, B_164) | ~r1_tarski(A_162, B_164))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.56/2.10  tff(c_715, plain, (![A_170, B_171]: (r1_tarski(k1_ordinal1(A_170), B_171) | ~r1_tarski(k1_tarski(A_170), B_171) | ~r1_tarski(A_170, B_171))), inference(superposition, [status(thm), theory('equality')], [c_28, c_677])).
% 5.56/2.10  tff(c_750, plain, (![A_174, B_175]: (r1_tarski(k1_ordinal1(A_174), B_175) | ~r1_tarski(A_174, B_175) | ~r2_hidden(A_174, B_175))), inference(resolution, [status(thm)], [c_22, c_715])).
% 5.56/2.10  tff(c_30, plain, (![A_42, B_43]: (r1_ordinal1(A_42, B_43) | ~r1_tarski(A_42, B_43) | ~v3_ordinal1(B_43) | ~v3_ordinal1(A_42))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.56/2.10  tff(c_3960, plain, (![A_362, B_363]: (r1_ordinal1(k1_ordinal1(A_362), B_363) | ~v3_ordinal1(B_363) | ~v3_ordinal1(k1_ordinal1(A_362)) | ~r1_tarski(A_362, B_363) | ~r2_hidden(A_362, B_363))), inference(resolution, [status(thm)], [c_750, c_30])).
% 5.56/2.10  tff(c_3980, plain, (~v3_ordinal1('#skF_2') | ~v3_ordinal1(k1_ordinal1('#skF_1')) | ~r1_tarski('#skF_1', '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_3960, c_511])).
% 5.56/2.10  tff(c_3988, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_512, c_701, c_42, c_3980])).
% 5.56/2.10  tff(c_3991, plain, (~r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_32, c_3988])).
% 5.56/2.10  tff(c_3995, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_664, c_3991])).
% 5.56/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.56/2.10  
% 5.56/2.10  Inference rules
% 5.56/2.10  ----------------------
% 5.56/2.10  #Ref     : 0
% 5.56/2.10  #Sup     : 809
% 5.56/2.10  #Fact    : 12
% 5.56/2.10  #Define  : 0
% 5.56/2.10  #Split   : 4
% 5.56/2.10  #Chain   : 0
% 5.56/2.10  #Close   : 0
% 5.56/2.10  
% 5.56/2.10  Ordering : KBO
% 5.56/2.10  
% 5.56/2.10  Simplification rules
% 5.56/2.10  ----------------------
% 5.56/2.10  #Subsume      : 152
% 5.56/2.10  #Demod        : 145
% 5.56/2.10  #Tautology    : 73
% 5.56/2.10  #SimpNegUnit  : 3
% 5.56/2.10  #BackRed      : 3
% 5.56/2.10  
% 5.56/2.10  #Partial instantiations: 0
% 5.56/2.10  #Strategies tried      : 1
% 5.56/2.10  
% 5.56/2.10  Timing (in seconds)
% 5.56/2.10  ----------------------
% 5.56/2.10  Preprocessing        : 0.33
% 5.56/2.10  Parsing              : 0.17
% 5.56/2.10  CNF conversion       : 0.02
% 5.56/2.10  Main loop            : 1.00
% 5.56/2.10  Inferencing          : 0.36
% 5.56/2.10  Reduction            : 0.28
% 5.56/2.10  Demodulation         : 0.19
% 5.56/2.10  BG Simplification    : 0.05
% 5.56/2.10  Subsumption          : 0.23
% 5.56/2.10  Abstraction          : 0.04
% 5.56/2.10  MUC search           : 0.00
% 5.56/2.10  Cooper               : 0.00
% 5.56/2.10  Total                : 1.36
% 5.56/2.10  Index Insertion      : 0.00
% 5.56/2.10  Index Deletion       : 0.00
% 5.56/2.10  Index Matching       : 0.00
% 5.56/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
