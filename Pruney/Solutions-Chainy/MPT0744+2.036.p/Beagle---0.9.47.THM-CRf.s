%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:19 EST 2020

% Result     : Theorem 20.80s
% Output     : CNFRefutation 20.80s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 157 expanded)
%              Number of leaves         :   40 (  71 expanded)
%              Depth                    :   11
%              Number of atoms          :  149 ( 304 expanded)
%              Number of equality atoms :   30 (  66 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_7 > #skF_1 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_6 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

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
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_148,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_124,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_57,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_59,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_109,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_133,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_107,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_116,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

tff(c_142,plain,(
    v3_ordinal1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_35433,plain,(
    ! [A_2919,B_2920] :
      ( r1_ordinal1(A_2919,B_2920)
      | ~ r1_tarski(A_2919,B_2920)
      | ~ v3_ordinal1(B_2920)
      | ~ v3_ordinal1(A_2919) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_35441,plain,(
    ! [B_8] :
      ( r1_ordinal1(B_8,B_8)
      | ~ v3_ordinal1(B_8) ) ),
    inference(resolution,[status(thm)],[c_24,c_35433])).

tff(c_50,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_229,plain,(
    ! [A_102,B_103] : k1_enumset1(A_102,A_102,B_103) = k2_tarski(A_102,B_103) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_32,plain,(
    ! [E_15,B_10,C_11] : r2_hidden(E_15,k1_enumset1(E_15,B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_256,plain,(
    ! [A_104,B_105] : r2_hidden(A_104,k2_tarski(A_104,B_105)) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_32])).

tff(c_262,plain,(
    ! [A_16] : r2_hidden(A_16,k1_tarski(A_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_256])).

tff(c_124,plain,(
    ! [A_59] : k2_xboole_0(A_59,k1_tarski(A_59)) = k1_ordinal1(A_59) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_270,plain,(
    ! [D_108,B_109,A_110] :
      ( ~ r2_hidden(D_108,B_109)
      | r2_hidden(D_108,k2_xboole_0(A_110,B_109)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_1233,plain,(
    ! [D_242,A_243] :
      ( ~ r2_hidden(D_242,k1_tarski(A_243))
      | r2_hidden(D_242,k1_ordinal1(A_243)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_270])).

tff(c_1246,plain,(
    ! [A_16] : r2_hidden(A_16,k1_ordinal1(A_16)) ),
    inference(resolution,[status(thm)],[c_262,c_1233])).

tff(c_140,plain,(
    v3_ordinal1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_462,plain,(
    ! [B_137,A_138] :
      ( r2_hidden(B_137,A_138)
      | r1_ordinal1(A_138,B_137)
      | ~ v3_ordinal1(B_137)
      | ~ v3_ordinal1(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_360,plain,(
    ! [D_123,A_124,B_125] :
      ( ~ r2_hidden(D_123,A_124)
      | r2_hidden(D_123,k2_xboole_0(A_124,B_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_375,plain,(
    ! [D_126,A_127] :
      ( ~ r2_hidden(D_126,A_127)
      | r2_hidden(D_126,k1_ordinal1(A_127)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_360])).

tff(c_144,plain,
    ( ~ r1_ordinal1('#skF_8','#skF_9')
    | ~ r2_hidden('#skF_8',k1_ordinal1('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_171,plain,(
    ~ r2_hidden('#skF_8',k1_ordinal1('#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_387,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_375,c_171])).

tff(c_477,plain,
    ( r1_ordinal1('#skF_9','#skF_8')
    | ~ v3_ordinal1('#skF_8')
    | ~ v3_ordinal1('#skF_9') ),
    inference(resolution,[status(thm)],[c_462,c_387])).

tff(c_492,plain,(
    r1_ordinal1('#skF_9','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_142,c_477])).

tff(c_150,plain,
    ( r2_hidden('#skF_8',k1_ordinal1('#skF_9'))
    | r1_ordinal1('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_212,plain,(
    r1_ordinal1('#skF_8','#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_171,c_150])).

tff(c_134,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(A_64,B_65)
      | ~ r1_ordinal1(A_64,B_65)
      | ~ v3_ordinal1(B_65)
      | ~ v3_ordinal1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_715,plain,(
    ! [A_156,B_157] :
      ( r1_tarski(A_156,B_157)
      | ~ r1_ordinal1(A_156,B_157)
      | ~ v3_ordinal1(B_157)
      | ~ v3_ordinal1(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_20,plain,(
    ! [B_8,A_7] :
      ( B_8 = A_7
      | ~ r1_tarski(B_8,A_7)
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_9396,plain,(
    ! [B_1181,A_1182] :
      ( B_1181 = A_1182
      | ~ r1_tarski(B_1181,A_1182)
      | ~ r1_ordinal1(A_1182,B_1181)
      | ~ v3_ordinal1(B_1181)
      | ~ v3_ordinal1(A_1182) ) ),
    inference(resolution,[status(thm)],[c_715,c_20])).

tff(c_34779,plain,(
    ! [B_2828,A_2829] :
      ( B_2828 = A_2829
      | ~ r1_ordinal1(B_2828,A_2829)
      | ~ r1_ordinal1(A_2829,B_2828)
      | ~ v3_ordinal1(B_2828)
      | ~ v3_ordinal1(A_2829) ) ),
    inference(resolution,[status(thm)],[c_134,c_9396])).

tff(c_34811,plain,
    ( '#skF_9' = '#skF_8'
    | ~ r1_ordinal1('#skF_9','#skF_8')
    | ~ v3_ordinal1('#skF_8')
    | ~ v3_ordinal1('#skF_9') ),
    inference(resolution,[status(thm)],[c_212,c_34779])).

tff(c_34832,plain,(
    '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_142,c_492,c_34811])).

tff(c_34877,plain,(
    ~ r2_hidden('#skF_8',k1_ordinal1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34832,c_171])).

tff(c_34883,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1246,c_34877])).

tff(c_34884,plain,(
    ~ r1_ordinal1('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_153,plain,(
    ! [A_73] :
      ( v1_ordinal1(A_73)
      | ~ v3_ordinal1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_160,plain,(
    v1_ordinal1('#skF_9') ),
    inference(resolution,[status(thm)],[c_140,c_153])).

tff(c_34885,plain,(
    r2_hidden('#skF_8',k1_ordinal1('#skF_9')) ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_36255,plain,(
    ! [D_3049,B_3050,A_3051] :
      ( r2_hidden(D_3049,B_3050)
      | r2_hidden(D_3049,A_3051)
      | ~ r2_hidden(D_3049,k2_xboole_0(A_3051,B_3050)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_36271,plain,(
    ! [D_3049,A_59] :
      ( r2_hidden(D_3049,k1_tarski(A_59))
      | r2_hidden(D_3049,A_59)
      | ~ r2_hidden(D_3049,k1_ordinal1(A_59)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_36255])).

tff(c_52,plain,(
    ! [A_17,B_18] : k1_enumset1(A_17,A_17,B_18) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_36471,plain,(
    ! [E_3056,C_3057,B_3058,A_3059] :
      ( E_3056 = C_3057
      | E_3056 = B_3058
      | E_3056 = A_3059
      | ~ r2_hidden(E_3056,k1_enumset1(A_3059,B_3058,C_3057)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_42063,plain,(
    ! [E_3841,B_3842,A_3843] :
      ( E_3841 = B_3842
      | E_3841 = A_3843
      | E_3841 = A_3843
      | ~ r2_hidden(E_3841,k2_tarski(A_3843,B_3842)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_36471])).

tff(c_44964,plain,(
    ! [E_3966,A_3967] :
      ( E_3966 = A_3967
      | E_3966 = A_3967
      | E_3966 = A_3967
      | ~ r2_hidden(E_3966,k1_tarski(A_3967)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_42063])).

tff(c_45040,plain,(
    ! [D_3969,A_3970] :
      ( D_3969 = A_3970
      | r2_hidden(D_3969,A_3970)
      | ~ r2_hidden(D_3969,k1_ordinal1(A_3970)) ) ),
    inference(resolution,[status(thm)],[c_36271,c_44964])).

tff(c_45122,plain,
    ( '#skF_9' = '#skF_8'
    | r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_34885,c_45040])).

tff(c_45123,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_45122])).

tff(c_126,plain,(
    ! [B_63,A_60] :
      ( r1_tarski(B_63,A_60)
      | ~ r2_hidden(B_63,A_60)
      | ~ v1_ordinal1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_45126,plain,
    ( r1_tarski('#skF_8','#skF_9')
    | ~ v1_ordinal1('#skF_9') ),
    inference(resolution,[status(thm)],[c_45123,c_126])).

tff(c_45132,plain,(
    r1_tarski('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_45126])).

tff(c_132,plain,(
    ! [A_64,B_65] :
      ( r1_ordinal1(A_64,B_65)
      | ~ r1_tarski(A_64,B_65)
      | ~ v3_ordinal1(B_65)
      | ~ v3_ordinal1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_45139,plain,
    ( r1_ordinal1('#skF_8','#skF_9')
    | ~ v3_ordinal1('#skF_9')
    | ~ v3_ordinal1('#skF_8') ),
    inference(resolution,[status(thm)],[c_45132,c_132])).

tff(c_45147,plain,(
    r1_ordinal1('#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_140,c_45139])).

tff(c_45149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34884,c_45147])).

tff(c_45150,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_45122])).

tff(c_45218,plain,(
    ~ r1_ordinal1('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45150,c_34884])).

tff(c_45239,plain,(
    ~ v3_ordinal1('#skF_8') ),
    inference(resolution,[status(thm)],[c_35441,c_45218])).

tff(c_45243,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_45239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:24:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.80/11.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.80/11.21  
% 20.80/11.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.80/11.21  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_ordinal1 > #skF_7 > #skF_1 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_6 > #skF_5 > #skF_3
% 20.80/11.21  
% 20.80/11.21  %Foreground sorts:
% 20.80/11.21  
% 20.80/11.21  
% 20.80/11.21  %Background operators:
% 20.80/11.21  
% 20.80/11.21  
% 20.80/11.21  %Foreground operators:
% 20.80/11.21  tff('#skF_7', type, '#skF_7': $i > $i).
% 20.80/11.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 20.80/11.21  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 20.80/11.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.80/11.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 20.80/11.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 20.80/11.21  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 20.80/11.21  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 20.80/11.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.80/11.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 20.80/11.21  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 20.80/11.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 20.80/11.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 20.80/11.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 20.80/11.21  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 20.80/11.21  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 20.80/11.21  tff('#skF_9', type, '#skF_9': $i).
% 20.80/11.21  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 20.80/11.21  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 20.80/11.21  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 20.80/11.21  tff('#skF_8', type, '#skF_8': $i).
% 20.80/11.21  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 20.80/11.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.80/11.21  tff(k3_tarski, type, k3_tarski: $i > $i).
% 20.80/11.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.80/11.21  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 20.80/11.21  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 20.80/11.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 20.80/11.21  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 20.80/11.21  
% 20.80/11.23  tff(f_148, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_ordinal1)).
% 20.80/11.23  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 20.80/11.23  tff(f_124, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 20.80/11.23  tff(f_57, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 20.80/11.23  tff(f_59, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 20.80/11.23  tff(f_55, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 20.80/11.23  tff(f_109, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 20.80/11.23  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 20.80/11.23  tff(f_133, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 20.80/11.23  tff(f_107, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_ordinal1)).
% 20.80/11.23  tff(f_116, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_ordinal1)).
% 20.80/11.23  tff(c_142, plain, (v3_ordinal1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_148])).
% 20.80/11.23  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 20.80/11.23  tff(c_35433, plain, (![A_2919, B_2920]: (r1_ordinal1(A_2919, B_2920) | ~r1_tarski(A_2919, B_2920) | ~v3_ordinal1(B_2920) | ~v3_ordinal1(A_2919))), inference(cnfTransformation, [status(thm)], [f_124])).
% 20.80/11.23  tff(c_35441, plain, (![B_8]: (r1_ordinal1(B_8, B_8) | ~v3_ordinal1(B_8))), inference(resolution, [status(thm)], [c_24, c_35433])).
% 20.80/11.23  tff(c_50, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_57])).
% 20.80/11.23  tff(c_229, plain, (![A_102, B_103]: (k1_enumset1(A_102, A_102, B_103)=k2_tarski(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_59])).
% 20.80/11.23  tff(c_32, plain, (![E_15, B_10, C_11]: (r2_hidden(E_15, k1_enumset1(E_15, B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 20.80/11.23  tff(c_256, plain, (![A_104, B_105]: (r2_hidden(A_104, k2_tarski(A_104, B_105)))), inference(superposition, [status(thm), theory('equality')], [c_229, c_32])).
% 20.80/11.23  tff(c_262, plain, (![A_16]: (r2_hidden(A_16, k1_tarski(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_256])).
% 20.80/11.23  tff(c_124, plain, (![A_59]: (k2_xboole_0(A_59, k1_tarski(A_59))=k1_ordinal1(A_59))), inference(cnfTransformation, [status(thm)], [f_109])).
% 20.80/11.23  tff(c_270, plain, (![D_108, B_109, A_110]: (~r2_hidden(D_108, B_109) | r2_hidden(D_108, k2_xboole_0(A_110, B_109)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 20.80/11.23  tff(c_1233, plain, (![D_242, A_243]: (~r2_hidden(D_242, k1_tarski(A_243)) | r2_hidden(D_242, k1_ordinal1(A_243)))), inference(superposition, [status(thm), theory('equality')], [c_124, c_270])).
% 20.80/11.23  tff(c_1246, plain, (![A_16]: (r2_hidden(A_16, k1_ordinal1(A_16)))), inference(resolution, [status(thm)], [c_262, c_1233])).
% 20.80/11.23  tff(c_140, plain, (v3_ordinal1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_148])).
% 20.80/11.23  tff(c_462, plain, (![B_137, A_138]: (r2_hidden(B_137, A_138) | r1_ordinal1(A_138, B_137) | ~v3_ordinal1(B_137) | ~v3_ordinal1(A_138))), inference(cnfTransformation, [status(thm)], [f_133])).
% 20.80/11.23  tff(c_360, plain, (![D_123, A_124, B_125]: (~r2_hidden(D_123, A_124) | r2_hidden(D_123, k2_xboole_0(A_124, B_125)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 20.80/11.23  tff(c_375, plain, (![D_126, A_127]: (~r2_hidden(D_126, A_127) | r2_hidden(D_126, k1_ordinal1(A_127)))), inference(superposition, [status(thm), theory('equality')], [c_124, c_360])).
% 20.80/11.23  tff(c_144, plain, (~r1_ordinal1('#skF_8', '#skF_9') | ~r2_hidden('#skF_8', k1_ordinal1('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 20.80/11.23  tff(c_171, plain, (~r2_hidden('#skF_8', k1_ordinal1('#skF_9'))), inference(splitLeft, [status(thm)], [c_144])).
% 20.80/11.23  tff(c_387, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_375, c_171])).
% 20.80/11.23  tff(c_477, plain, (r1_ordinal1('#skF_9', '#skF_8') | ~v3_ordinal1('#skF_8') | ~v3_ordinal1('#skF_9')), inference(resolution, [status(thm)], [c_462, c_387])).
% 20.80/11.23  tff(c_492, plain, (r1_ordinal1('#skF_9', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_142, c_477])).
% 20.80/11.23  tff(c_150, plain, (r2_hidden('#skF_8', k1_ordinal1('#skF_9')) | r1_ordinal1('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_148])).
% 20.80/11.23  tff(c_212, plain, (r1_ordinal1('#skF_8', '#skF_9')), inference(negUnitSimplification, [status(thm)], [c_171, c_150])).
% 20.80/11.23  tff(c_134, plain, (![A_64, B_65]: (r1_tarski(A_64, B_65) | ~r1_ordinal1(A_64, B_65) | ~v3_ordinal1(B_65) | ~v3_ordinal1(A_64))), inference(cnfTransformation, [status(thm)], [f_124])).
% 20.80/11.23  tff(c_715, plain, (![A_156, B_157]: (r1_tarski(A_156, B_157) | ~r1_ordinal1(A_156, B_157) | ~v3_ordinal1(B_157) | ~v3_ordinal1(A_156))), inference(cnfTransformation, [status(thm)], [f_124])).
% 20.80/11.23  tff(c_20, plain, (![B_8, A_7]: (B_8=A_7 | ~r1_tarski(B_8, A_7) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 20.80/11.23  tff(c_9396, plain, (![B_1181, A_1182]: (B_1181=A_1182 | ~r1_tarski(B_1181, A_1182) | ~r1_ordinal1(A_1182, B_1181) | ~v3_ordinal1(B_1181) | ~v3_ordinal1(A_1182))), inference(resolution, [status(thm)], [c_715, c_20])).
% 20.80/11.23  tff(c_34779, plain, (![B_2828, A_2829]: (B_2828=A_2829 | ~r1_ordinal1(B_2828, A_2829) | ~r1_ordinal1(A_2829, B_2828) | ~v3_ordinal1(B_2828) | ~v3_ordinal1(A_2829))), inference(resolution, [status(thm)], [c_134, c_9396])).
% 20.80/11.23  tff(c_34811, plain, ('#skF_9'='#skF_8' | ~r1_ordinal1('#skF_9', '#skF_8') | ~v3_ordinal1('#skF_8') | ~v3_ordinal1('#skF_9')), inference(resolution, [status(thm)], [c_212, c_34779])).
% 20.80/11.23  tff(c_34832, plain, ('#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_140, c_142, c_492, c_34811])).
% 20.80/11.23  tff(c_34877, plain, (~r2_hidden('#skF_8', k1_ordinal1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_34832, c_171])).
% 20.80/11.23  tff(c_34883, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1246, c_34877])).
% 20.80/11.23  tff(c_34884, plain, (~r1_ordinal1('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_144])).
% 20.80/11.23  tff(c_153, plain, (![A_73]: (v1_ordinal1(A_73) | ~v3_ordinal1(A_73))), inference(cnfTransformation, [status(thm)], [f_107])).
% 20.80/11.23  tff(c_160, plain, (v1_ordinal1('#skF_9')), inference(resolution, [status(thm)], [c_140, c_153])).
% 20.80/11.23  tff(c_34885, plain, (r2_hidden('#skF_8', k1_ordinal1('#skF_9'))), inference(splitRight, [status(thm)], [c_144])).
% 20.80/11.23  tff(c_36255, plain, (![D_3049, B_3050, A_3051]: (r2_hidden(D_3049, B_3050) | r2_hidden(D_3049, A_3051) | ~r2_hidden(D_3049, k2_xboole_0(A_3051, B_3050)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 20.80/11.23  tff(c_36271, plain, (![D_3049, A_59]: (r2_hidden(D_3049, k1_tarski(A_59)) | r2_hidden(D_3049, A_59) | ~r2_hidden(D_3049, k1_ordinal1(A_59)))), inference(superposition, [status(thm), theory('equality')], [c_124, c_36255])).
% 20.80/11.23  tff(c_52, plain, (![A_17, B_18]: (k1_enumset1(A_17, A_17, B_18)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 20.80/11.23  tff(c_36471, plain, (![E_3056, C_3057, B_3058, A_3059]: (E_3056=C_3057 | E_3056=B_3058 | E_3056=A_3059 | ~r2_hidden(E_3056, k1_enumset1(A_3059, B_3058, C_3057)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 20.80/11.23  tff(c_42063, plain, (![E_3841, B_3842, A_3843]: (E_3841=B_3842 | E_3841=A_3843 | E_3841=A_3843 | ~r2_hidden(E_3841, k2_tarski(A_3843, B_3842)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_36471])).
% 20.80/11.23  tff(c_44964, plain, (![E_3966, A_3967]: (E_3966=A_3967 | E_3966=A_3967 | E_3966=A_3967 | ~r2_hidden(E_3966, k1_tarski(A_3967)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_42063])).
% 20.80/11.23  tff(c_45040, plain, (![D_3969, A_3970]: (D_3969=A_3970 | r2_hidden(D_3969, A_3970) | ~r2_hidden(D_3969, k1_ordinal1(A_3970)))), inference(resolution, [status(thm)], [c_36271, c_44964])).
% 20.80/11.23  tff(c_45122, plain, ('#skF_9'='#skF_8' | r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_34885, c_45040])).
% 20.80/11.23  tff(c_45123, plain, (r2_hidden('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_45122])).
% 20.80/11.23  tff(c_126, plain, (![B_63, A_60]: (r1_tarski(B_63, A_60) | ~r2_hidden(B_63, A_60) | ~v1_ordinal1(A_60))), inference(cnfTransformation, [status(thm)], [f_116])).
% 20.80/11.23  tff(c_45126, plain, (r1_tarski('#skF_8', '#skF_9') | ~v1_ordinal1('#skF_9')), inference(resolution, [status(thm)], [c_45123, c_126])).
% 20.80/11.23  tff(c_45132, plain, (r1_tarski('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_45126])).
% 20.80/11.23  tff(c_132, plain, (![A_64, B_65]: (r1_ordinal1(A_64, B_65) | ~r1_tarski(A_64, B_65) | ~v3_ordinal1(B_65) | ~v3_ordinal1(A_64))), inference(cnfTransformation, [status(thm)], [f_124])).
% 20.80/11.23  tff(c_45139, plain, (r1_ordinal1('#skF_8', '#skF_9') | ~v3_ordinal1('#skF_9') | ~v3_ordinal1('#skF_8')), inference(resolution, [status(thm)], [c_45132, c_132])).
% 20.80/11.23  tff(c_45147, plain, (r1_ordinal1('#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_140, c_45139])).
% 20.80/11.23  tff(c_45149, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34884, c_45147])).
% 20.80/11.23  tff(c_45150, plain, ('#skF_9'='#skF_8'), inference(splitRight, [status(thm)], [c_45122])).
% 20.80/11.23  tff(c_45218, plain, (~r1_ordinal1('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_45150, c_34884])).
% 20.80/11.23  tff(c_45239, plain, (~v3_ordinal1('#skF_8')), inference(resolution, [status(thm)], [c_35441, c_45218])).
% 20.80/11.23  tff(c_45243, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_45239])).
% 20.80/11.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.80/11.23  
% 20.80/11.23  Inference rules
% 20.80/11.23  ----------------------
% 20.80/11.23  #Ref     : 0
% 20.80/11.23  #Sup     : 9377
% 20.80/11.23  #Fact    : 44
% 20.80/11.23  #Define  : 0
% 20.80/11.23  #Split   : 5
% 20.80/11.23  #Chain   : 0
% 20.80/11.23  #Close   : 0
% 20.80/11.23  
% 20.80/11.23  Ordering : KBO
% 20.80/11.23  
% 20.80/11.23  Simplification rules
% 20.80/11.23  ----------------------
% 20.80/11.23  #Subsume      : 3243
% 20.80/11.23  #Demod        : 1299
% 20.80/11.23  #Tautology    : 300
% 20.80/11.23  #SimpNegUnit  : 180
% 20.80/11.23  #BackRed      : 115
% 20.80/11.23  
% 20.80/11.23  #Partial instantiations: 0
% 20.80/11.23  #Strategies tried      : 1
% 20.80/11.23  
% 20.80/11.23  Timing (in seconds)
% 20.80/11.23  ----------------------
% 20.80/11.23  Preprocessing        : 0.38
% 20.80/11.23  Parsing              : 0.17
% 20.80/11.23  CNF conversion       : 0.03
% 20.80/11.23  Main loop            : 10.10
% 20.80/11.23  Inferencing          : 1.66
% 20.80/11.23  Reduction            : 3.42
% 20.80/11.23  Demodulation         : 1.73
% 20.80/11.23  BG Simplification    : 0.19
% 20.80/11.23  Subsumption          : 4.15
% 20.80/11.23  Abstraction          : 0.28
% 20.80/11.23  MUC search           : 0.00
% 20.80/11.23  Cooper               : 0.00
% 20.80/11.23  Total                : 10.51
% 20.80/11.23  Index Insertion      : 0.00
% 20.80/11.23  Index Deletion       : 0.00
% 20.80/11.23  Index Matching       : 0.00
% 20.80/11.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
