%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:34 EST 2020

% Result     : Theorem 6.55s
% Output     : CNFRefutation 6.55s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 540 expanded)
%              Number of leaves         :   33 ( 204 expanded)
%              Depth                    :   16
%              Number of atoms          :  206 (1486 expanded)
%              Number of equality atoms :   25 ( 209 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_wellord1 > r2_hidden > r1_tarski > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(r4_wellord1,type,(
    r4_wellord1: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_131,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r4_wellord1(k1_wellord2(A),k1_wellord2(B))
             => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).

tff(f_117,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v2_wellord1(k1_wellord2(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).

tff(f_104,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
           => r4_wellord1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

tff(f_121,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_102,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_113,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
           => A = k1_wellord1(k1_wellord2(B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
       => ! [B] :
            ~ ( r2_hidden(B,k3_relat_1(A))
              & r4_wellord1(A,k2_wellord1(A,k1_wellord1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).

tff(f_55,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k1_wellord1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( D != B
                & r2_hidden(k4_tarski(D,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

tff(c_68,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_58,plain,(
    ! [A_42] :
      ( v2_wellord1(k1_wellord2(A_42))
      | ~ v3_ordinal1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_66,plain,(
    v3_ordinal1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_62,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_54,plain,(
    ! [A_38] : v1_relat_1(k1_wellord2(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_64,plain,(
    r4_wellord1(k1_wellord2('#skF_6'),k1_wellord2('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_108,plain,(
    ! [B_61,A_62] :
      ( r4_wellord1(B_61,A_62)
      | ~ r4_wellord1(A_62,B_61)
      | ~ v1_relat_1(B_61)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_110,plain,
    ( r4_wellord1(k1_wellord2('#skF_7'),k1_wellord2('#skF_6'))
    | ~ v1_relat_1(k1_wellord2('#skF_7'))
    | ~ v1_relat_1(k1_wellord2('#skF_6')) ),
    inference(resolution,[status(thm)],[c_64,c_108])).

tff(c_113,plain,(
    r4_wellord1(k1_wellord2('#skF_7'),k1_wellord2('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_110])).

tff(c_60,plain,(
    ! [B_44,A_43] :
      ( k2_wellord1(k1_wellord2(B_44),A_43) = k1_wellord2(A_43)
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_48,plain,(
    ! [A_30] :
      ( k3_relat_1(k1_wellord2(A_30)) = A_30
      | ~ v1_relat_1(k1_wellord2(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_74,plain,(
    ! [A_30] : k3_relat_1(k1_wellord2(A_30)) = A_30 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48])).

tff(c_56,plain,(
    ! [B_41,A_39] :
      ( k1_wellord1(k1_wellord2(B_41),A_39) = A_39
      | ~ r2_hidden(A_39,B_41)
      | ~ v3_ordinal1(B_41)
      | ~ v3_ordinal1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_531,plain,(
    ! [A_124,B_125] :
      ( ~ r4_wellord1(A_124,k2_wellord1(A_124,k1_wellord1(A_124,B_125)))
      | ~ r2_hidden(B_125,k3_relat_1(A_124))
      | ~ v2_wellord1(A_124)
      | ~ v1_relat_1(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_534,plain,(
    ! [B_41,A_39] :
      ( ~ r4_wellord1(k1_wellord2(B_41),k2_wellord1(k1_wellord2(B_41),A_39))
      | ~ r2_hidden(A_39,k3_relat_1(k1_wellord2(B_41)))
      | ~ v2_wellord1(k1_wellord2(B_41))
      | ~ v1_relat_1(k1_wellord2(B_41))
      | ~ r2_hidden(A_39,B_41)
      | ~ v3_ordinal1(B_41)
      | ~ v3_ordinal1(A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_531])).

tff(c_1993,plain,(
    ! [B_240,A_241] :
      ( ~ r4_wellord1(k1_wellord2(B_240),k2_wellord1(k1_wellord2(B_240),A_241))
      | ~ v2_wellord1(k1_wellord2(B_240))
      | ~ r2_hidden(A_241,B_240)
      | ~ v3_ordinal1(B_240)
      | ~ v3_ordinal1(A_241) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_74,c_534])).

tff(c_4212,plain,(
    ! [B_357,A_358] :
      ( ~ r4_wellord1(k1_wellord2(B_357),k1_wellord2(A_358))
      | ~ v2_wellord1(k1_wellord2(B_357))
      | ~ r2_hidden(A_358,B_357)
      | ~ v3_ordinal1(B_357)
      | ~ v3_ordinal1(A_358)
      | ~ r1_tarski(A_358,B_357) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_1993])).

tff(c_4215,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_7'))
    | ~ r2_hidden('#skF_6','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_6')
    | ~ r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_113,c_4212])).

tff(c_4221,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_7'))
    | ~ r2_hidden('#skF_6','#skF_7')
    | ~ r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_4215])).

tff(c_4225,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_4221])).

tff(c_12,plain,(
    ! [B_11,A_9] :
      ( r2_hidden(B_11,A_9)
      | B_11 = A_9
      | r2_hidden(A_9,B_11)
      | ~ v3_ordinal1(B_11)
      | ~ v3_ordinal1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_213,plain,(
    ! [D_78,B_79,A_80] :
      ( r2_hidden(k4_tarski(D_78,B_79),A_80)
      | ~ r2_hidden(D_78,k1_wellord1(A_80,B_79))
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_10,plain,(
    ! [A_6,C_8,B_7] :
      ( r2_hidden(A_6,k3_relat_1(C_8))
      | ~ r2_hidden(k4_tarski(A_6,B_7),C_8)
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_259,plain,(
    ! [D_84,A_85,B_86] :
      ( r2_hidden(D_84,k3_relat_1(A_85))
      | ~ r2_hidden(D_84,k1_wellord1(A_85,B_86))
      | ~ v1_relat_1(A_85) ) ),
    inference(resolution,[status(thm)],[c_213,c_10])).

tff(c_670,plain,(
    ! [A_150,B_151,B_152] :
      ( r2_hidden('#skF_1'(k1_wellord1(A_150,B_151),B_152),k3_relat_1(A_150))
      | ~ v1_relat_1(A_150)
      | r1_tarski(k1_wellord1(A_150,B_151),B_152) ) ),
    inference(resolution,[status(thm)],[c_6,c_259])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_708,plain,(
    ! [A_156,B_157] :
      ( ~ v1_relat_1(A_156)
      | r1_tarski(k1_wellord1(A_156,B_157),k3_relat_1(A_156)) ) ),
    inference(resolution,[status(thm)],[c_670,c_4])).

tff(c_719,plain,(
    ! [B_41,A_39] :
      ( ~ v1_relat_1(k1_wellord2(B_41))
      | r1_tarski(A_39,k3_relat_1(k1_wellord2(B_41)))
      | ~ r2_hidden(A_39,B_41)
      | ~ v3_ordinal1(B_41)
      | ~ v3_ordinal1(A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_708])).

tff(c_751,plain,(
    ! [A_160,B_161] :
      ( r1_tarski(A_160,B_161)
      | ~ r2_hidden(A_160,B_161)
      | ~ v3_ordinal1(B_161)
      | ~ v3_ordinal1(A_160) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_54,c_719])).

tff(c_792,plain,(
    ! [B_11,A_9] :
      ( r1_tarski(B_11,A_9)
      | B_11 = A_9
      | r2_hidden(A_9,B_11)
      | ~ v3_ordinal1(B_11)
      | ~ v3_ordinal1(A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_751])).

tff(c_893,plain,(
    ! [B_169,A_170] :
      ( r1_tarski(B_169,A_170)
      | B_169 = A_170
      | r2_hidden(A_170,B_169)
      | ~ v3_ordinal1(B_169)
      | ~ v3_ordinal1(A_170) ) ),
    inference(resolution,[status(thm)],[c_12,c_751])).

tff(c_728,plain,(
    ! [A_39,B_41] :
      ( r1_tarski(A_39,B_41)
      | ~ r2_hidden(A_39,B_41)
      | ~ v3_ordinal1(B_41)
      | ~ v3_ordinal1(A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_54,c_719])).

tff(c_942,plain,(
    ! [A_170,B_169] :
      ( r1_tarski(A_170,B_169)
      | r1_tarski(B_169,A_170)
      | B_169 = A_170
      | ~ v3_ordinal1(B_169)
      | ~ v3_ordinal1(A_170) ) ),
    inference(resolution,[status(thm)],[c_893,c_728])).

tff(c_4218,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_6'))
    | ~ r2_hidden('#skF_7','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_7')
    | ~ r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_4212])).

tff(c_4224,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_6'))
    | ~ r2_hidden('#skF_7','#skF_6')
    | ~ r1_tarski('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_4218])).

tff(c_4229,plain,(
    ~ r1_tarski('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_4224])).

tff(c_4233,plain,
    ( r1_tarski('#skF_6','#skF_7')
    | '#skF_7' = '#skF_6'
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_942,c_4229])).

tff(c_4239,plain,
    ( r1_tarski('#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_4233])).

tff(c_4241,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_4225,c_4239])).

tff(c_4242,plain,
    ( ~ r2_hidden('#skF_7','#skF_6')
    | ~ v2_wellord1(k1_wellord2('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_4224])).

tff(c_4360,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_4242])).

tff(c_4363,plain,(
    ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_4360])).

tff(c_4367,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_4363])).

tff(c_4368,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(splitRight,[status(thm)],[c_4242])).

tff(c_4373,plain,
    ( r1_tarski('#skF_6','#skF_7')
    | '#skF_7' = '#skF_6'
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_792,c_4368])).

tff(c_4382,plain,
    ( r1_tarski('#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_4373])).

tff(c_4384,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_4225,c_4382])).

tff(c_4385,plain,
    ( ~ r2_hidden('#skF_6','#skF_7')
    | ~ v2_wellord1(k1_wellord2('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_4221])).

tff(c_4414,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_4385])).

tff(c_4417,plain,(
    ~ v3_ordinal1('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_4414])).

tff(c_4421,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_4417])).

tff(c_4422,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_4385])).

tff(c_4427,plain,
    ( r1_tarski('#skF_7','#skF_6')
    | '#skF_7' = '#skF_6'
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_792,c_4422])).

tff(c_4432,plain,
    ( r1_tarski('#skF_7','#skF_6')
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_4427])).

tff(c_4433,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_4432])).

tff(c_4751,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_6'))
    | ~ r2_hidden('#skF_7','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4433,c_4224])).

tff(c_4752,plain,(
    ~ r2_hidden('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_4751])).

tff(c_4759,plain,
    ( '#skF_7' = '#skF_6'
    | r2_hidden('#skF_6','#skF_7')
    | ~ v3_ordinal1('#skF_7')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_12,c_4752])).

tff(c_4769,plain,
    ( '#skF_7' = '#skF_6'
    | r2_hidden('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_4759])).

tff(c_4771,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4422,c_62,c_4769])).

tff(c_4772,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_4751])).

tff(c_4776,plain,(
    ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_4772])).

tff(c_4780,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_4776])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n023.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 19:06:35 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.55/2.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.55/2.33  
% 6.55/2.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.55/2.33  %$ r4_wellord1 > r2_hidden > r1_tarski > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 6.55/2.33  
% 6.55/2.33  %Foreground sorts:
% 6.55/2.33  
% 6.55/2.33  
% 6.55/2.33  %Background operators:
% 6.55/2.33  
% 6.55/2.33  
% 6.55/2.33  %Foreground operators:
% 6.55/2.33  tff(r4_wellord1, type, r4_wellord1: ($i * $i) > $o).
% 6.55/2.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.55/2.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.55/2.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.55/2.33  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 6.55/2.33  tff('#skF_7', type, '#skF_7': $i).
% 6.55/2.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.55/2.33  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 6.55/2.33  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 6.55/2.33  tff('#skF_6', type, '#skF_6': $i).
% 6.55/2.33  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.55/2.33  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 6.55/2.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.55/2.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.55/2.33  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 6.55/2.33  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.55/2.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.55/2.33  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 6.55/2.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.55/2.33  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 6.55/2.33  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.55/2.33  
% 6.55/2.35  tff(f_131, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r4_wellord1(k1_wellord2(A), k1_wellord2(B)) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_wellord2)).
% 6.55/2.35  tff(f_117, axiom, (![A]: (v3_ordinal1(A) => v2_wellord1(k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_wellord2)).
% 6.55/2.35  tff(f_104, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 6.55/2.35  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r4_wellord1(A, B) => r4_wellord1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_wellord1)).
% 6.55/2.35  tff(f_121, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_wellord2)).
% 6.55/2.35  tff(f_102, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 6.55/2.35  tff(f_113, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) => (A = k1_wellord1(k1_wellord2(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_wellord2)).
% 6.55/2.35  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) => (![B]: ~(r2_hidden(B, k3_relat_1(A)) & r4_wellord1(A, k2_wellord1(A, k1_wellord1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_wellord1)).
% 6.55/2.35  tff(f_55, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 6.55/2.35  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.55/2.35  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k1_wellord1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (~(D = B) & r2_hidden(k4_tarski(D, B), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord1)).
% 6.55/2.35  tff(f_40, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relat_1)).
% 6.55/2.35  tff(c_68, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.55/2.35  tff(c_58, plain, (![A_42]: (v2_wellord1(k1_wellord2(A_42)) | ~v3_ordinal1(A_42))), inference(cnfTransformation, [status(thm)], [f_117])).
% 6.55/2.35  tff(c_66, plain, (v3_ordinal1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.55/2.35  tff(c_62, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.55/2.35  tff(c_54, plain, (![A_38]: (v1_relat_1(k1_wellord2(A_38)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.55/2.35  tff(c_64, plain, (r4_wellord1(k1_wellord2('#skF_6'), k1_wellord2('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.55/2.35  tff(c_108, plain, (![B_61, A_62]: (r4_wellord1(B_61, A_62) | ~r4_wellord1(A_62, B_61) | ~v1_relat_1(B_61) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.55/2.35  tff(c_110, plain, (r4_wellord1(k1_wellord2('#skF_7'), k1_wellord2('#skF_6')) | ~v1_relat_1(k1_wellord2('#skF_7')) | ~v1_relat_1(k1_wellord2('#skF_6'))), inference(resolution, [status(thm)], [c_64, c_108])).
% 6.55/2.35  tff(c_113, plain, (r4_wellord1(k1_wellord2('#skF_7'), k1_wellord2('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_54, c_110])).
% 6.55/2.35  tff(c_60, plain, (![B_44, A_43]: (k2_wellord1(k1_wellord2(B_44), A_43)=k1_wellord2(A_43) | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_121])).
% 6.55/2.35  tff(c_48, plain, (![A_30]: (k3_relat_1(k1_wellord2(A_30))=A_30 | ~v1_relat_1(k1_wellord2(A_30)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.55/2.35  tff(c_74, plain, (![A_30]: (k3_relat_1(k1_wellord2(A_30))=A_30)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_48])).
% 6.55/2.35  tff(c_56, plain, (![B_41, A_39]: (k1_wellord1(k1_wellord2(B_41), A_39)=A_39 | ~r2_hidden(A_39, B_41) | ~v3_ordinal1(B_41) | ~v3_ordinal1(A_39))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.55/2.35  tff(c_531, plain, (![A_124, B_125]: (~r4_wellord1(A_124, k2_wellord1(A_124, k1_wellord1(A_124, B_125))) | ~r2_hidden(B_125, k3_relat_1(A_124)) | ~v2_wellord1(A_124) | ~v1_relat_1(A_124))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.55/2.35  tff(c_534, plain, (![B_41, A_39]: (~r4_wellord1(k1_wellord2(B_41), k2_wellord1(k1_wellord2(B_41), A_39)) | ~r2_hidden(A_39, k3_relat_1(k1_wellord2(B_41))) | ~v2_wellord1(k1_wellord2(B_41)) | ~v1_relat_1(k1_wellord2(B_41)) | ~r2_hidden(A_39, B_41) | ~v3_ordinal1(B_41) | ~v3_ordinal1(A_39))), inference(superposition, [status(thm), theory('equality')], [c_56, c_531])).
% 6.55/2.35  tff(c_1993, plain, (![B_240, A_241]: (~r4_wellord1(k1_wellord2(B_240), k2_wellord1(k1_wellord2(B_240), A_241)) | ~v2_wellord1(k1_wellord2(B_240)) | ~r2_hidden(A_241, B_240) | ~v3_ordinal1(B_240) | ~v3_ordinal1(A_241))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_74, c_534])).
% 6.55/2.35  tff(c_4212, plain, (![B_357, A_358]: (~r4_wellord1(k1_wellord2(B_357), k1_wellord2(A_358)) | ~v2_wellord1(k1_wellord2(B_357)) | ~r2_hidden(A_358, B_357) | ~v3_ordinal1(B_357) | ~v3_ordinal1(A_358) | ~r1_tarski(A_358, B_357))), inference(superposition, [status(thm), theory('equality')], [c_60, c_1993])).
% 6.55/2.35  tff(c_4215, plain, (~v2_wellord1(k1_wellord2('#skF_7')) | ~r2_hidden('#skF_6', '#skF_7') | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_6') | ~r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_113, c_4212])).
% 6.55/2.35  tff(c_4221, plain, (~v2_wellord1(k1_wellord2('#skF_7')) | ~r2_hidden('#skF_6', '#skF_7') | ~r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_4215])).
% 6.55/2.35  tff(c_4225, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_4221])).
% 6.55/2.35  tff(c_12, plain, (![B_11, A_9]: (r2_hidden(B_11, A_9) | B_11=A_9 | r2_hidden(A_9, B_11) | ~v3_ordinal1(B_11) | ~v3_ordinal1(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.55/2.35  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.55/2.35  tff(c_213, plain, (![D_78, B_79, A_80]: (r2_hidden(k4_tarski(D_78, B_79), A_80) | ~r2_hidden(D_78, k1_wellord1(A_80, B_79)) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.55/2.35  tff(c_10, plain, (![A_6, C_8, B_7]: (r2_hidden(A_6, k3_relat_1(C_8)) | ~r2_hidden(k4_tarski(A_6, B_7), C_8) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.55/2.35  tff(c_259, plain, (![D_84, A_85, B_86]: (r2_hidden(D_84, k3_relat_1(A_85)) | ~r2_hidden(D_84, k1_wellord1(A_85, B_86)) | ~v1_relat_1(A_85))), inference(resolution, [status(thm)], [c_213, c_10])).
% 6.55/2.35  tff(c_670, plain, (![A_150, B_151, B_152]: (r2_hidden('#skF_1'(k1_wellord1(A_150, B_151), B_152), k3_relat_1(A_150)) | ~v1_relat_1(A_150) | r1_tarski(k1_wellord1(A_150, B_151), B_152))), inference(resolution, [status(thm)], [c_6, c_259])).
% 6.55/2.35  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.55/2.35  tff(c_708, plain, (![A_156, B_157]: (~v1_relat_1(A_156) | r1_tarski(k1_wellord1(A_156, B_157), k3_relat_1(A_156)))), inference(resolution, [status(thm)], [c_670, c_4])).
% 6.55/2.35  tff(c_719, plain, (![B_41, A_39]: (~v1_relat_1(k1_wellord2(B_41)) | r1_tarski(A_39, k3_relat_1(k1_wellord2(B_41))) | ~r2_hidden(A_39, B_41) | ~v3_ordinal1(B_41) | ~v3_ordinal1(A_39))), inference(superposition, [status(thm), theory('equality')], [c_56, c_708])).
% 6.55/2.35  tff(c_751, plain, (![A_160, B_161]: (r1_tarski(A_160, B_161) | ~r2_hidden(A_160, B_161) | ~v3_ordinal1(B_161) | ~v3_ordinal1(A_160))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_54, c_719])).
% 6.55/2.35  tff(c_792, plain, (![B_11, A_9]: (r1_tarski(B_11, A_9) | B_11=A_9 | r2_hidden(A_9, B_11) | ~v3_ordinal1(B_11) | ~v3_ordinal1(A_9))), inference(resolution, [status(thm)], [c_12, c_751])).
% 6.55/2.35  tff(c_893, plain, (![B_169, A_170]: (r1_tarski(B_169, A_170) | B_169=A_170 | r2_hidden(A_170, B_169) | ~v3_ordinal1(B_169) | ~v3_ordinal1(A_170))), inference(resolution, [status(thm)], [c_12, c_751])).
% 6.55/2.35  tff(c_728, plain, (![A_39, B_41]: (r1_tarski(A_39, B_41) | ~r2_hidden(A_39, B_41) | ~v3_ordinal1(B_41) | ~v3_ordinal1(A_39))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_54, c_719])).
% 6.55/2.35  tff(c_942, plain, (![A_170, B_169]: (r1_tarski(A_170, B_169) | r1_tarski(B_169, A_170) | B_169=A_170 | ~v3_ordinal1(B_169) | ~v3_ordinal1(A_170))), inference(resolution, [status(thm)], [c_893, c_728])).
% 6.55/2.35  tff(c_4218, plain, (~v2_wellord1(k1_wellord2('#skF_6')) | ~r2_hidden('#skF_7', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_7') | ~r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_64, c_4212])).
% 6.55/2.35  tff(c_4224, plain, (~v2_wellord1(k1_wellord2('#skF_6')) | ~r2_hidden('#skF_7', '#skF_6') | ~r1_tarski('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_4218])).
% 6.55/2.35  tff(c_4229, plain, (~r1_tarski('#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_4224])).
% 6.55/2.35  tff(c_4233, plain, (r1_tarski('#skF_6', '#skF_7') | '#skF_7'='#skF_6' | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_7')), inference(resolution, [status(thm)], [c_942, c_4229])).
% 6.55/2.35  tff(c_4239, plain, (r1_tarski('#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_4233])).
% 6.55/2.35  tff(c_4241, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_4225, c_4239])).
% 6.55/2.35  tff(c_4242, plain, (~r2_hidden('#skF_7', '#skF_6') | ~v2_wellord1(k1_wellord2('#skF_6'))), inference(splitRight, [status(thm)], [c_4224])).
% 6.55/2.35  tff(c_4360, plain, (~v2_wellord1(k1_wellord2('#skF_6'))), inference(splitLeft, [status(thm)], [c_4242])).
% 6.55/2.35  tff(c_4363, plain, (~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_4360])).
% 6.55/2.35  tff(c_4367, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_4363])).
% 6.55/2.35  tff(c_4368, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(splitRight, [status(thm)], [c_4242])).
% 6.55/2.35  tff(c_4373, plain, (r1_tarski('#skF_6', '#skF_7') | '#skF_7'='#skF_6' | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_7')), inference(resolution, [status(thm)], [c_792, c_4368])).
% 6.55/2.35  tff(c_4382, plain, (r1_tarski('#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_4373])).
% 6.55/2.35  tff(c_4384, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_4225, c_4382])).
% 6.55/2.35  tff(c_4385, plain, (~r2_hidden('#skF_6', '#skF_7') | ~v2_wellord1(k1_wellord2('#skF_7'))), inference(splitRight, [status(thm)], [c_4221])).
% 6.55/2.35  tff(c_4414, plain, (~v2_wellord1(k1_wellord2('#skF_7'))), inference(splitLeft, [status(thm)], [c_4385])).
% 6.55/2.35  tff(c_4417, plain, (~v3_ordinal1('#skF_7')), inference(resolution, [status(thm)], [c_58, c_4414])).
% 6.55/2.35  tff(c_4421, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_4417])).
% 6.55/2.35  tff(c_4422, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_4385])).
% 6.55/2.35  tff(c_4427, plain, (r1_tarski('#skF_7', '#skF_6') | '#skF_7'='#skF_6' | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_792, c_4422])).
% 6.55/2.35  tff(c_4432, plain, (r1_tarski('#skF_7', '#skF_6') | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_4427])).
% 6.55/2.35  tff(c_4433, plain, (r1_tarski('#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_62, c_4432])).
% 6.55/2.35  tff(c_4751, plain, (~v2_wellord1(k1_wellord2('#skF_6')) | ~r2_hidden('#skF_7', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4433, c_4224])).
% 6.55/2.35  tff(c_4752, plain, (~r2_hidden('#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_4751])).
% 6.55/2.35  tff(c_4759, plain, ('#skF_7'='#skF_6' | r2_hidden('#skF_6', '#skF_7') | ~v3_ordinal1('#skF_7') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_12, c_4752])).
% 6.55/2.35  tff(c_4769, plain, ('#skF_7'='#skF_6' | r2_hidden('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_4759])).
% 6.55/2.35  tff(c_4771, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4422, c_62, c_4769])).
% 6.55/2.35  tff(c_4772, plain, (~v2_wellord1(k1_wellord2('#skF_6'))), inference(splitRight, [status(thm)], [c_4751])).
% 6.55/2.35  tff(c_4776, plain, (~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_4772])).
% 6.55/2.35  tff(c_4780, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_4776])).
% 6.55/2.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.55/2.35  
% 6.55/2.35  Inference rules
% 6.55/2.35  ----------------------
% 6.55/2.35  #Ref     : 0
% 6.55/2.35  #Sup     : 1142
% 6.55/2.35  #Fact    : 6
% 6.55/2.35  #Define  : 0
% 6.55/2.35  #Split   : 8
% 6.55/2.35  #Chain   : 0
% 6.55/2.35  #Close   : 0
% 6.55/2.35  
% 6.55/2.35  Ordering : KBO
% 6.55/2.35  
% 6.55/2.35  Simplification rules
% 6.55/2.35  ----------------------
% 6.55/2.35  #Subsume      : 319
% 6.55/2.35  #Demod        : 196
% 6.55/2.35  #Tautology    : 56
% 6.55/2.35  #SimpNegUnit  : 8
% 6.55/2.35  #BackRed      : 3
% 6.55/2.35  
% 6.55/2.35  #Partial instantiations: 0
% 6.55/2.35  #Strategies tried      : 1
% 6.55/2.35  
% 6.55/2.35  Timing (in seconds)
% 6.55/2.35  ----------------------
% 6.55/2.35  Preprocessing        : 0.35
% 6.55/2.35  Parsing              : 0.18
% 6.55/2.35  CNF conversion       : 0.03
% 6.55/2.35  Main loop            : 1.21
% 6.55/2.35  Inferencing          : 0.34
% 6.55/2.35  Reduction            : 0.28
% 6.55/2.35  Demodulation         : 0.19
% 6.55/2.35  BG Simplification    : 0.05
% 6.55/2.35  Subsumption          : 0.44
% 6.55/2.35  Abstraction          : 0.06
% 6.55/2.35  MUC search           : 0.00
% 6.55/2.35  Cooper               : 0.00
% 6.55/2.35  Total                : 1.59
% 6.55/2.35  Index Insertion      : 0.00
% 6.55/2.35  Index Deletion       : 0.00
% 6.55/2.35  Index Matching       : 0.00
% 6.55/2.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
