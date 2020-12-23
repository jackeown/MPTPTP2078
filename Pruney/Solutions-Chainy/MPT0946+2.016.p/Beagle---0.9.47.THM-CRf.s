%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:33 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 367 expanded)
%              Number of leaves         :   37 ( 147 expanded)
%              Depth                    :   13
%              Number of atoms          :  203 ( 976 expanded)
%              Number of equality atoms :   24 ( 129 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_wellord1 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_xboole_0 > k2_wellord1 > k2_tarski > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > k1_tarski > k1_ordinal1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_140,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r4_wellord1(k1_wellord2(A),k1_wellord2(B))
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_113,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
           => r4_wellord1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

tff(f_130,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_111,axiom,(
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

tff(f_122,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
           => A = k1_wellord1(k1_wellord2(B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).

tff(f_96,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
       => ! [B] :
            ~ ( r2_hidden(B,k3_relat_1(A))
              & r4_wellord1(A,k2_wellord1(A,k1_wellord1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).

tff(f_68,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_77,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,k1_ordinal1(B))
          <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_126,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v2_wellord1(k1_wellord2(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).

tff(c_58,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_64,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_62,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | ~ r1_ordinal1(A_8,B_9)
      | ~ v3_ordinal1(B_9)
      | ~ v3_ordinal1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_50,plain,(
    ! [A_34] : v1_relat_1(k1_wellord2(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_60,plain,(
    r4_wellord1(k1_wellord2('#skF_3'),k1_wellord2('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_150,plain,(
    ! [B_64,A_65] :
      ( r4_wellord1(B_64,A_65)
      | ~ r4_wellord1(A_65,B_64)
      | ~ v1_relat_1(B_64)
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_152,plain,
    ( r4_wellord1(k1_wellord2('#skF_4'),k1_wellord2('#skF_3'))
    | ~ v1_relat_1(k1_wellord2('#skF_4'))
    | ~ v1_relat_1(k1_wellord2('#skF_3')) ),
    inference(resolution,[status(thm)],[c_60,c_150])).

tff(c_155,plain,(
    r4_wellord1(k1_wellord2('#skF_4'),k1_wellord2('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_152])).

tff(c_56,plain,(
    ! [B_40,A_39] :
      ( k2_wellord1(k1_wellord2(B_40),A_39) = k1_wellord2(A_39)
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_44,plain,(
    ! [A_26] :
      ( k3_relat_1(k1_wellord2(A_26)) = A_26
      | ~ v1_relat_1(k1_wellord2(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_70,plain,(
    ! [A_26] : k3_relat_1(k1_wellord2(A_26)) = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_44])).

tff(c_52,plain,(
    ! [B_37,A_35] :
      ( k1_wellord1(k1_wellord2(B_37),A_35) = A_35
      | ~ r2_hidden(A_35,B_37)
      | ~ v3_ordinal1(B_37)
      | ~ v3_ordinal1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_371,plain,(
    ! [A_96,B_97] :
      ( ~ r4_wellord1(A_96,k2_wellord1(A_96,k1_wellord1(A_96,B_97)))
      | ~ r2_hidden(B_97,k3_relat_1(A_96))
      | ~ v2_wellord1(A_96)
      | ~ v1_relat_1(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_374,plain,(
    ! [B_37,A_35] :
      ( ~ r4_wellord1(k1_wellord2(B_37),k2_wellord1(k1_wellord2(B_37),A_35))
      | ~ r2_hidden(A_35,k3_relat_1(k1_wellord2(B_37)))
      | ~ v2_wellord1(k1_wellord2(B_37))
      | ~ v1_relat_1(k1_wellord2(B_37))
      | ~ r2_hidden(A_35,B_37)
      | ~ v3_ordinal1(B_37)
      | ~ v3_ordinal1(A_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_371])).

tff(c_488,plain,(
    ! [B_112,A_113] :
      ( ~ r4_wellord1(k1_wellord2(B_112),k2_wellord1(k1_wellord2(B_112),A_113))
      | ~ v2_wellord1(k1_wellord2(B_112))
      | ~ r2_hidden(A_113,B_112)
      | ~ v3_ordinal1(B_112)
      | ~ v3_ordinal1(A_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_70,c_374])).

tff(c_629,plain,(
    ! [B_125,A_126] :
      ( ~ r4_wellord1(k1_wellord2(B_125),k1_wellord2(A_126))
      | ~ v2_wellord1(k1_wellord2(B_125))
      | ~ r2_hidden(A_126,B_125)
      | ~ v3_ordinal1(B_125)
      | ~ v3_ordinal1(A_126)
      | ~ r1_tarski(A_126,B_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_488])).

tff(c_632,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_155,c_629])).

tff(c_638,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_632])).

tff(c_642,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_638])).

tff(c_645,plain,
    ( ~ r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_642])).

tff(c_648,plain,(
    ~ r1_ordinal1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_645])).

tff(c_229,plain,(
    ! [B_80,A_81] :
      ( r2_hidden(B_80,A_81)
      | B_80 = A_81
      | r2_hidden(A_81,B_80)
      | ~ v3_ordinal1(B_80)
      | ~ v3_ordinal1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( ~ r2_hidden(A_10,B_11)
      | r2_hidden(A_10,k1_ordinal1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_167,plain,(
    ! [A_70,B_71] :
      ( r1_ordinal1(A_70,B_71)
      | ~ r2_hidden(A_70,k1_ordinal1(B_71))
      | ~ v3_ordinal1(B_71)
      | ~ v3_ordinal1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_174,plain,(
    ! [A_10,B_11] :
      ( r1_ordinal1(A_10,B_11)
      | ~ v3_ordinal1(B_11)
      | ~ v3_ordinal1(A_10)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(resolution,[status(thm)],[c_18,c_167])).

tff(c_262,plain,(
    ! [A_81,B_80] :
      ( r1_ordinal1(A_81,B_80)
      | r2_hidden(B_80,A_81)
      | B_80 = A_81
      | ~ v3_ordinal1(B_80)
      | ~ v3_ordinal1(A_81) ) ),
    inference(resolution,[status(thm)],[c_229,c_174])).

tff(c_54,plain,(
    ! [A_38] :
      ( v2_wellord1(k1_wellord2(A_38))
      | ~ v3_ordinal1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_304,plain,(
    ! [A_85,B_86] :
      ( r1_ordinal1(A_85,B_86)
      | r2_hidden(B_86,A_85)
      | B_86 = A_85
      | ~ v3_ordinal1(B_86)
      | ~ v3_ordinal1(A_85) ) ),
    inference(resolution,[status(thm)],[c_229,c_174])).

tff(c_319,plain,(
    ! [B_86,A_85] :
      ( r1_ordinal1(B_86,A_85)
      | r1_ordinal1(A_85,B_86)
      | B_86 = A_85
      | ~ v3_ordinal1(B_86)
      | ~ v3_ordinal1(A_85) ) ),
    inference(resolution,[status(thm)],[c_304,c_174])).

tff(c_651,plain,
    ( r1_ordinal1('#skF_4','#skF_3')
    | '#skF_3' = '#skF_4'
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_319,c_648])).

tff(c_657,plain,
    ( r1_ordinal1('#skF_4','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_64,c_651])).

tff(c_658,plain,(
    r1_ordinal1('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_657])).

tff(c_635,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_3'))
    | ~ r2_hidden('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_629])).

tff(c_641,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_3'))
    | ~ r2_hidden('#skF_4','#skF_3')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_64,c_635])).

tff(c_675,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_641])).

tff(c_678,plain,
    ( ~ r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_675])).

tff(c_682,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_64,c_658,c_678])).

tff(c_683,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | ~ v2_wellord1(k1_wellord2('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_641])).

tff(c_691,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_683])).

tff(c_694,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_691])).

tff(c_698,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_694])).

tff(c_699,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_683])).

tff(c_703,plain,
    ( r1_ordinal1('#skF_3','#skF_4')
    | '#skF_3' = '#skF_4'
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_262,c_699])).

tff(c_711,plain,
    ( r1_ordinal1('#skF_3','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_703])).

tff(c_713,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_648,c_711])).

tff(c_715,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_638])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( r1_ordinal1(A_8,B_9)
      | ~ r1_tarski(A_8,B_9)
      | ~ v3_ordinal1(B_9)
      | ~ v3_ordinal1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_718,plain,
    ( r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_715,c_10])).

tff(c_721,plain,(
    r1_ordinal1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_718])).

tff(c_186,plain,(
    ! [A_75,B_76] :
      ( r2_hidden(A_75,k1_ordinal1(B_76))
      | ~ r1_ordinal1(A_75,B_76)
      | ~ v3_ordinal1(B_76)
      | ~ v3_ordinal1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | r2_hidden(A_10,B_11)
      | ~ r2_hidden(A_10,k1_ordinal1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_201,plain,(
    ! [B_76,A_75] :
      ( B_76 = A_75
      | r2_hidden(A_75,B_76)
      | ~ r1_ordinal1(A_75,B_76)
      | ~ v3_ordinal1(B_76)
      | ~ v3_ordinal1(A_75) ) ),
    inference(resolution,[status(thm)],[c_186,c_14])).

tff(c_714,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | ~ v2_wellord1(k1_wellord2('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_638])).

tff(c_733,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_714])).

tff(c_736,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_733])).

tff(c_740,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_736])).

tff(c_741,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_714])).

tff(c_748,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_201,c_741])).

tff(c_761,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_721,c_748])).

tff(c_763,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_761])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:37:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.18/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.62  
% 3.18/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.63  %$ r4_wellord1 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_xboole_0 > k2_wellord1 > k2_tarski > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > k1_tarski > k1_ordinal1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.18/1.63  
% 3.18/1.63  %Foreground sorts:
% 3.18/1.63  
% 3.18/1.63  
% 3.18/1.63  %Background operators:
% 3.18/1.63  
% 3.18/1.63  
% 3.18/1.63  %Foreground operators:
% 3.18/1.63  tff(r4_wellord1, type, r4_wellord1: ($i * $i) > $o).
% 3.18/1.63  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 3.18/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.18/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.18/1.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.18/1.63  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.18/1.63  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.18/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.18/1.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.18/1.63  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 3.18/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.18/1.63  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 3.18/1.63  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 3.18/1.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.18/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.18/1.63  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 3.18/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.18/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.18/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.18/1.63  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 3.18/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.18/1.63  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.18/1.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.18/1.63  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 3.18/1.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.18/1.63  
% 3.18/1.64  tff(f_140, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r4_wellord1(k1_wellord2(A), k1_wellord2(B)) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_wellord2)).
% 3.18/1.64  tff(f_41, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 3.18/1.64  tff(f_113, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 3.18/1.64  tff(f_86, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r4_wellord1(A, B) => r4_wellord1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_wellord1)).
% 3.18/1.64  tff(f_130, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_wellord2)).
% 3.18/1.64  tff(f_111, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 3.18/1.64  tff(f_122, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) => (A = k1_wellord1(k1_wellord2(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_wellord2)).
% 3.18/1.64  tff(f_96, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) => (![B]: ~(r2_hidden(B, k3_relat_1(A)) & r4_wellord1(A, k2_wellord1(A, k1_wellord1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_wellord1)).
% 3.18/1.64  tff(f_68, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 3.18/1.64  tff(f_47, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 3.18/1.64  tff(f_77, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 3.18/1.64  tff(f_126, axiom, (![A]: (v3_ordinal1(A) => v2_wellord1(k1_wellord2(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_wellord2)).
% 3.18/1.64  tff(c_58, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.18/1.64  tff(c_64, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.18/1.64  tff(c_62, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.18/1.64  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | ~r1_ordinal1(A_8, B_9) | ~v3_ordinal1(B_9) | ~v3_ordinal1(A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.18/1.64  tff(c_50, plain, (![A_34]: (v1_relat_1(k1_wellord2(A_34)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.18/1.64  tff(c_60, plain, (r4_wellord1(k1_wellord2('#skF_3'), k1_wellord2('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.18/1.64  tff(c_150, plain, (![B_64, A_65]: (r4_wellord1(B_64, A_65) | ~r4_wellord1(A_65, B_64) | ~v1_relat_1(B_64) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.18/1.64  tff(c_152, plain, (r4_wellord1(k1_wellord2('#skF_4'), k1_wellord2('#skF_3')) | ~v1_relat_1(k1_wellord2('#skF_4')) | ~v1_relat_1(k1_wellord2('#skF_3'))), inference(resolution, [status(thm)], [c_60, c_150])).
% 3.18/1.64  tff(c_155, plain, (r4_wellord1(k1_wellord2('#skF_4'), k1_wellord2('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_152])).
% 3.18/1.64  tff(c_56, plain, (![B_40, A_39]: (k2_wellord1(k1_wellord2(B_40), A_39)=k1_wellord2(A_39) | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.18/1.64  tff(c_44, plain, (![A_26]: (k3_relat_1(k1_wellord2(A_26))=A_26 | ~v1_relat_1(k1_wellord2(A_26)))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.18/1.64  tff(c_70, plain, (![A_26]: (k3_relat_1(k1_wellord2(A_26))=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_44])).
% 3.18/1.64  tff(c_52, plain, (![B_37, A_35]: (k1_wellord1(k1_wellord2(B_37), A_35)=A_35 | ~r2_hidden(A_35, B_37) | ~v3_ordinal1(B_37) | ~v3_ordinal1(A_35))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.18/1.64  tff(c_371, plain, (![A_96, B_97]: (~r4_wellord1(A_96, k2_wellord1(A_96, k1_wellord1(A_96, B_97))) | ~r2_hidden(B_97, k3_relat_1(A_96)) | ~v2_wellord1(A_96) | ~v1_relat_1(A_96))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.18/1.64  tff(c_374, plain, (![B_37, A_35]: (~r4_wellord1(k1_wellord2(B_37), k2_wellord1(k1_wellord2(B_37), A_35)) | ~r2_hidden(A_35, k3_relat_1(k1_wellord2(B_37))) | ~v2_wellord1(k1_wellord2(B_37)) | ~v1_relat_1(k1_wellord2(B_37)) | ~r2_hidden(A_35, B_37) | ~v3_ordinal1(B_37) | ~v3_ordinal1(A_35))), inference(superposition, [status(thm), theory('equality')], [c_52, c_371])).
% 3.18/1.64  tff(c_488, plain, (![B_112, A_113]: (~r4_wellord1(k1_wellord2(B_112), k2_wellord1(k1_wellord2(B_112), A_113)) | ~v2_wellord1(k1_wellord2(B_112)) | ~r2_hidden(A_113, B_112) | ~v3_ordinal1(B_112) | ~v3_ordinal1(A_113))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_70, c_374])).
% 3.18/1.64  tff(c_629, plain, (![B_125, A_126]: (~r4_wellord1(k1_wellord2(B_125), k1_wellord2(A_126)) | ~v2_wellord1(k1_wellord2(B_125)) | ~r2_hidden(A_126, B_125) | ~v3_ordinal1(B_125) | ~v3_ordinal1(A_126) | ~r1_tarski(A_126, B_125))), inference(superposition, [status(thm), theory('equality')], [c_56, c_488])).
% 3.18/1.64  tff(c_632, plain, (~v2_wellord1(k1_wellord2('#skF_4')) | ~r2_hidden('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3') | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_155, c_629])).
% 3.18/1.64  tff(c_638, plain, (~v2_wellord1(k1_wellord2('#skF_4')) | ~r2_hidden('#skF_3', '#skF_4') | ~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_632])).
% 3.18/1.64  tff(c_642, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_638])).
% 3.18/1.64  tff(c_645, plain, (~r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_642])).
% 3.18/1.64  tff(c_648, plain, (~r1_ordinal1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_645])).
% 3.18/1.64  tff(c_229, plain, (![B_80, A_81]: (r2_hidden(B_80, A_81) | B_80=A_81 | r2_hidden(A_81, B_80) | ~v3_ordinal1(B_80) | ~v3_ordinal1(A_81))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.18/1.64  tff(c_18, plain, (![A_10, B_11]: (~r2_hidden(A_10, B_11) | r2_hidden(A_10, k1_ordinal1(B_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.18/1.64  tff(c_167, plain, (![A_70, B_71]: (r1_ordinal1(A_70, B_71) | ~r2_hidden(A_70, k1_ordinal1(B_71)) | ~v3_ordinal1(B_71) | ~v3_ordinal1(A_70))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.18/1.64  tff(c_174, plain, (![A_10, B_11]: (r1_ordinal1(A_10, B_11) | ~v3_ordinal1(B_11) | ~v3_ordinal1(A_10) | ~r2_hidden(A_10, B_11))), inference(resolution, [status(thm)], [c_18, c_167])).
% 3.18/1.64  tff(c_262, plain, (![A_81, B_80]: (r1_ordinal1(A_81, B_80) | r2_hidden(B_80, A_81) | B_80=A_81 | ~v3_ordinal1(B_80) | ~v3_ordinal1(A_81))), inference(resolution, [status(thm)], [c_229, c_174])).
% 3.18/1.64  tff(c_54, plain, (![A_38]: (v2_wellord1(k1_wellord2(A_38)) | ~v3_ordinal1(A_38))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.18/1.64  tff(c_304, plain, (![A_85, B_86]: (r1_ordinal1(A_85, B_86) | r2_hidden(B_86, A_85) | B_86=A_85 | ~v3_ordinal1(B_86) | ~v3_ordinal1(A_85))), inference(resolution, [status(thm)], [c_229, c_174])).
% 3.18/1.64  tff(c_319, plain, (![B_86, A_85]: (r1_ordinal1(B_86, A_85) | r1_ordinal1(A_85, B_86) | B_86=A_85 | ~v3_ordinal1(B_86) | ~v3_ordinal1(A_85))), inference(resolution, [status(thm)], [c_304, c_174])).
% 3.18/1.64  tff(c_651, plain, (r1_ordinal1('#skF_4', '#skF_3') | '#skF_3'='#skF_4' | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_319, c_648])).
% 3.18/1.64  tff(c_657, plain, (r1_ordinal1('#skF_4', '#skF_3') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_64, c_651])).
% 3.18/1.64  tff(c_658, plain, (r1_ordinal1('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_58, c_657])).
% 3.18/1.64  tff(c_635, plain, (~v2_wellord1(k1_wellord2('#skF_3')) | ~r2_hidden('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4') | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_629])).
% 3.18/1.64  tff(c_641, plain, (~v2_wellord1(k1_wellord2('#skF_3')) | ~r2_hidden('#skF_4', '#skF_3') | ~r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_64, c_635])).
% 3.18/1.64  tff(c_675, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_641])).
% 3.18/1.64  tff(c_678, plain, (~r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_675])).
% 3.18/1.64  tff(c_682, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_64, c_658, c_678])).
% 3.18/1.64  tff(c_683, plain, (~r2_hidden('#skF_4', '#skF_3') | ~v2_wellord1(k1_wellord2('#skF_3'))), inference(splitRight, [status(thm)], [c_641])).
% 3.18/1.64  tff(c_691, plain, (~v2_wellord1(k1_wellord2('#skF_3'))), inference(splitLeft, [status(thm)], [c_683])).
% 3.18/1.64  tff(c_694, plain, (~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_54, c_691])).
% 3.18/1.64  tff(c_698, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_694])).
% 3.18/1.64  tff(c_699, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_683])).
% 3.18/1.64  tff(c_703, plain, (r1_ordinal1('#skF_3', '#skF_4') | '#skF_3'='#skF_4' | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_262, c_699])).
% 3.18/1.64  tff(c_711, plain, (r1_ordinal1('#skF_3', '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_703])).
% 3.18/1.64  tff(c_713, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_648, c_711])).
% 3.18/1.64  tff(c_715, plain, (r1_tarski('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_638])).
% 3.18/1.64  tff(c_10, plain, (![A_8, B_9]: (r1_ordinal1(A_8, B_9) | ~r1_tarski(A_8, B_9) | ~v3_ordinal1(B_9) | ~v3_ordinal1(A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.18/1.64  tff(c_718, plain, (r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_715, c_10])).
% 3.18/1.64  tff(c_721, plain, (r1_ordinal1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_718])).
% 3.18/1.64  tff(c_186, plain, (![A_75, B_76]: (r2_hidden(A_75, k1_ordinal1(B_76)) | ~r1_ordinal1(A_75, B_76) | ~v3_ordinal1(B_76) | ~v3_ordinal1(A_75))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.18/1.64  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | r2_hidden(A_10, B_11) | ~r2_hidden(A_10, k1_ordinal1(B_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.18/1.64  tff(c_201, plain, (![B_76, A_75]: (B_76=A_75 | r2_hidden(A_75, B_76) | ~r1_ordinal1(A_75, B_76) | ~v3_ordinal1(B_76) | ~v3_ordinal1(A_75))), inference(resolution, [status(thm)], [c_186, c_14])).
% 3.18/1.64  tff(c_714, plain, (~r2_hidden('#skF_3', '#skF_4') | ~v2_wellord1(k1_wellord2('#skF_4'))), inference(splitRight, [status(thm)], [c_638])).
% 3.18/1.64  tff(c_733, plain, (~v2_wellord1(k1_wellord2('#skF_4'))), inference(splitLeft, [status(thm)], [c_714])).
% 3.18/1.64  tff(c_736, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_733])).
% 3.18/1.64  tff(c_740, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_736])).
% 3.18/1.64  tff(c_741, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_714])).
% 3.18/1.64  tff(c_748, plain, ('#skF_3'='#skF_4' | ~r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_201, c_741])).
% 3.18/1.64  tff(c_761, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_721, c_748])).
% 3.18/1.64  tff(c_763, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_761])).
% 3.18/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.64  
% 3.18/1.64  Inference rules
% 3.18/1.64  ----------------------
% 3.18/1.64  #Ref     : 0
% 3.18/1.64  #Sup     : 127
% 3.18/1.64  #Fact    : 4
% 3.18/1.64  #Define  : 0
% 3.18/1.64  #Split   : 4
% 3.18/1.64  #Chain   : 0
% 3.18/1.64  #Close   : 0
% 3.18/1.64  
% 3.18/1.64  Ordering : KBO
% 3.18/1.64  
% 3.18/1.64  Simplification rules
% 3.18/1.64  ----------------------
% 3.18/1.64  #Subsume      : 12
% 3.18/1.64  #Demod        : 110
% 3.18/1.64  #Tautology    : 56
% 3.18/1.64  #SimpNegUnit  : 5
% 3.18/1.64  #BackRed      : 0
% 3.18/1.64  
% 3.18/1.64  #Partial instantiations: 0
% 3.18/1.64  #Strategies tried      : 1
% 3.18/1.64  
% 3.18/1.64  Timing (in seconds)
% 3.18/1.64  ----------------------
% 3.18/1.65  Preprocessing        : 0.42
% 3.18/1.65  Parsing              : 0.22
% 3.18/1.65  CNF conversion       : 0.03
% 3.18/1.65  Main loop            : 0.40
% 3.18/1.65  Inferencing          : 0.14
% 3.18/1.65  Reduction            : 0.12
% 3.18/1.65  Demodulation         : 0.09
% 3.18/1.65  BG Simplification    : 0.03
% 3.18/1.65  Subsumption          : 0.09
% 3.18/1.65  Abstraction          : 0.02
% 3.18/1.65  MUC search           : 0.00
% 3.18/1.65  Cooper               : 0.00
% 3.18/1.65  Total                : 0.86
% 3.18/1.65  Index Insertion      : 0.00
% 3.18/1.65  Index Deletion       : 0.00
% 3.18/1.65  Index Matching       : 0.00
% 3.18/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
