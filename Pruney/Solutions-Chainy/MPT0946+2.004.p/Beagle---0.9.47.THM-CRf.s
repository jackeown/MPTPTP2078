%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:32 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 535 expanded)
%              Number of leaves         :   33 ( 202 expanded)
%              Depth                    :   15
%              Number of atoms          :  261 (1414 expanded)
%              Number of equality atoms :   20 ( 183 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_wellord1 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

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

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_147,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r4_wellord1(k1_wellord2(A),k1_wellord2(B))
             => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).

tff(f_133,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v2_wellord1(k1_wellord2(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_137,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_120,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_118,axiom,(
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

tff(f_129,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
           => A = k1_wellord1(k1_wellord2(B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).

tff(f_103,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
       => ! [B] :
            ~ ( r2_hidden(B,k3_relat_1(A))
              & r4_wellord1(A,k2_wellord1(A,k1_wellord1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
           => r4_wellord1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

tff(f_62,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k3_relat_1(k2_wellord1(C,B)))
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_wellord1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_93,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( ( r4_wellord1(A,B)
                  & r4_wellord1(B,C) )
               => r4_wellord1(A,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_wellord1)).

tff(c_52,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_58,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_48,plain,(
    ! [A_38] :
      ( v2_wellord1(k1_wellord2(A_38))
      | ~ v3_ordinal1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_56,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ r1_ordinal1(A_5,B_6)
      | ~ v3_ordinal1(B_6)
      | ~ v3_ordinal1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_54,plain,(
    r4_wellord1(k1_wellord2('#skF_3'),k1_wellord2('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_50,plain,(
    ! [B_40,A_39] :
      ( k2_wellord1(k1_wellord2(B_40),A_39) = k1_wellord2(A_39)
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_44,plain,(
    ! [A_34] : v1_relat_1(k1_wellord2(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_38,plain,(
    ! [A_26] :
      ( k3_relat_1(k1_wellord2(A_26)) = A_26
      | ~ v1_relat_1(k1_wellord2(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_64,plain,(
    ! [A_26] : k3_relat_1(k1_wellord2(A_26)) = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38])).

tff(c_46,plain,(
    ! [B_37,A_35] :
      ( k1_wellord1(k1_wellord2(B_37),A_35) = A_35
      | ~ r2_hidden(A_35,B_37)
      | ~ v3_ordinal1(B_37)
      | ~ v3_ordinal1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_272,plain,(
    ! [A_81,B_82] :
      ( ~ r4_wellord1(A_81,k2_wellord1(A_81,k1_wellord1(A_81,B_82)))
      | ~ r2_hidden(B_82,k3_relat_1(A_81))
      | ~ v2_wellord1(A_81)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_275,plain,(
    ! [B_37,A_35] :
      ( ~ r4_wellord1(k1_wellord2(B_37),k2_wellord1(k1_wellord2(B_37),A_35))
      | ~ r2_hidden(A_35,k3_relat_1(k1_wellord2(B_37)))
      | ~ v2_wellord1(k1_wellord2(B_37))
      | ~ v1_relat_1(k1_wellord2(B_37))
      | ~ r2_hidden(A_35,B_37)
      | ~ v3_ordinal1(B_37)
      | ~ v3_ordinal1(A_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_272])).

tff(c_501,plain,(
    ! [B_103,A_104] :
      ( ~ r4_wellord1(k1_wellord2(B_103),k2_wellord1(k1_wellord2(B_103),A_104))
      | ~ v2_wellord1(k1_wellord2(B_103))
      | ~ r2_hidden(A_104,B_103)
      | ~ v3_ordinal1(B_103)
      | ~ v3_ordinal1(A_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_64,c_275])).

tff(c_593,plain,(
    ! [B_117,A_118] :
      ( ~ r4_wellord1(k1_wellord2(B_117),k1_wellord2(A_118))
      | ~ v2_wellord1(k1_wellord2(B_117))
      | ~ r2_hidden(A_118,B_117)
      | ~ v3_ordinal1(B_117)
      | ~ v3_ordinal1(A_118)
      | ~ r1_tarski(A_118,B_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_501])).

tff(c_609,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_3'))
    | ~ r2_hidden('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_593])).

tff(c_624,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_3'))
    | ~ r2_hidden('#skF_4','#skF_3')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_609])).

tff(c_625,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_624])).

tff(c_628,plain,
    ( ~ r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_625])).

tff(c_631,plain,(
    ~ r1_ordinal1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_628])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( r1_ordinal1(B_4,A_3)
      | r1_ordinal1(A_3,B_4)
      | ~ v3_ordinal1(B_4)
      | ~ v3_ordinal1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_94,plain,(
    ! [B_50,A_51] :
      ( r4_wellord1(B_50,A_51)
      | ~ r4_wellord1(A_51,B_50)
      | ~ v1_relat_1(B_50)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_96,plain,
    ( r4_wellord1(k1_wellord2('#skF_4'),k1_wellord2('#skF_3'))
    | ~ v1_relat_1(k1_wellord2('#skF_4'))
    | ~ v1_relat_1(k1_wellord2('#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_94])).

tff(c_99,plain,(
    r4_wellord1(k1_wellord2('#skF_4'),k1_wellord2('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_96])).

tff(c_606,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_99,c_593])).

tff(c_621,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_606])).

tff(c_686,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_621])).

tff(c_689,plain,
    ( ~ r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_686])).

tff(c_692,plain,(
    ~ r1_ordinal1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_689])).

tff(c_709,plain,
    ( r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_692])).

tff(c_715,plain,(
    r1_ordinal1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_709])).

tff(c_717,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_631,c_715])).

tff(c_719,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_621])).

tff(c_14,plain,(
    ! [B_9,A_7] :
      ( r2_hidden(B_9,A_7)
      | B_9 = A_7
      | r2_hidden(A_7,B_9)
      | ~ v3_ordinal1(B_9)
      | ~ v3_ordinal1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_718,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | ~ v2_wellord1(k1_wellord2('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_621])).

tff(c_753,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_718])).

tff(c_756,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_753])).

tff(c_760,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_756])).

tff(c_761,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_718])).

tff(c_771,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_761])).

tff(c_784,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58,c_771])).

tff(c_785,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_784])).

tff(c_167,plain,(
    ! [A_64,C_65,B_66] :
      ( r2_hidden(A_64,k3_relat_1(C_65))
      | ~ r2_hidden(A_64,k3_relat_1(k2_wellord1(C_65,B_66)))
      | ~ v1_relat_1(C_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_178,plain,(
    ! [A_64,B_40,A_39] :
      ( r2_hidden(A_64,k3_relat_1(k1_wellord2(B_40)))
      | ~ r2_hidden(A_64,k3_relat_1(k1_wellord2(A_39)))
      | ~ v1_relat_1(k1_wellord2(B_40))
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_167])).

tff(c_182,plain,(
    ! [A_64,B_40,A_39] :
      ( r2_hidden(A_64,B_40)
      | ~ r2_hidden(A_64,A_39)
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_64,c_64,c_178])).

tff(c_794,plain,(
    ! [B_123] :
      ( r2_hidden('#skF_4',B_123)
      | ~ r1_tarski('#skF_3',B_123) ) ),
    inference(resolution,[status(thm)],[c_785,c_182])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_284,plain,(
    ! [A_83,C_84,B_85] :
      ( r4_wellord1(A_83,C_84)
      | ~ r4_wellord1(B_85,C_84)
      | ~ r4_wellord1(A_83,B_85)
      | ~ v1_relat_1(C_84)
      | ~ v1_relat_1(B_85)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_288,plain,(
    ! [A_83] :
      ( r4_wellord1(A_83,k1_wellord2('#skF_4'))
      | ~ r4_wellord1(A_83,k1_wellord2('#skF_3'))
      | ~ v1_relat_1(k1_wellord2('#skF_4'))
      | ~ v1_relat_1(k1_wellord2('#skF_3'))
      | ~ v1_relat_1(A_83) ) ),
    inference(resolution,[status(thm)],[c_54,c_284])).

tff(c_295,plain,(
    ! [A_86] :
      ( r4_wellord1(A_86,k1_wellord2('#skF_4'))
      | ~ r4_wellord1(A_86,k1_wellord2('#skF_3'))
      | ~ v1_relat_1(A_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_288])).

tff(c_298,plain,
    ( r4_wellord1(k1_wellord2('#skF_4'),k1_wellord2('#skF_4'))
    | ~ v1_relat_1(k1_wellord2('#skF_4')) ),
    inference(resolution,[status(thm)],[c_99,c_295])).

tff(c_301,plain,(
    r4_wellord1(k1_wellord2('#skF_4'),k1_wellord2('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_298])).

tff(c_603,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_4','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_301,c_593])).

tff(c_618,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_56,c_603])).

tff(c_635,plain,(
    ~ r2_hidden('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_618])).

tff(c_797,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_794,c_635])).

tff(c_811,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_797])).

tff(c_812,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_618])).

tff(c_816,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_812])).

tff(c_820,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_816])).

tff(c_821,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | ~ v2_wellord1(k1_wellord2('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_624])).

tff(c_897,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_821])).

tff(c_900,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_897])).

tff(c_904,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_900])).

tff(c_905,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_821])).

tff(c_822,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_624])).

tff(c_183,plain,(
    ! [A_67,B_68,A_69] :
      ( r2_hidden(A_67,B_68)
      | ~ r2_hidden(A_67,A_69)
      | ~ r1_tarski(A_69,B_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_64,c_64,c_178])).

tff(c_189,plain,(
    ! [A_7,B_68,B_9] :
      ( r2_hidden(A_7,B_68)
      | ~ r1_tarski(B_9,B_68)
      | r2_hidden(B_9,A_7)
      | B_9 = A_7
      | ~ v3_ordinal1(B_9)
      | ~ v3_ordinal1(A_7) ) ),
    inference(resolution,[status(thm)],[c_14,c_183])).

tff(c_824,plain,(
    ! [A_7] :
      ( r2_hidden(A_7,'#skF_3')
      | r2_hidden('#skF_4',A_7)
      | A_7 = '#skF_4'
      | ~ v3_ordinal1('#skF_4')
      | ~ v3_ordinal1(A_7) ) ),
    inference(resolution,[status(thm)],[c_822,c_189])).

tff(c_949,plain,(
    ! [A_127] :
      ( r2_hidden(A_127,'#skF_3')
      | r2_hidden('#skF_4',A_127)
      | A_127 = '#skF_4'
      | ~ v3_ordinal1(A_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_824])).

tff(c_906,plain,(
    v2_wellord1(k1_wellord2('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_821])).

tff(c_286,plain,(
    ! [A_83] :
      ( r4_wellord1(A_83,k1_wellord2('#skF_3'))
      | ~ r4_wellord1(A_83,k1_wellord2('#skF_4'))
      | ~ v1_relat_1(k1_wellord2('#skF_3'))
      | ~ v1_relat_1(k1_wellord2('#skF_4'))
      | ~ v1_relat_1(A_83) ) ),
    inference(resolution,[status(thm)],[c_99,c_284])).

tff(c_312,plain,(
    ! [A_87] :
      ( r4_wellord1(A_87,k1_wellord2('#skF_3'))
      | ~ r4_wellord1(A_87,k1_wellord2('#skF_4'))
      | ~ v1_relat_1(A_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_286])).

tff(c_20,plain,(
    ! [B_15,A_13] :
      ( r4_wellord1(B_15,A_13)
      | ~ r4_wellord1(A_13,B_15)
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_319,plain,(
    ! [A_87] :
      ( r4_wellord1(k1_wellord2('#skF_3'),A_87)
      | ~ v1_relat_1(k1_wellord2('#skF_3'))
      | ~ r4_wellord1(A_87,k1_wellord2('#skF_4'))
      | ~ v1_relat_1(A_87) ) ),
    inference(resolution,[status(thm)],[c_312,c_20])).

tff(c_327,plain,(
    ! [A_88] :
      ( r4_wellord1(k1_wellord2('#skF_3'),A_88)
      | ~ r4_wellord1(A_88,k1_wellord2('#skF_4'))
      | ~ v1_relat_1(A_88) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_319])).

tff(c_331,plain,
    ( r4_wellord1(k1_wellord2('#skF_3'),k1_wellord2('#skF_3'))
    | ~ v1_relat_1(k1_wellord2('#skF_3')) ),
    inference(resolution,[status(thm)],[c_54,c_327])).

tff(c_337,plain,(
    r4_wellord1(k1_wellord2('#skF_3'),k1_wellord2('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_331])).

tff(c_596,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_3'))
    | ~ r2_hidden('#skF_3','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_337,c_593])).

tff(c_612,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_3'))
    | ~ r2_hidden('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_58,c_596])).

tff(c_933,plain,(
    ~ r2_hidden('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_906,c_612])).

tff(c_952,plain,
    ( r2_hidden('#skF_4','#skF_3')
    | '#skF_3' = '#skF_4'
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_949,c_933])).

tff(c_972,plain,
    ( r2_hidden('#skF_4','#skF_3')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_952])).

tff(c_974,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_905,c_972])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:21:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.58  
% 3.20/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.58  %$ r4_wellord1 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.20/1.58  
% 3.20/1.58  %Foreground sorts:
% 3.20/1.58  
% 3.20/1.58  
% 3.20/1.58  %Background operators:
% 3.20/1.58  
% 3.20/1.58  
% 3.20/1.58  %Foreground operators:
% 3.20/1.58  tff(r4_wellord1, type, r4_wellord1: ($i * $i) > $o).
% 3.20/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.20/1.58  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.20/1.58  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.20/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.20/1.58  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 3.20/1.58  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 3.20/1.58  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 3.20/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.20/1.58  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 3.20/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.20/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.20/1.58  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 3.20/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.58  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.20/1.58  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 3.20/1.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.20/1.58  
% 3.20/1.61  tff(f_147, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r4_wellord1(k1_wellord2(A), k1_wellord2(B)) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_wellord2)).
% 3.20/1.61  tff(f_133, axiom, (![A]: (v3_ordinal1(A) => v2_wellord1(k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_wellord2)).
% 3.20/1.61  tff(f_47, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 3.20/1.61  tff(f_137, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_wellord2)).
% 3.20/1.61  tff(f_120, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 3.20/1.61  tff(f_118, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 3.20/1.61  tff(f_129, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) => (A = k1_wellord1(k1_wellord2(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_wellord2)).
% 3.20/1.61  tff(f_103, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) => (![B]: ~(r2_hidden(B, k3_relat_1(A)) & r4_wellord1(A, k2_wellord1(A, k1_wellord1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_wellord1)).
% 3.20/1.61  tff(f_39, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 3.20/1.61  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r4_wellord1(A, B) => r4_wellord1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_wellord1)).
% 3.20/1.61  tff(f_62, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 3.20/1.61  tff(f_70, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k3_relat_1(k2_wellord1(C, B))) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_wellord1)).
% 3.20/1.61  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.20/1.61  tff(f_93, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((r4_wellord1(A, B) & r4_wellord1(B, C)) => r4_wellord1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_wellord1)).
% 3.20/1.61  tff(c_52, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.20/1.61  tff(c_58, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.20/1.61  tff(c_48, plain, (![A_38]: (v2_wellord1(k1_wellord2(A_38)) | ~v3_ordinal1(A_38))), inference(cnfTransformation, [status(thm)], [f_133])).
% 3.20/1.61  tff(c_56, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.20/1.61  tff(c_12, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~r1_ordinal1(A_5, B_6) | ~v3_ordinal1(B_6) | ~v3_ordinal1(A_5))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.20/1.61  tff(c_54, plain, (r4_wellord1(k1_wellord2('#skF_3'), k1_wellord2('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.20/1.61  tff(c_50, plain, (![B_40, A_39]: (k2_wellord1(k1_wellord2(B_40), A_39)=k1_wellord2(A_39) | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.20/1.61  tff(c_44, plain, (![A_34]: (v1_relat_1(k1_wellord2(A_34)))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.20/1.61  tff(c_38, plain, (![A_26]: (k3_relat_1(k1_wellord2(A_26))=A_26 | ~v1_relat_1(k1_wellord2(A_26)))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.20/1.61  tff(c_64, plain, (![A_26]: (k3_relat_1(k1_wellord2(A_26))=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38])).
% 3.20/1.61  tff(c_46, plain, (![B_37, A_35]: (k1_wellord1(k1_wellord2(B_37), A_35)=A_35 | ~r2_hidden(A_35, B_37) | ~v3_ordinal1(B_37) | ~v3_ordinal1(A_35))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.20/1.61  tff(c_272, plain, (![A_81, B_82]: (~r4_wellord1(A_81, k2_wellord1(A_81, k1_wellord1(A_81, B_82))) | ~r2_hidden(B_82, k3_relat_1(A_81)) | ~v2_wellord1(A_81) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.20/1.61  tff(c_275, plain, (![B_37, A_35]: (~r4_wellord1(k1_wellord2(B_37), k2_wellord1(k1_wellord2(B_37), A_35)) | ~r2_hidden(A_35, k3_relat_1(k1_wellord2(B_37))) | ~v2_wellord1(k1_wellord2(B_37)) | ~v1_relat_1(k1_wellord2(B_37)) | ~r2_hidden(A_35, B_37) | ~v3_ordinal1(B_37) | ~v3_ordinal1(A_35))), inference(superposition, [status(thm), theory('equality')], [c_46, c_272])).
% 3.20/1.61  tff(c_501, plain, (![B_103, A_104]: (~r4_wellord1(k1_wellord2(B_103), k2_wellord1(k1_wellord2(B_103), A_104)) | ~v2_wellord1(k1_wellord2(B_103)) | ~r2_hidden(A_104, B_103) | ~v3_ordinal1(B_103) | ~v3_ordinal1(A_104))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_64, c_275])).
% 3.20/1.61  tff(c_593, plain, (![B_117, A_118]: (~r4_wellord1(k1_wellord2(B_117), k1_wellord2(A_118)) | ~v2_wellord1(k1_wellord2(B_117)) | ~r2_hidden(A_118, B_117) | ~v3_ordinal1(B_117) | ~v3_ordinal1(A_118) | ~r1_tarski(A_118, B_117))), inference(superposition, [status(thm), theory('equality')], [c_50, c_501])).
% 3.20/1.61  tff(c_609, plain, (~v2_wellord1(k1_wellord2('#skF_3')) | ~r2_hidden('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4') | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_593])).
% 3.20/1.61  tff(c_624, plain, (~v2_wellord1(k1_wellord2('#skF_3')) | ~r2_hidden('#skF_4', '#skF_3') | ~r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_609])).
% 3.20/1.61  tff(c_625, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_624])).
% 3.20/1.61  tff(c_628, plain, (~r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_625])).
% 3.20/1.61  tff(c_631, plain, (~r1_ordinal1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_628])).
% 3.20/1.61  tff(c_8, plain, (![B_4, A_3]: (r1_ordinal1(B_4, A_3) | r1_ordinal1(A_3, B_4) | ~v3_ordinal1(B_4) | ~v3_ordinal1(A_3))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.20/1.61  tff(c_94, plain, (![B_50, A_51]: (r4_wellord1(B_50, A_51) | ~r4_wellord1(A_51, B_50) | ~v1_relat_1(B_50) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.20/1.61  tff(c_96, plain, (r4_wellord1(k1_wellord2('#skF_4'), k1_wellord2('#skF_3')) | ~v1_relat_1(k1_wellord2('#skF_4')) | ~v1_relat_1(k1_wellord2('#skF_3'))), inference(resolution, [status(thm)], [c_54, c_94])).
% 3.20/1.61  tff(c_99, plain, (r4_wellord1(k1_wellord2('#skF_4'), k1_wellord2('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_96])).
% 3.20/1.61  tff(c_606, plain, (~v2_wellord1(k1_wellord2('#skF_4')) | ~r2_hidden('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3') | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_99, c_593])).
% 3.20/1.61  tff(c_621, plain, (~v2_wellord1(k1_wellord2('#skF_4')) | ~r2_hidden('#skF_3', '#skF_4') | ~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_606])).
% 3.20/1.61  tff(c_686, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_621])).
% 3.20/1.61  tff(c_689, plain, (~r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_686])).
% 3.20/1.61  tff(c_692, plain, (~r1_ordinal1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_689])).
% 3.20/1.61  tff(c_709, plain, (r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_8, c_692])).
% 3.20/1.61  tff(c_715, plain, (r1_ordinal1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_709])).
% 3.20/1.61  tff(c_717, plain, $false, inference(negUnitSimplification, [status(thm)], [c_631, c_715])).
% 3.20/1.61  tff(c_719, plain, (r1_tarski('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_621])).
% 3.20/1.61  tff(c_14, plain, (![B_9, A_7]: (r2_hidden(B_9, A_7) | B_9=A_7 | r2_hidden(A_7, B_9) | ~v3_ordinal1(B_9) | ~v3_ordinal1(A_7))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.20/1.61  tff(c_718, plain, (~r2_hidden('#skF_3', '#skF_4') | ~v2_wellord1(k1_wellord2('#skF_4'))), inference(splitRight, [status(thm)], [c_621])).
% 3.20/1.61  tff(c_753, plain, (~v2_wellord1(k1_wellord2('#skF_4'))), inference(splitLeft, [status(thm)], [c_718])).
% 3.20/1.61  tff(c_756, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_753])).
% 3.20/1.61  tff(c_760, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_756])).
% 3.20/1.61  tff(c_761, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_718])).
% 3.20/1.61  tff(c_771, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_761])).
% 3.20/1.61  tff(c_784, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58, c_771])).
% 3.20/1.61  tff(c_785, plain, (r2_hidden('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_52, c_784])).
% 3.20/1.61  tff(c_167, plain, (![A_64, C_65, B_66]: (r2_hidden(A_64, k3_relat_1(C_65)) | ~r2_hidden(A_64, k3_relat_1(k2_wellord1(C_65, B_66))) | ~v1_relat_1(C_65))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.20/1.61  tff(c_178, plain, (![A_64, B_40, A_39]: (r2_hidden(A_64, k3_relat_1(k1_wellord2(B_40))) | ~r2_hidden(A_64, k3_relat_1(k1_wellord2(A_39))) | ~v1_relat_1(k1_wellord2(B_40)) | ~r1_tarski(A_39, B_40))), inference(superposition, [status(thm), theory('equality')], [c_50, c_167])).
% 3.20/1.61  tff(c_182, plain, (![A_64, B_40, A_39]: (r2_hidden(A_64, B_40) | ~r2_hidden(A_64, A_39) | ~r1_tarski(A_39, B_40))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_64, c_64, c_178])).
% 3.20/1.61  tff(c_794, plain, (![B_123]: (r2_hidden('#skF_4', B_123) | ~r1_tarski('#skF_3', B_123))), inference(resolution, [status(thm)], [c_785, c_182])).
% 3.20/1.61  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.61  tff(c_284, plain, (![A_83, C_84, B_85]: (r4_wellord1(A_83, C_84) | ~r4_wellord1(B_85, C_84) | ~r4_wellord1(A_83, B_85) | ~v1_relat_1(C_84) | ~v1_relat_1(B_85) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.20/1.61  tff(c_288, plain, (![A_83]: (r4_wellord1(A_83, k1_wellord2('#skF_4')) | ~r4_wellord1(A_83, k1_wellord2('#skF_3')) | ~v1_relat_1(k1_wellord2('#skF_4')) | ~v1_relat_1(k1_wellord2('#skF_3')) | ~v1_relat_1(A_83))), inference(resolution, [status(thm)], [c_54, c_284])).
% 3.20/1.61  tff(c_295, plain, (![A_86]: (r4_wellord1(A_86, k1_wellord2('#skF_4')) | ~r4_wellord1(A_86, k1_wellord2('#skF_3')) | ~v1_relat_1(A_86))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_288])).
% 3.20/1.61  tff(c_298, plain, (r4_wellord1(k1_wellord2('#skF_4'), k1_wellord2('#skF_4')) | ~v1_relat_1(k1_wellord2('#skF_4'))), inference(resolution, [status(thm)], [c_99, c_295])).
% 3.20/1.61  tff(c_301, plain, (r4_wellord1(k1_wellord2('#skF_4'), k1_wellord2('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_298])).
% 3.20/1.61  tff(c_603, plain, (~v2_wellord1(k1_wellord2('#skF_4')) | ~r2_hidden('#skF_4', '#skF_4') | ~v3_ordinal1('#skF_4') | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_301, c_593])).
% 3.20/1.61  tff(c_618, plain, (~v2_wellord1(k1_wellord2('#skF_4')) | ~r2_hidden('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_56, c_603])).
% 3.20/1.61  tff(c_635, plain, (~r2_hidden('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_618])).
% 3.20/1.61  tff(c_797, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_794, c_635])).
% 3.20/1.61  tff(c_811, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_719, c_797])).
% 3.20/1.61  tff(c_812, plain, (~v2_wellord1(k1_wellord2('#skF_4'))), inference(splitRight, [status(thm)], [c_618])).
% 3.20/1.61  tff(c_816, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_812])).
% 3.20/1.61  tff(c_820, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_816])).
% 3.20/1.61  tff(c_821, plain, (~r2_hidden('#skF_4', '#skF_3') | ~v2_wellord1(k1_wellord2('#skF_3'))), inference(splitRight, [status(thm)], [c_624])).
% 3.20/1.61  tff(c_897, plain, (~v2_wellord1(k1_wellord2('#skF_3'))), inference(splitLeft, [status(thm)], [c_821])).
% 3.20/1.61  tff(c_900, plain, (~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_48, c_897])).
% 3.20/1.61  tff(c_904, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_900])).
% 3.20/1.61  tff(c_905, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_821])).
% 3.20/1.61  tff(c_822, plain, (r1_tarski('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_624])).
% 3.20/1.61  tff(c_183, plain, (![A_67, B_68, A_69]: (r2_hidden(A_67, B_68) | ~r2_hidden(A_67, A_69) | ~r1_tarski(A_69, B_68))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_64, c_64, c_178])).
% 3.20/1.61  tff(c_189, plain, (![A_7, B_68, B_9]: (r2_hidden(A_7, B_68) | ~r1_tarski(B_9, B_68) | r2_hidden(B_9, A_7) | B_9=A_7 | ~v3_ordinal1(B_9) | ~v3_ordinal1(A_7))), inference(resolution, [status(thm)], [c_14, c_183])).
% 3.20/1.61  tff(c_824, plain, (![A_7]: (r2_hidden(A_7, '#skF_3') | r2_hidden('#skF_4', A_7) | A_7='#skF_4' | ~v3_ordinal1('#skF_4') | ~v3_ordinal1(A_7))), inference(resolution, [status(thm)], [c_822, c_189])).
% 3.20/1.61  tff(c_949, plain, (![A_127]: (r2_hidden(A_127, '#skF_3') | r2_hidden('#skF_4', A_127) | A_127='#skF_4' | ~v3_ordinal1(A_127))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_824])).
% 3.20/1.61  tff(c_906, plain, (v2_wellord1(k1_wellord2('#skF_3'))), inference(splitRight, [status(thm)], [c_821])).
% 3.20/1.61  tff(c_286, plain, (![A_83]: (r4_wellord1(A_83, k1_wellord2('#skF_3')) | ~r4_wellord1(A_83, k1_wellord2('#skF_4')) | ~v1_relat_1(k1_wellord2('#skF_3')) | ~v1_relat_1(k1_wellord2('#skF_4')) | ~v1_relat_1(A_83))), inference(resolution, [status(thm)], [c_99, c_284])).
% 3.20/1.61  tff(c_312, plain, (![A_87]: (r4_wellord1(A_87, k1_wellord2('#skF_3')) | ~r4_wellord1(A_87, k1_wellord2('#skF_4')) | ~v1_relat_1(A_87))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_286])).
% 3.20/1.61  tff(c_20, plain, (![B_15, A_13]: (r4_wellord1(B_15, A_13) | ~r4_wellord1(A_13, B_15) | ~v1_relat_1(B_15) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.20/1.61  tff(c_319, plain, (![A_87]: (r4_wellord1(k1_wellord2('#skF_3'), A_87) | ~v1_relat_1(k1_wellord2('#skF_3')) | ~r4_wellord1(A_87, k1_wellord2('#skF_4')) | ~v1_relat_1(A_87))), inference(resolution, [status(thm)], [c_312, c_20])).
% 3.20/1.61  tff(c_327, plain, (![A_88]: (r4_wellord1(k1_wellord2('#skF_3'), A_88) | ~r4_wellord1(A_88, k1_wellord2('#skF_4')) | ~v1_relat_1(A_88))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_319])).
% 3.20/1.61  tff(c_331, plain, (r4_wellord1(k1_wellord2('#skF_3'), k1_wellord2('#skF_3')) | ~v1_relat_1(k1_wellord2('#skF_3'))), inference(resolution, [status(thm)], [c_54, c_327])).
% 3.20/1.61  tff(c_337, plain, (r4_wellord1(k1_wellord2('#skF_3'), k1_wellord2('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_331])).
% 3.20/1.61  tff(c_596, plain, (~v2_wellord1(k1_wellord2('#skF_3')) | ~r2_hidden('#skF_3', '#skF_3') | ~v3_ordinal1('#skF_3') | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_337, c_593])).
% 3.20/1.61  tff(c_612, plain, (~v2_wellord1(k1_wellord2('#skF_3')) | ~r2_hidden('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_58, c_596])).
% 3.20/1.61  tff(c_933, plain, (~r2_hidden('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_906, c_612])).
% 3.20/1.61  tff(c_952, plain, (r2_hidden('#skF_4', '#skF_3') | '#skF_3'='#skF_4' | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_949, c_933])).
% 3.20/1.61  tff(c_972, plain, (r2_hidden('#skF_4', '#skF_3') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_952])).
% 3.20/1.61  tff(c_974, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_905, c_972])).
% 3.20/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.61  
% 3.20/1.61  Inference rules
% 3.20/1.61  ----------------------
% 3.20/1.61  #Ref     : 0
% 3.20/1.61  #Sup     : 160
% 3.20/1.61  #Fact    : 6
% 3.20/1.61  #Define  : 0
% 3.20/1.61  #Split   : 7
% 3.20/1.61  #Chain   : 0
% 3.20/1.61  #Close   : 0
% 3.20/1.61  
% 3.20/1.61  Ordering : KBO
% 3.20/1.61  
% 3.20/1.61  Simplification rules
% 3.20/1.61  ----------------------
% 3.20/1.61  #Subsume      : 21
% 3.20/1.61  #Demod        : 177
% 3.20/1.61  #Tautology    : 51
% 3.20/1.61  #SimpNegUnit  : 11
% 3.20/1.61  #BackRed      : 0
% 3.20/1.61  
% 3.20/1.61  #Partial instantiations: 0
% 3.20/1.61  #Strategies tried      : 1
% 3.20/1.61  
% 3.20/1.61  Timing (in seconds)
% 3.20/1.61  ----------------------
% 3.20/1.61  Preprocessing        : 0.36
% 3.20/1.61  Parsing              : 0.19
% 3.20/1.61  CNF conversion       : 0.03
% 3.20/1.61  Main loop            : 0.40
% 3.20/1.61  Inferencing          : 0.14
% 3.20/1.61  Reduction            : 0.12
% 3.20/1.61  Demodulation         : 0.08
% 3.20/1.61  BG Simplification    : 0.03
% 3.20/1.61  Subsumption          : 0.09
% 3.20/1.61  Abstraction          : 0.02
% 3.20/1.61  MUC search           : 0.00
% 3.20/1.61  Cooper               : 0.00
% 3.20/1.61  Total                : 0.80
% 3.20/1.61  Index Insertion      : 0.00
% 3.20/1.61  Index Deletion       : 0.00
% 3.20/1.61  Index Matching       : 0.00
% 3.20/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
