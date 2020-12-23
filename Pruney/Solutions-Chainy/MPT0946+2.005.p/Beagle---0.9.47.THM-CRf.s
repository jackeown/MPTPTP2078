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
% DateTime   : Thu Dec  3 10:10:32 EST 2020

% Result     : Theorem 8.53s
% Output     : CNFRefutation 8.53s
% Verified   : 
% Statistics : Number of formulae       :  140 (1635 expanded)
%              Number of leaves         :   33 ( 585 expanded)
%              Depth                    :   22
%              Number of atoms          :  313 (4156 expanded)
%              Number of equality atoms :   47 ( 826 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_143,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r4_wellord1(k1_wellord2(A),k1_wellord2(B))
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).

tff(f_62,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_129,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v2_wellord1(k1_wellord2(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_116,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
           => r4_wellord1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

tff(f_133,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_114,axiom,(
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

tff(f_125,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
           => A = k1_wellord1(k1_wellord2(B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).

tff(f_99,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
       => ! [B] :
            ~ ( r2_hidden(B,k3_relat_1(A))
              & r4_wellord1(A,k2_wellord1(A,k1_wellord1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( ( r4_wellord1(A,B)
                  & r4_wellord1(B,C) )
               => r4_wellord1(A,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_wellord1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(k2_wellord1(C,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_wellord1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_50,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_56,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_14,plain,(
    ! [B_9,A_7] :
      ( r2_hidden(B_9,A_7)
      | B_9 = A_7
      | r2_hidden(A_7,B_9)
      | ~ v3_ordinal1(B_9)
      | ~ v3_ordinal1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_46,plain,(
    ! [A_38] :
      ( v2_wellord1(k1_wellord2(A_38))
      | ~ v3_ordinal1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( r1_ordinal1(B_4,A_3)
      | r1_ordinal1(A_3,B_4)
      | ~ v3_ordinal1(B_4)
      | ~ v3_ordinal1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ r1_ordinal1(A_5,B_6)
      | ~ v3_ordinal1(B_6)
      | ~ v3_ordinal1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_42,plain,(
    ! [A_34] : v1_relat_1(k1_wellord2(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_52,plain,(
    r4_wellord1(k1_wellord2('#skF_3'),k1_wellord2('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_121,plain,(
    ! [B_57,A_58] :
      ( r4_wellord1(B_57,A_58)
      | ~ r4_wellord1(A_58,B_57)
      | ~ v1_relat_1(B_57)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_123,plain,
    ( r4_wellord1(k1_wellord2('#skF_4'),k1_wellord2('#skF_3'))
    | ~ v1_relat_1(k1_wellord2('#skF_4'))
    | ~ v1_relat_1(k1_wellord2('#skF_3')) ),
    inference(resolution,[status(thm)],[c_52,c_121])).

tff(c_126,plain,(
    r4_wellord1(k1_wellord2('#skF_4'),k1_wellord2('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_123])).

tff(c_48,plain,(
    ! [B_40,A_39] :
      ( k2_wellord1(k1_wellord2(B_40),A_39) = k1_wellord2(A_39)
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_36,plain,(
    ! [A_26] :
      ( k3_relat_1(k1_wellord2(A_26)) = A_26
      | ~ v1_relat_1(k1_wellord2(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_62,plain,(
    ! [A_26] : k3_relat_1(k1_wellord2(A_26)) = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_36])).

tff(c_44,plain,(
    ! [B_37,A_35] :
      ( k1_wellord1(k1_wellord2(B_37),A_35) = A_35
      | ~ r2_hidden(A_35,B_37)
      | ~ v3_ordinal1(B_37)
      | ~ v3_ordinal1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_426,plain,(
    ! [A_87,B_88] :
      ( ~ r4_wellord1(A_87,k2_wellord1(A_87,k1_wellord1(A_87,B_88)))
      | ~ r2_hidden(B_88,k3_relat_1(A_87))
      | ~ v2_wellord1(A_87)
      | ~ v1_relat_1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_437,plain,(
    ! [B_37,A_35] :
      ( ~ r4_wellord1(k1_wellord2(B_37),k2_wellord1(k1_wellord2(B_37),A_35))
      | ~ r2_hidden(A_35,k3_relat_1(k1_wellord2(B_37)))
      | ~ v2_wellord1(k1_wellord2(B_37))
      | ~ v1_relat_1(k1_wellord2(B_37))
      | ~ r2_hidden(A_35,B_37)
      | ~ v3_ordinal1(B_37)
      | ~ v3_ordinal1(A_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_426])).

tff(c_896,plain,(
    ! [B_119,A_120] :
      ( ~ r4_wellord1(k1_wellord2(B_119),k2_wellord1(k1_wellord2(B_119),A_120))
      | ~ v2_wellord1(k1_wellord2(B_119))
      | ~ r2_hidden(A_120,B_119)
      | ~ v3_ordinal1(B_119)
      | ~ v3_ordinal1(A_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_62,c_437])).

tff(c_3775,plain,(
    ! [B_177,A_178] :
      ( ~ r4_wellord1(k1_wellord2(B_177),k1_wellord2(A_178))
      | ~ v2_wellord1(k1_wellord2(B_177))
      | ~ r2_hidden(A_178,B_177)
      | ~ v3_ordinal1(B_177)
      | ~ v3_ordinal1(A_178)
      | ~ r1_tarski(A_178,B_177) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_896])).

tff(c_3788,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_126,c_3775])).

tff(c_3803,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_3788])).

tff(c_3813,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3803])).

tff(c_3816,plain,
    ( ~ r1_ordinal1('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_3813])).

tff(c_3819,plain,(
    ~ r1_ordinal1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_3816])).

tff(c_3822,plain,
    ( r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_3819])).

tff(c_3828,plain,(
    r1_ordinal1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_3822])).

tff(c_3791,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_3'))
    | ~ r2_hidden('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_3775])).

tff(c_3806,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_3'))
    | ~ r2_hidden('#skF_4','#skF_3')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_3791])).

tff(c_3843,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3806])).

tff(c_3846,plain,
    ( ~ r1_ordinal1('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_3843])).

tff(c_3850,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_3828,c_3846])).

tff(c_3851,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | ~ v2_wellord1(k1_wellord2('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3806])).

tff(c_3892,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3851])).

tff(c_3895,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_3892])).

tff(c_3899,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3895])).

tff(c_3900,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_3851])).

tff(c_356,plain,(
    ! [A_81,C_82,B_83] :
      ( r4_wellord1(A_81,C_82)
      | ~ r4_wellord1(B_83,C_82)
      | ~ r4_wellord1(A_81,B_83)
      | ~ v1_relat_1(C_82)
      | ~ v1_relat_1(B_83)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_360,plain,(
    ! [A_81] :
      ( r4_wellord1(A_81,k1_wellord2('#skF_4'))
      | ~ r4_wellord1(A_81,k1_wellord2('#skF_3'))
      | ~ v1_relat_1(k1_wellord2('#skF_4'))
      | ~ v1_relat_1(k1_wellord2('#skF_3'))
      | ~ v1_relat_1(A_81) ) ),
    inference(resolution,[status(thm)],[c_52,c_356])).

tff(c_367,plain,(
    ! [A_84] :
      ( r4_wellord1(A_84,k1_wellord2('#skF_4'))
      | ~ r4_wellord1(A_84,k1_wellord2('#skF_3'))
      | ~ v1_relat_1(A_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_360])).

tff(c_370,plain,
    ( r4_wellord1(k1_wellord2('#skF_4'),k1_wellord2('#skF_4'))
    | ~ v1_relat_1(k1_wellord2('#skF_4')) ),
    inference(resolution,[status(thm)],[c_126,c_367])).

tff(c_373,plain,(
    r4_wellord1(k1_wellord2('#skF_4'),k1_wellord2('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_370])).

tff(c_3852,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_3806])).

tff(c_127,plain,(
    ! [C_59,B_60,A_61] :
      ( k2_wellord1(k2_wellord1(C_59,B_60),A_61) = k2_wellord1(k2_wellord1(C_59,A_61),B_60)
      | ~ v1_relat_1(C_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_181,plain,(
    ! [B_40,B_60,A_39] :
      ( k2_wellord1(k2_wellord1(k1_wellord2(B_40),B_60),A_39) = k2_wellord1(k1_wellord2(A_39),B_60)
      | ~ v1_relat_1(k1_wellord2(B_40))
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_127])).

tff(c_268,plain,(
    ! [B_72,B_73,A_74] :
      ( k2_wellord1(k2_wellord1(k1_wellord2(B_72),B_73),A_74) = k2_wellord1(k1_wellord2(A_74),B_73)
      | ~ r1_tarski(A_74,B_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_181])).

tff(c_446,plain,(
    ! [A_90,A_89,B_91] :
      ( k2_wellord1(k1_wellord2(A_90),A_89) = k2_wellord1(k1_wellord2(A_89),A_90)
      | ~ r1_tarski(A_89,B_91)
      | ~ r1_tarski(A_90,B_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_268])).

tff(c_453,plain,(
    ! [B_92,A_93] :
      ( k2_wellord1(k1_wellord2(B_92),A_93) = k2_wellord1(k1_wellord2(A_93),B_92)
      | ~ r1_tarski(A_93,B_92) ) ),
    inference(resolution,[status(thm)],[c_6,c_446])).

tff(c_605,plain,(
    ! [A_98,B_99] :
      ( k2_wellord1(k1_wellord2(A_98),B_99) = k1_wellord2(A_98)
      | ~ r1_tarski(A_98,B_99)
      | ~ r1_tarski(A_98,B_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_453])).

tff(c_16,plain,(
    ! [C_12,B_11,A_10] :
      ( k2_wellord1(k2_wellord1(C_12,B_11),A_10) = k2_wellord1(k2_wellord1(C_12,A_10),B_11)
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_633,plain,(
    ! [A_98,B_11,B_99] :
      ( k2_wellord1(k2_wellord1(k1_wellord2(A_98),B_11),B_99) = k2_wellord1(k1_wellord2(A_98),B_11)
      | ~ v1_relat_1(k1_wellord2(A_98))
      | ~ r1_tarski(A_98,B_99)
      | ~ r1_tarski(A_98,B_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_605,c_16])).

tff(c_713,plain,(
    ! [A_106,B_107,B_108] :
      ( k2_wellord1(k2_wellord1(k1_wellord2(A_106),B_107),B_108) = k2_wellord1(k1_wellord2(A_106),B_107)
      | ~ r1_tarski(A_106,B_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_633])).

tff(c_770,plain,(
    ! [B_40,A_39,B_108] :
      ( k2_wellord1(k1_wellord2(B_40),A_39) = k2_wellord1(k1_wellord2(A_39),B_108)
      | ~ r1_tarski(B_40,B_108)
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_713])).

tff(c_4188,plain,(
    ! [A_183] :
      ( k2_wellord1(k1_wellord2(A_183),'#skF_3') = k2_wellord1(k1_wellord2('#skF_4'),A_183)
      | ~ r1_tarski(A_183,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3852,c_770])).

tff(c_452,plain,(
    ! [B_2,A_90] :
      ( k2_wellord1(k1_wellord2(B_2),A_90) = k2_wellord1(k1_wellord2(A_90),B_2)
      | ~ r1_tarski(A_90,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_446])).

tff(c_6826,plain,(
    ! [A_207] :
      ( k2_wellord1(k1_wellord2('#skF_3'),A_207) = k2_wellord1(k1_wellord2('#skF_4'),A_207)
      | ~ r1_tarski(A_207,'#skF_3')
      | ~ r1_tarski(A_207,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4188,c_452])).

tff(c_297,plain,(
    ! [A_74,A_39,B_40] :
      ( k2_wellord1(k1_wellord2(A_74),A_39) = k2_wellord1(k1_wellord2(A_39),A_74)
      | ~ r1_tarski(A_74,B_40)
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_268])).

tff(c_3881,plain,(
    ! [A_39] :
      ( k2_wellord1(k1_wellord2(A_39),'#skF_4') = k2_wellord1(k1_wellord2('#skF_4'),A_39)
      | ~ r1_tarski(A_39,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_3852,c_297])).

tff(c_6874,plain,
    ( k2_wellord1(k1_wellord2('#skF_4'),'#skF_3') = k2_wellord1(k1_wellord2('#skF_4'),'#skF_4')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_4','#skF_3')
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6826,c_3881])).

tff(c_7045,plain,(
    k2_wellord1(k1_wellord2('#skF_4'),'#skF_3') = k2_wellord1(k1_wellord2('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3852,c_6,c_6874])).

tff(c_4380,plain,(
    ! [A_183] :
      ( k2_wellord1(k1_wellord2(A_183),'#skF_3') = k1_wellord2(A_183)
      | ~ r1_tarski(A_183,'#skF_4')
      | ~ r1_tarski(A_183,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4188,c_48])).

tff(c_7099,plain,
    ( k2_wellord1(k1_wellord2('#skF_4'),'#skF_4') = k1_wellord2('#skF_4')
    | ~ r1_tarski('#skF_4','#skF_4')
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7045,c_4380])).

tff(c_7228,plain,(
    k2_wellord1(k1_wellord2('#skF_4'),'#skF_4') = k1_wellord2('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_7099])).

tff(c_7277,plain,(
    k2_wellord1(k1_wellord2('#skF_4'),'#skF_3') = k1_wellord2('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7228,c_7045])).

tff(c_443,plain,(
    ! [B_37,A_35] :
      ( ~ r4_wellord1(k1_wellord2(B_37),k2_wellord1(k1_wellord2(B_37),A_35))
      | ~ v2_wellord1(k1_wellord2(B_37))
      | ~ r2_hidden(A_35,B_37)
      | ~ v3_ordinal1(B_37)
      | ~ v3_ordinal1(A_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_62,c_437])).

tff(c_7536,plain,
    ( ~ r4_wellord1(k1_wellord2('#skF_4'),k1_wellord2('#skF_4'))
    | ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7277,c_443])).

tff(c_7629,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_373,c_7536])).

tff(c_7878,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_7629])).

tff(c_7881,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_7878])).

tff(c_7887,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_7881])).

tff(c_7889,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3900,c_50,c_7887])).

tff(c_7890,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_7629])).

tff(c_7894,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_7890])).

tff(c_7898,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_7894])).

tff(c_7899,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | ~ v2_wellord1(k1_wellord2('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3803])).

tff(c_7959,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_7899])).

tff(c_7962,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_7959])).

tff(c_7966,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_7962])).

tff(c_7967,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_7899])).

tff(c_7971,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_4','#skF_3')
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_7967])).

tff(c_7977,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_56,c_7971])).

tff(c_7978,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_7977])).

tff(c_358,plain,(
    ! [A_81] :
      ( r4_wellord1(A_81,k1_wellord2('#skF_3'))
      | ~ r4_wellord1(A_81,k1_wellord2('#skF_4'))
      | ~ v1_relat_1(k1_wellord2('#skF_3'))
      | ~ v1_relat_1(k1_wellord2('#skF_4'))
      | ~ v1_relat_1(A_81) ) ),
    inference(resolution,[status(thm)],[c_126,c_356])).

tff(c_384,plain,(
    ! [A_85] :
      ( r4_wellord1(A_85,k1_wellord2('#skF_3'))
      | ~ r4_wellord1(A_85,k1_wellord2('#skF_4'))
      | ~ v1_relat_1(A_85) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_358])).

tff(c_18,plain,(
    ! [B_15,A_13] :
      ( r4_wellord1(B_15,A_13)
      | ~ r4_wellord1(A_13,B_15)
      | ~ v1_relat_1(B_15)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_391,plain,(
    ! [A_85] :
      ( r4_wellord1(k1_wellord2('#skF_3'),A_85)
      | ~ v1_relat_1(k1_wellord2('#skF_3'))
      | ~ r4_wellord1(A_85,k1_wellord2('#skF_4'))
      | ~ v1_relat_1(A_85) ) ),
    inference(resolution,[status(thm)],[c_384,c_18])).

tff(c_399,plain,(
    ! [A_86] :
      ( r4_wellord1(k1_wellord2('#skF_3'),A_86)
      | ~ r4_wellord1(A_86,k1_wellord2('#skF_4'))
      | ~ v1_relat_1(A_86) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_391])).

tff(c_403,plain,
    ( r4_wellord1(k1_wellord2('#skF_3'),k1_wellord2('#skF_3'))
    | ~ v1_relat_1(k1_wellord2('#skF_3')) ),
    inference(resolution,[status(thm)],[c_52,c_399])).

tff(c_409,plain,(
    r4_wellord1(k1_wellord2('#skF_3'),k1_wellord2('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_403])).

tff(c_7900,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_3803])).

tff(c_8270,plain,(
    ! [A_216] :
      ( k2_wellord1(k1_wellord2(A_216),'#skF_4') = k2_wellord1(k1_wellord2('#skF_3'),A_216)
      | ~ r1_tarski(A_216,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_7900,c_770])).

tff(c_8547,plain,(
    ! [A_217] :
      ( k2_wellord1(k1_wellord2(A_217),'#skF_4') = k1_wellord2(A_217)
      | ~ r1_tarski(A_217,'#skF_3')
      | ~ r1_tarski(A_217,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8270,c_48])).

tff(c_7929,plain,(
    ! [A_39] :
      ( k2_wellord1(k1_wellord2(A_39),'#skF_3') = k2_wellord1(k1_wellord2('#skF_3'),A_39)
      | ~ r1_tarski(A_39,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_7900,c_297])).

tff(c_8561,plain,
    ( k2_wellord1(k1_wellord2('#skF_4'),'#skF_3') = k1_wellord2('#skF_3')
    | ~ r1_tarski('#skF_4','#skF_4')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8547,c_7929])).

tff(c_8697,plain,(
    k2_wellord1(k1_wellord2('#skF_4'),'#skF_3') = k1_wellord2('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6,c_6,c_8561])).

tff(c_659,plain,(
    ! [A_98,B_11,B_99] :
      ( k2_wellord1(k2_wellord1(k1_wellord2(A_98),B_11),B_99) = k2_wellord1(k1_wellord2(A_98),B_11)
      | ~ r1_tarski(A_98,B_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_633])).

tff(c_8776,plain,(
    ! [B_99] :
      ( k2_wellord1(k1_wellord2('#skF_3'),B_99) = k2_wellord1(k1_wellord2('#skF_4'),'#skF_3')
      | ~ r1_tarski('#skF_4',B_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8697,c_659])).

tff(c_8832,plain,(
    ! [B_218] :
      ( k2_wellord1(k1_wellord2('#skF_3'),B_218) = k1_wellord2('#skF_3')
      | ~ r1_tarski('#skF_4',B_218) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8697,c_8776])).

tff(c_8911,plain,(
    ! [B_218] :
      ( ~ r4_wellord1(k1_wellord2('#skF_3'),k1_wellord2('#skF_3'))
      | ~ v2_wellord1(k1_wellord2('#skF_3'))
      | ~ r2_hidden(B_218,'#skF_3')
      | ~ v3_ordinal1('#skF_3')
      | ~ v3_ordinal1(B_218)
      | ~ r1_tarski('#skF_4',B_218) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8832,c_443])).

tff(c_8990,plain,(
    ! [B_218] :
      ( ~ v2_wellord1(k1_wellord2('#skF_3'))
      | ~ r2_hidden(B_218,'#skF_3')
      | ~ v3_ordinal1(B_218)
      | ~ r1_tarski('#skF_4',B_218) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_409,c_8911])).

tff(c_10219,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_8990])).

tff(c_10222,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_10219])).

tff(c_10226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_10222])).

tff(c_10229,plain,(
    ! [B_226] :
      ( ~ r2_hidden(B_226,'#skF_3')
      | ~ v3_ordinal1(B_226)
      | ~ r1_tarski('#skF_4',B_226) ) ),
    inference(splitRight,[status(thm)],[c_8990])).

tff(c_10232,plain,
    ( ~ v3_ordinal1('#skF_4')
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_7978,c_10229])).

tff(c_10248,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_54,c_10232])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:50:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.53/2.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.53/2.87  
% 8.53/2.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.53/2.87  %$ r4_wellord1 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 8.53/2.87  
% 8.53/2.87  %Foreground sorts:
% 8.53/2.87  
% 8.53/2.87  
% 8.53/2.87  %Background operators:
% 8.53/2.87  
% 8.53/2.87  
% 8.53/2.87  %Foreground operators:
% 8.53/2.87  tff(r4_wellord1, type, r4_wellord1: ($i * $i) > $o).
% 8.53/2.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.53/2.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.53/2.87  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.53/2.87  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 8.53/2.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.53/2.87  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 8.53/2.87  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 8.53/2.87  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 8.53/2.87  tff('#skF_3', type, '#skF_3': $i).
% 8.53/2.87  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 8.53/2.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.53/2.87  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.53/2.87  tff('#skF_4', type, '#skF_4': $i).
% 8.53/2.87  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 8.53/2.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.53/2.87  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.53/2.87  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 8.53/2.87  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.53/2.87  
% 8.53/2.90  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.53/2.90  tff(f_143, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r4_wellord1(k1_wellord2(A), k1_wellord2(B)) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_wellord2)).
% 8.53/2.90  tff(f_62, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 8.53/2.90  tff(f_129, axiom, (![A]: (v3_ordinal1(A) => v2_wellord1(k1_wellord2(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_wellord2)).
% 8.53/2.90  tff(f_39, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 8.53/2.90  tff(f_47, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 8.53/2.90  tff(f_116, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 8.53/2.90  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r4_wellord1(A, B) => r4_wellord1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_wellord1)).
% 8.53/2.90  tff(f_133, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_wellord2)).
% 8.53/2.90  tff(f_114, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 8.53/2.90  tff(f_125, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) => (A = k1_wellord1(k1_wellord2(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_wellord2)).
% 8.53/2.90  tff(f_99, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) => (![B]: ~(r2_hidden(B, k3_relat_1(A)) & r4_wellord1(A, k2_wellord1(A, k1_wellord1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_wellord1)).
% 8.53/2.90  tff(f_89, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((r4_wellord1(A, B) & r4_wellord1(B, C)) => r4_wellord1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_wellord1)).
% 8.53/2.90  tff(f_66, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(k2_wellord1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_wellord1)).
% 8.53/2.90  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.53/2.90  tff(c_54, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 8.53/2.90  tff(c_50, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_143])).
% 8.53/2.90  tff(c_56, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_143])).
% 8.53/2.90  tff(c_14, plain, (![B_9, A_7]: (r2_hidden(B_9, A_7) | B_9=A_7 | r2_hidden(A_7, B_9) | ~v3_ordinal1(B_9) | ~v3_ordinal1(A_7))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.53/2.90  tff(c_46, plain, (![A_38]: (v2_wellord1(k1_wellord2(A_38)) | ~v3_ordinal1(A_38))), inference(cnfTransformation, [status(thm)], [f_129])).
% 8.53/2.90  tff(c_8, plain, (![B_4, A_3]: (r1_ordinal1(B_4, A_3) | r1_ordinal1(A_3, B_4) | ~v3_ordinal1(B_4) | ~v3_ordinal1(A_3))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.53/2.90  tff(c_12, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~r1_ordinal1(A_5, B_6) | ~v3_ordinal1(B_6) | ~v3_ordinal1(A_5))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.53/2.90  tff(c_42, plain, (![A_34]: (v1_relat_1(k1_wellord2(A_34)))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.53/2.90  tff(c_52, plain, (r4_wellord1(k1_wellord2('#skF_3'), k1_wellord2('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 8.53/2.90  tff(c_121, plain, (![B_57, A_58]: (r4_wellord1(B_57, A_58) | ~r4_wellord1(A_58, B_57) | ~v1_relat_1(B_57) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.53/2.90  tff(c_123, plain, (r4_wellord1(k1_wellord2('#skF_4'), k1_wellord2('#skF_3')) | ~v1_relat_1(k1_wellord2('#skF_4')) | ~v1_relat_1(k1_wellord2('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_121])).
% 8.53/2.90  tff(c_126, plain, (r4_wellord1(k1_wellord2('#skF_4'), k1_wellord2('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_123])).
% 8.53/2.90  tff(c_48, plain, (![B_40, A_39]: (k2_wellord1(k1_wellord2(B_40), A_39)=k1_wellord2(A_39) | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_133])).
% 8.53/2.90  tff(c_36, plain, (![A_26]: (k3_relat_1(k1_wellord2(A_26))=A_26 | ~v1_relat_1(k1_wellord2(A_26)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 8.53/2.90  tff(c_62, plain, (![A_26]: (k3_relat_1(k1_wellord2(A_26))=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_36])).
% 8.53/2.90  tff(c_44, plain, (![B_37, A_35]: (k1_wellord1(k1_wellord2(B_37), A_35)=A_35 | ~r2_hidden(A_35, B_37) | ~v3_ordinal1(B_37) | ~v3_ordinal1(A_35))), inference(cnfTransformation, [status(thm)], [f_125])).
% 8.53/2.90  tff(c_426, plain, (![A_87, B_88]: (~r4_wellord1(A_87, k2_wellord1(A_87, k1_wellord1(A_87, B_88))) | ~r2_hidden(B_88, k3_relat_1(A_87)) | ~v2_wellord1(A_87) | ~v1_relat_1(A_87))), inference(cnfTransformation, [status(thm)], [f_99])).
% 8.53/2.90  tff(c_437, plain, (![B_37, A_35]: (~r4_wellord1(k1_wellord2(B_37), k2_wellord1(k1_wellord2(B_37), A_35)) | ~r2_hidden(A_35, k3_relat_1(k1_wellord2(B_37))) | ~v2_wellord1(k1_wellord2(B_37)) | ~v1_relat_1(k1_wellord2(B_37)) | ~r2_hidden(A_35, B_37) | ~v3_ordinal1(B_37) | ~v3_ordinal1(A_35))), inference(superposition, [status(thm), theory('equality')], [c_44, c_426])).
% 8.53/2.90  tff(c_896, plain, (![B_119, A_120]: (~r4_wellord1(k1_wellord2(B_119), k2_wellord1(k1_wellord2(B_119), A_120)) | ~v2_wellord1(k1_wellord2(B_119)) | ~r2_hidden(A_120, B_119) | ~v3_ordinal1(B_119) | ~v3_ordinal1(A_120))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_62, c_437])).
% 8.53/2.90  tff(c_3775, plain, (![B_177, A_178]: (~r4_wellord1(k1_wellord2(B_177), k1_wellord2(A_178)) | ~v2_wellord1(k1_wellord2(B_177)) | ~r2_hidden(A_178, B_177) | ~v3_ordinal1(B_177) | ~v3_ordinal1(A_178) | ~r1_tarski(A_178, B_177))), inference(superposition, [status(thm), theory('equality')], [c_48, c_896])).
% 8.53/2.90  tff(c_3788, plain, (~v2_wellord1(k1_wellord2('#skF_4')) | ~r2_hidden('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3') | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_126, c_3775])).
% 8.53/2.90  tff(c_3803, plain, (~v2_wellord1(k1_wellord2('#skF_4')) | ~r2_hidden('#skF_3', '#skF_4') | ~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_3788])).
% 8.53/2.90  tff(c_3813, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_3803])).
% 8.53/2.90  tff(c_3816, plain, (~r1_ordinal1('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_3813])).
% 8.53/2.90  tff(c_3819, plain, (~r1_ordinal1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_3816])).
% 8.53/2.90  tff(c_3822, plain, (r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_8, c_3819])).
% 8.53/2.90  tff(c_3828, plain, (r1_ordinal1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_3822])).
% 8.53/2.90  tff(c_3791, plain, (~v2_wellord1(k1_wellord2('#skF_3')) | ~r2_hidden('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4') | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_3775])).
% 8.53/2.90  tff(c_3806, plain, (~v2_wellord1(k1_wellord2('#skF_3')) | ~r2_hidden('#skF_4', '#skF_3') | ~r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_3791])).
% 8.53/2.90  tff(c_3843, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_3806])).
% 8.53/2.90  tff(c_3846, plain, (~r1_ordinal1('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_3843])).
% 8.53/2.90  tff(c_3850, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_3828, c_3846])).
% 8.53/2.90  tff(c_3851, plain, (~r2_hidden('#skF_4', '#skF_3') | ~v2_wellord1(k1_wellord2('#skF_3'))), inference(splitRight, [status(thm)], [c_3806])).
% 8.53/2.90  tff(c_3892, plain, (~v2_wellord1(k1_wellord2('#skF_3'))), inference(splitLeft, [status(thm)], [c_3851])).
% 8.53/2.90  tff(c_3895, plain, (~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_3892])).
% 8.53/2.90  tff(c_3899, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_3895])).
% 8.53/2.90  tff(c_3900, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_3851])).
% 8.53/2.90  tff(c_356, plain, (![A_81, C_82, B_83]: (r4_wellord1(A_81, C_82) | ~r4_wellord1(B_83, C_82) | ~r4_wellord1(A_81, B_83) | ~v1_relat_1(C_82) | ~v1_relat_1(B_83) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.53/2.90  tff(c_360, plain, (![A_81]: (r4_wellord1(A_81, k1_wellord2('#skF_4')) | ~r4_wellord1(A_81, k1_wellord2('#skF_3')) | ~v1_relat_1(k1_wellord2('#skF_4')) | ~v1_relat_1(k1_wellord2('#skF_3')) | ~v1_relat_1(A_81))), inference(resolution, [status(thm)], [c_52, c_356])).
% 8.53/2.90  tff(c_367, plain, (![A_84]: (r4_wellord1(A_84, k1_wellord2('#skF_4')) | ~r4_wellord1(A_84, k1_wellord2('#skF_3')) | ~v1_relat_1(A_84))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_360])).
% 8.53/2.90  tff(c_370, plain, (r4_wellord1(k1_wellord2('#skF_4'), k1_wellord2('#skF_4')) | ~v1_relat_1(k1_wellord2('#skF_4'))), inference(resolution, [status(thm)], [c_126, c_367])).
% 8.53/2.90  tff(c_373, plain, (r4_wellord1(k1_wellord2('#skF_4'), k1_wellord2('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_370])).
% 8.53/2.90  tff(c_3852, plain, (r1_tarski('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_3806])).
% 8.53/2.90  tff(c_127, plain, (![C_59, B_60, A_61]: (k2_wellord1(k2_wellord1(C_59, B_60), A_61)=k2_wellord1(k2_wellord1(C_59, A_61), B_60) | ~v1_relat_1(C_59))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.53/2.90  tff(c_181, plain, (![B_40, B_60, A_39]: (k2_wellord1(k2_wellord1(k1_wellord2(B_40), B_60), A_39)=k2_wellord1(k1_wellord2(A_39), B_60) | ~v1_relat_1(k1_wellord2(B_40)) | ~r1_tarski(A_39, B_40))), inference(superposition, [status(thm), theory('equality')], [c_48, c_127])).
% 8.53/2.90  tff(c_268, plain, (![B_72, B_73, A_74]: (k2_wellord1(k2_wellord1(k1_wellord2(B_72), B_73), A_74)=k2_wellord1(k1_wellord2(A_74), B_73) | ~r1_tarski(A_74, B_72))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_181])).
% 8.53/2.90  tff(c_446, plain, (![A_90, A_89, B_91]: (k2_wellord1(k1_wellord2(A_90), A_89)=k2_wellord1(k1_wellord2(A_89), A_90) | ~r1_tarski(A_89, B_91) | ~r1_tarski(A_90, B_91))), inference(superposition, [status(thm), theory('equality')], [c_48, c_268])).
% 8.53/2.90  tff(c_453, plain, (![B_92, A_93]: (k2_wellord1(k1_wellord2(B_92), A_93)=k2_wellord1(k1_wellord2(A_93), B_92) | ~r1_tarski(A_93, B_92))), inference(resolution, [status(thm)], [c_6, c_446])).
% 8.53/2.90  tff(c_605, plain, (![A_98, B_99]: (k2_wellord1(k1_wellord2(A_98), B_99)=k1_wellord2(A_98) | ~r1_tarski(A_98, B_99) | ~r1_tarski(A_98, B_99))), inference(superposition, [status(thm), theory('equality')], [c_48, c_453])).
% 8.53/2.90  tff(c_16, plain, (![C_12, B_11, A_10]: (k2_wellord1(k2_wellord1(C_12, B_11), A_10)=k2_wellord1(k2_wellord1(C_12, A_10), B_11) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.53/2.90  tff(c_633, plain, (![A_98, B_11, B_99]: (k2_wellord1(k2_wellord1(k1_wellord2(A_98), B_11), B_99)=k2_wellord1(k1_wellord2(A_98), B_11) | ~v1_relat_1(k1_wellord2(A_98)) | ~r1_tarski(A_98, B_99) | ~r1_tarski(A_98, B_99))), inference(superposition, [status(thm), theory('equality')], [c_605, c_16])).
% 8.53/2.90  tff(c_713, plain, (![A_106, B_107, B_108]: (k2_wellord1(k2_wellord1(k1_wellord2(A_106), B_107), B_108)=k2_wellord1(k1_wellord2(A_106), B_107) | ~r1_tarski(A_106, B_108))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_633])).
% 8.53/2.90  tff(c_770, plain, (![B_40, A_39, B_108]: (k2_wellord1(k1_wellord2(B_40), A_39)=k2_wellord1(k1_wellord2(A_39), B_108) | ~r1_tarski(B_40, B_108) | ~r1_tarski(A_39, B_40))), inference(superposition, [status(thm), theory('equality')], [c_48, c_713])).
% 8.53/2.90  tff(c_4188, plain, (![A_183]: (k2_wellord1(k1_wellord2(A_183), '#skF_3')=k2_wellord1(k1_wellord2('#skF_4'), A_183) | ~r1_tarski(A_183, '#skF_4'))), inference(resolution, [status(thm)], [c_3852, c_770])).
% 8.53/2.90  tff(c_452, plain, (![B_2, A_90]: (k2_wellord1(k1_wellord2(B_2), A_90)=k2_wellord1(k1_wellord2(A_90), B_2) | ~r1_tarski(A_90, B_2))), inference(resolution, [status(thm)], [c_6, c_446])).
% 8.53/2.90  tff(c_6826, plain, (![A_207]: (k2_wellord1(k1_wellord2('#skF_3'), A_207)=k2_wellord1(k1_wellord2('#skF_4'), A_207) | ~r1_tarski(A_207, '#skF_3') | ~r1_tarski(A_207, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4188, c_452])).
% 8.53/2.90  tff(c_297, plain, (![A_74, A_39, B_40]: (k2_wellord1(k1_wellord2(A_74), A_39)=k2_wellord1(k1_wellord2(A_39), A_74) | ~r1_tarski(A_74, B_40) | ~r1_tarski(A_39, B_40))), inference(superposition, [status(thm), theory('equality')], [c_48, c_268])).
% 8.53/2.90  tff(c_3881, plain, (![A_39]: (k2_wellord1(k1_wellord2(A_39), '#skF_4')=k2_wellord1(k1_wellord2('#skF_4'), A_39) | ~r1_tarski(A_39, '#skF_3'))), inference(resolution, [status(thm)], [c_3852, c_297])).
% 8.53/2.90  tff(c_6874, plain, (k2_wellord1(k1_wellord2('#skF_4'), '#skF_3')=k2_wellord1(k1_wellord2('#skF_4'), '#skF_4') | ~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_4', '#skF_3') | ~r1_tarski('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6826, c_3881])).
% 8.53/2.90  tff(c_7045, plain, (k2_wellord1(k1_wellord2('#skF_4'), '#skF_3')=k2_wellord1(k1_wellord2('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_3852, c_6, c_6874])).
% 8.53/2.90  tff(c_4380, plain, (![A_183]: (k2_wellord1(k1_wellord2(A_183), '#skF_3')=k1_wellord2(A_183) | ~r1_tarski(A_183, '#skF_4') | ~r1_tarski(A_183, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4188, c_48])).
% 8.53/2.90  tff(c_7099, plain, (k2_wellord1(k1_wellord2('#skF_4'), '#skF_4')=k1_wellord2('#skF_4') | ~r1_tarski('#skF_4', '#skF_4') | ~r1_tarski('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7045, c_4380])).
% 8.53/2.90  tff(c_7228, plain, (k2_wellord1(k1_wellord2('#skF_4'), '#skF_4')=k1_wellord2('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_7099])).
% 8.53/2.90  tff(c_7277, plain, (k2_wellord1(k1_wellord2('#skF_4'), '#skF_3')=k1_wellord2('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7228, c_7045])).
% 8.53/2.90  tff(c_443, plain, (![B_37, A_35]: (~r4_wellord1(k1_wellord2(B_37), k2_wellord1(k1_wellord2(B_37), A_35)) | ~v2_wellord1(k1_wellord2(B_37)) | ~r2_hidden(A_35, B_37) | ~v3_ordinal1(B_37) | ~v3_ordinal1(A_35))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_62, c_437])).
% 8.53/2.90  tff(c_7536, plain, (~r4_wellord1(k1_wellord2('#skF_4'), k1_wellord2('#skF_4')) | ~v2_wellord1(k1_wellord2('#skF_4')) | ~r2_hidden('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7277, c_443])).
% 8.53/2.90  tff(c_7629, plain, (~v2_wellord1(k1_wellord2('#skF_4')) | ~r2_hidden('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_373, c_7536])).
% 8.53/2.90  tff(c_7878, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_7629])).
% 8.53/2.90  tff(c_7881, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_7878])).
% 8.53/2.90  tff(c_7887, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_7881])).
% 8.53/2.90  tff(c_7889, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3900, c_50, c_7887])).
% 8.53/2.90  tff(c_7890, plain, (~v2_wellord1(k1_wellord2('#skF_4'))), inference(splitRight, [status(thm)], [c_7629])).
% 8.53/2.90  tff(c_7894, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_7890])).
% 8.53/2.90  tff(c_7898, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_7894])).
% 8.53/2.90  tff(c_7899, plain, (~r2_hidden('#skF_3', '#skF_4') | ~v2_wellord1(k1_wellord2('#skF_4'))), inference(splitRight, [status(thm)], [c_3803])).
% 8.53/2.90  tff(c_7959, plain, (~v2_wellord1(k1_wellord2('#skF_4'))), inference(splitLeft, [status(thm)], [c_7899])).
% 8.53/2.90  tff(c_7962, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_7959])).
% 8.53/2.90  tff(c_7966, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_7962])).
% 8.53/2.90  tff(c_7967, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_7899])).
% 8.53/2.90  tff(c_7971, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_4', '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_7967])).
% 8.53/2.90  tff(c_7977, plain, ('#skF_3'='#skF_4' | r2_hidden('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_56, c_7971])).
% 8.53/2.90  tff(c_7978, plain, (r2_hidden('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_50, c_7977])).
% 8.53/2.90  tff(c_358, plain, (![A_81]: (r4_wellord1(A_81, k1_wellord2('#skF_3')) | ~r4_wellord1(A_81, k1_wellord2('#skF_4')) | ~v1_relat_1(k1_wellord2('#skF_3')) | ~v1_relat_1(k1_wellord2('#skF_4')) | ~v1_relat_1(A_81))), inference(resolution, [status(thm)], [c_126, c_356])).
% 8.53/2.90  tff(c_384, plain, (![A_85]: (r4_wellord1(A_85, k1_wellord2('#skF_3')) | ~r4_wellord1(A_85, k1_wellord2('#skF_4')) | ~v1_relat_1(A_85))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_358])).
% 8.53/2.90  tff(c_18, plain, (![B_15, A_13]: (r4_wellord1(B_15, A_13) | ~r4_wellord1(A_13, B_15) | ~v1_relat_1(B_15) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.53/2.90  tff(c_391, plain, (![A_85]: (r4_wellord1(k1_wellord2('#skF_3'), A_85) | ~v1_relat_1(k1_wellord2('#skF_3')) | ~r4_wellord1(A_85, k1_wellord2('#skF_4')) | ~v1_relat_1(A_85))), inference(resolution, [status(thm)], [c_384, c_18])).
% 8.53/2.90  tff(c_399, plain, (![A_86]: (r4_wellord1(k1_wellord2('#skF_3'), A_86) | ~r4_wellord1(A_86, k1_wellord2('#skF_4')) | ~v1_relat_1(A_86))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_391])).
% 8.53/2.90  tff(c_403, plain, (r4_wellord1(k1_wellord2('#skF_3'), k1_wellord2('#skF_3')) | ~v1_relat_1(k1_wellord2('#skF_3'))), inference(resolution, [status(thm)], [c_52, c_399])).
% 8.53/2.90  tff(c_409, plain, (r4_wellord1(k1_wellord2('#skF_3'), k1_wellord2('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_403])).
% 8.53/2.90  tff(c_7900, plain, (r1_tarski('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_3803])).
% 8.53/2.90  tff(c_8270, plain, (![A_216]: (k2_wellord1(k1_wellord2(A_216), '#skF_4')=k2_wellord1(k1_wellord2('#skF_3'), A_216) | ~r1_tarski(A_216, '#skF_3'))), inference(resolution, [status(thm)], [c_7900, c_770])).
% 8.53/2.90  tff(c_8547, plain, (![A_217]: (k2_wellord1(k1_wellord2(A_217), '#skF_4')=k1_wellord2(A_217) | ~r1_tarski(A_217, '#skF_3') | ~r1_tarski(A_217, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_8270, c_48])).
% 8.53/2.90  tff(c_7929, plain, (![A_39]: (k2_wellord1(k1_wellord2(A_39), '#skF_3')=k2_wellord1(k1_wellord2('#skF_3'), A_39) | ~r1_tarski(A_39, '#skF_4'))), inference(resolution, [status(thm)], [c_7900, c_297])).
% 8.53/2.90  tff(c_8561, plain, (k2_wellord1(k1_wellord2('#skF_4'), '#skF_3')=k1_wellord2('#skF_3') | ~r1_tarski('#skF_4', '#skF_4') | ~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8547, c_7929])).
% 8.53/2.90  tff(c_8697, plain, (k2_wellord1(k1_wellord2('#skF_4'), '#skF_3')=k1_wellord2('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_6, c_6, c_8561])).
% 8.53/2.90  tff(c_659, plain, (![A_98, B_11, B_99]: (k2_wellord1(k2_wellord1(k1_wellord2(A_98), B_11), B_99)=k2_wellord1(k1_wellord2(A_98), B_11) | ~r1_tarski(A_98, B_99))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_633])).
% 8.53/2.90  tff(c_8776, plain, (![B_99]: (k2_wellord1(k1_wellord2('#skF_3'), B_99)=k2_wellord1(k1_wellord2('#skF_4'), '#skF_3') | ~r1_tarski('#skF_4', B_99))), inference(superposition, [status(thm), theory('equality')], [c_8697, c_659])).
% 8.53/2.90  tff(c_8832, plain, (![B_218]: (k2_wellord1(k1_wellord2('#skF_3'), B_218)=k1_wellord2('#skF_3') | ~r1_tarski('#skF_4', B_218))), inference(demodulation, [status(thm), theory('equality')], [c_8697, c_8776])).
% 8.53/2.90  tff(c_8911, plain, (![B_218]: (~r4_wellord1(k1_wellord2('#skF_3'), k1_wellord2('#skF_3')) | ~v2_wellord1(k1_wellord2('#skF_3')) | ~r2_hidden(B_218, '#skF_3') | ~v3_ordinal1('#skF_3') | ~v3_ordinal1(B_218) | ~r1_tarski('#skF_4', B_218))), inference(superposition, [status(thm), theory('equality')], [c_8832, c_443])).
% 8.53/2.90  tff(c_8990, plain, (![B_218]: (~v2_wellord1(k1_wellord2('#skF_3')) | ~r2_hidden(B_218, '#skF_3') | ~v3_ordinal1(B_218) | ~r1_tarski('#skF_4', B_218))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_409, c_8911])).
% 8.53/2.90  tff(c_10219, plain, (~v2_wellord1(k1_wellord2('#skF_3'))), inference(splitLeft, [status(thm)], [c_8990])).
% 8.53/2.90  tff(c_10222, plain, (~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_10219])).
% 8.53/2.90  tff(c_10226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_10222])).
% 8.53/2.90  tff(c_10229, plain, (![B_226]: (~r2_hidden(B_226, '#skF_3') | ~v3_ordinal1(B_226) | ~r1_tarski('#skF_4', B_226))), inference(splitRight, [status(thm)], [c_8990])).
% 8.53/2.90  tff(c_10232, plain, (~v3_ordinal1('#skF_4') | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_7978, c_10229])).
% 8.53/2.90  tff(c_10248, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_54, c_10232])).
% 8.53/2.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.53/2.90  
% 8.53/2.90  Inference rules
% 8.53/2.90  ----------------------
% 8.53/2.90  #Ref     : 0
% 8.53/2.90  #Sup     : 2652
% 8.53/2.90  #Fact    : 4
% 8.53/2.90  #Define  : 0
% 8.53/2.90  #Split   : 9
% 8.53/2.90  #Chain   : 0
% 8.53/2.90  #Close   : 0
% 8.53/2.90  
% 8.53/2.90  Ordering : KBO
% 8.53/2.90  
% 8.53/2.90  Simplification rules
% 8.53/2.90  ----------------------
% 8.53/2.90  #Subsume      : 1005
% 8.53/2.90  #Demod        : 983
% 8.53/2.90  #Tautology    : 352
% 8.53/2.90  #SimpNegUnit  : 9
% 8.53/2.90  #BackRed      : 1
% 8.53/2.90  
% 8.53/2.90  #Partial instantiations: 0
% 8.53/2.90  #Strategies tried      : 1
% 8.53/2.90  
% 8.53/2.90  Timing (in seconds)
% 8.53/2.90  ----------------------
% 8.53/2.90  Preprocessing        : 0.38
% 8.53/2.90  Parsing              : 0.20
% 8.53/2.90  CNF conversion       : 0.03
% 8.53/2.90  Main loop            : 1.74
% 8.53/2.90  Inferencing          : 0.62
% 8.53/2.90  Reduction            : 0.44
% 8.53/2.90  Demodulation         : 0.30
% 8.53/2.90  BG Simplification    : 0.09
% 8.53/2.90  Subsumption          : 0.47
% 8.53/2.90  Abstraction          : 0.11
% 8.53/2.90  MUC search           : 0.00
% 8.53/2.90  Cooper               : 0.00
% 8.53/2.90  Total                : 2.16
% 8.53/2.90  Index Insertion      : 0.00
% 8.53/2.90  Index Deletion       : 0.00
% 8.53/2.90  Index Matching       : 0.00
% 8.53/2.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
