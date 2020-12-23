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
% DateTime   : Thu Dec  3 10:10:32 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 631 expanded)
%              Number of leaves         :   34 ( 236 expanded)
%              Depth                    :   16
%              Number of atoms          :  290 (1750 expanded)
%              Number of equality atoms :   33 ( 255 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_wellord1 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

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

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_140,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r4_wellord1(k1_wellord2(A),k1_wellord2(B))
             => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).

tff(f_126,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v2_wellord1(k1_wellord2(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).

tff(f_56,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
        | r1_ordinal1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_113,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_86,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
           => r4_wellord1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

tff(f_130,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_122,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
           => A = k1_wellord1(k1_wellord2(B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).

tff(f_96,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
       => ! [B] :
            ~ ( r2_hidden(B,k3_relat_1(A))
              & r4_wellord1(A,k2_wellord1(A,k1_wellord1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k3_relat_1(k2_wellord1(C,B)))
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_wellord1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k1_wellord1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( D != B
                & r2_hidden(k4_tarski(D,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

tff(c_68,plain,(
    v3_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_58,plain,(
    ! [A_41] :
      ( v2_wellord1(k1_wellord2(A_41))
      | ~ v3_ordinal1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_62,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_66,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_8,plain,(
    ! [B_7,A_5] :
      ( r2_hidden(B_7,A_5)
      | B_7 = A_5
      | r2_hidden(A_5,B_7)
      | ~ v3_ordinal1(B_7)
      | ~ v3_ordinal1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_ordinal1(B_2,A_1)
      | r1_ordinal1(A_1,B_2)
      | ~ v3_ordinal1(B_2)
      | ~ v3_ordinal1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ r1_ordinal1(A_3,B_4)
      | ~ v3_ordinal1(B_4)
      | ~ v3_ordinal1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_54,plain,(
    ! [A_37] : v1_relat_1(k1_wellord2(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_64,plain,(
    r4_wellord1(k1_wellord2('#skF_5'),k1_wellord2('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_118,plain,(
    ! [B_59,A_60] :
      ( r4_wellord1(B_59,A_60)
      | ~ r4_wellord1(A_60,B_59)
      | ~ v1_relat_1(B_59)
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_120,plain,
    ( r4_wellord1(k1_wellord2('#skF_6'),k1_wellord2('#skF_5'))
    | ~ v1_relat_1(k1_wellord2('#skF_6'))
    | ~ v1_relat_1(k1_wellord2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_64,c_118])).

tff(c_123,plain,(
    r4_wellord1(k1_wellord2('#skF_6'),k1_wellord2('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_120])).

tff(c_60,plain,(
    ! [B_43,A_42] :
      ( k2_wellord1(k1_wellord2(B_43),A_42) = k1_wellord2(A_42)
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_48,plain,(
    ! [A_29] :
      ( k3_relat_1(k1_wellord2(A_29)) = A_29
      | ~ v1_relat_1(k1_wellord2(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_74,plain,(
    ! [A_29] : k3_relat_1(k1_wellord2(A_29)) = A_29 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48])).

tff(c_56,plain,(
    ! [B_40,A_38] :
      ( k1_wellord1(k1_wellord2(B_40),A_38) = A_38
      | ~ r2_hidden(A_38,B_40)
      | ~ v3_ordinal1(B_40)
      | ~ v3_ordinal1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_322,plain,(
    ! [A_90,B_91] :
      ( ~ r4_wellord1(A_90,k2_wellord1(A_90,k1_wellord1(A_90,B_91)))
      | ~ r2_hidden(B_91,k3_relat_1(A_90))
      | ~ v2_wellord1(A_90)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_325,plain,(
    ! [B_40,A_38] :
      ( ~ r4_wellord1(k1_wellord2(B_40),k2_wellord1(k1_wellord2(B_40),A_38))
      | ~ r2_hidden(A_38,k3_relat_1(k1_wellord2(B_40)))
      | ~ v2_wellord1(k1_wellord2(B_40))
      | ~ v1_relat_1(k1_wellord2(B_40))
      | ~ r2_hidden(A_38,B_40)
      | ~ v3_ordinal1(B_40)
      | ~ v3_ordinal1(A_38) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_322])).

tff(c_457,plain,(
    ! [B_112,A_113] :
      ( ~ r4_wellord1(k1_wellord2(B_112),k2_wellord1(k1_wellord2(B_112),A_113))
      | ~ v2_wellord1(k1_wellord2(B_112))
      | ~ r2_hidden(A_113,B_112)
      | ~ v3_ordinal1(B_112)
      | ~ v3_ordinal1(A_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_74,c_325])).

tff(c_838,plain,(
    ! [B_146,A_147] :
      ( ~ r4_wellord1(k1_wellord2(B_146),k1_wellord2(A_147))
      | ~ v2_wellord1(k1_wellord2(B_146))
      | ~ r2_hidden(A_147,B_146)
      | ~ v3_ordinal1(B_146)
      | ~ v3_ordinal1(A_147)
      | ~ r1_tarski(A_147,B_146) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_457])).

tff(c_841,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_6'))
    | ~ r2_hidden('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5')
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_123,c_838])).

tff(c_847,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_6'))
    | ~ r2_hidden('#skF_5','#skF_6')
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_841])).

tff(c_851,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_847])).

tff(c_854,plain,
    ( ~ r1_ordinal1('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_851])).

tff(c_857,plain,(
    ~ r1_ordinal1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_854])).

tff(c_861,plain,
    ( r1_ordinal1('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_857])).

tff(c_867,plain,(
    r1_ordinal1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_861])).

tff(c_844,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_5'))
    | ~ r2_hidden('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6')
    | ~ r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_838])).

tff(c_850,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_5'))
    | ~ r2_hidden('#skF_6','#skF_5')
    | ~ r1_tarski('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_844])).

tff(c_925,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_850])).

tff(c_928,plain,
    ( ~ r1_ordinal1('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_925])).

tff(c_932,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_867,c_928])).

tff(c_933,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | ~ v2_wellord1(k1_wellord2('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_850])).

tff(c_949,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_933])).

tff(c_952,plain,(
    ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_949])).

tff(c_956,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_952])).

tff(c_957,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_933])).

tff(c_934,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_850])).

tff(c_158,plain,(
    ! [B_70,A_71] :
      ( r2_hidden(B_70,A_71)
      | B_70 = A_71
      | r2_hidden(A_71,B_70)
      | ~ v3_ordinal1(B_70)
      | ~ v3_ordinal1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_135,plain,(
    ! [A_64,C_65,B_66] :
      ( r2_hidden(A_64,k3_relat_1(C_65))
      | ~ r2_hidden(A_64,k3_relat_1(k2_wellord1(C_65,B_66)))
      | ~ v1_relat_1(C_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_138,plain,(
    ! [A_64,B_43,A_42] :
      ( r2_hidden(A_64,k3_relat_1(k1_wellord2(B_43)))
      | ~ r2_hidden(A_64,k3_relat_1(k1_wellord2(A_42)))
      | ~ v1_relat_1(k1_wellord2(B_43))
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_135])).

tff(c_140,plain,(
    ! [A_64,B_43,A_42] :
      ( r2_hidden(A_64,B_43)
      | ~ r2_hidden(A_64,A_42)
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_74,c_74,c_138])).

tff(c_186,plain,(
    ! [A_71,B_43,B_70] :
      ( r2_hidden(A_71,B_43)
      | ~ r1_tarski(B_70,B_43)
      | r2_hidden(B_70,A_71)
      | B_70 = A_71
      | ~ v3_ordinal1(B_70)
      | ~ v3_ordinal1(A_71) ) ),
    inference(resolution,[status(thm)],[c_158,c_140])).

tff(c_938,plain,(
    ! [A_71] :
      ( r2_hidden(A_71,'#skF_5')
      | r2_hidden('#skF_6',A_71)
      | A_71 = '#skF_6'
      | ~ v3_ordinal1('#skF_6')
      | ~ v3_ordinal1(A_71) ) ),
    inference(resolution,[status(thm)],[c_934,c_186])).

tff(c_945,plain,(
    ! [A_71] :
      ( r2_hidden(A_71,'#skF_5')
      | r2_hidden('#skF_6',A_71)
      | A_71 = '#skF_6'
      | ~ v3_ordinal1(A_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_938])).

tff(c_968,plain,(
    ! [A_149] :
      ( r2_hidden(A_149,'#skF_5')
      | r2_hidden('#skF_6',A_149)
      | A_149 = '#skF_6'
      | ~ v3_ordinal1(A_149) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_938])).

tff(c_208,plain,(
    ! [B_75,A_76] :
      ( k1_wellord1(k1_wellord2(B_75),A_76) = A_76
      | ~ r2_hidden(A_76,B_75)
      | ~ v3_ordinal1(B_75)
      | ~ v3_ordinal1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_14,plain,(
    ! [D_19,A_8] :
      ( ~ r2_hidden(D_19,k1_wellord1(A_8,D_19))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_214,plain,(
    ! [A_76,B_75] :
      ( ~ r2_hidden(A_76,A_76)
      | ~ v1_relat_1(k1_wellord2(B_75))
      | ~ r2_hidden(A_76,B_75)
      | ~ v3_ordinal1(B_75)
      | ~ v3_ordinal1(A_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_14])).

tff(c_220,plain,(
    ! [A_76,B_75] :
      ( ~ r2_hidden(A_76,A_76)
      | ~ r2_hidden(A_76,B_75)
      | ~ v3_ordinal1(B_75)
      | ~ v3_ordinal1(A_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_214])).

tff(c_995,plain,(
    ! [B_75] :
      ( ~ r2_hidden('#skF_5',B_75)
      | ~ v3_ordinal1(B_75)
      | r2_hidden('#skF_6','#skF_5')
      | '#skF_5' = '#skF_6'
      | ~ v3_ordinal1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_968,c_220])).

tff(c_1028,plain,(
    ! [B_75] :
      ( ~ r2_hidden('#skF_5',B_75)
      | ~ v3_ordinal1(B_75)
      | r2_hidden('#skF_6','#skF_5')
      | '#skF_5' = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_995])).

tff(c_1082,plain,(
    ! [B_151] :
      ( ~ r2_hidden('#skF_5',B_151)
      | ~ v3_ordinal1(B_151) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_957,c_1028])).

tff(c_1086,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | '#skF_5' = '#skF_6'
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_945,c_1082])).

tff(c_1109,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1086])).

tff(c_1111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_957,c_1109])).

tff(c_1112,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | ~ v2_wellord1(k1_wellord2('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_847])).

tff(c_1326,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1112])).

tff(c_1329,plain,(
    ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_1326])).

tff(c_1333,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1329])).

tff(c_1334,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_1112])).

tff(c_1387,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_8,c_1334])).

tff(c_1400,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_1387])).

tff(c_1401,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1400])).

tff(c_1143,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1112])).

tff(c_1146,plain,(
    ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_1143])).

tff(c_1150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1146])).

tff(c_1151,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_1112])).

tff(c_1164,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | '#skF_5' = '#skF_6'
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_1151])).

tff(c_1178,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1164])).

tff(c_1179,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1178])).

tff(c_1133,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_850])).

tff(c_1136,plain,
    ( ~ r1_ordinal1('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_1133])).

tff(c_1139,plain,(
    ~ r1_ordinal1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_1136])).

tff(c_372,plain,(
    ! [A_98,B_99,B_100] :
      ( r2_hidden(A_98,B_99)
      | ~ r1_tarski(B_100,B_99)
      | r2_hidden(B_100,A_98)
      | B_100 = A_98
      | ~ v3_ordinal1(B_100)
      | ~ v3_ordinal1(A_98) ) ),
    inference(resolution,[status(thm)],[c_158,c_140])).

tff(c_589,plain,(
    ! [A_125,B_126,A_127] :
      ( r2_hidden(A_125,B_126)
      | r2_hidden(A_127,A_125)
      | A_127 = A_125
      | ~ v3_ordinal1(A_125)
      | ~ r1_ordinal1(A_127,B_126)
      | ~ v3_ordinal1(B_126)
      | ~ v3_ordinal1(A_127) ) ),
    inference(resolution,[status(thm)],[c_6,c_372])).

tff(c_597,plain,(
    ! [A_125,A_1,B_2] :
      ( r2_hidden(A_125,A_1)
      | r2_hidden(B_2,A_125)
      | B_2 = A_125
      | ~ v3_ordinal1(A_125)
      | r1_ordinal1(A_1,B_2)
      | ~ v3_ordinal1(B_2)
      | ~ v3_ordinal1(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_589])).

tff(c_1158,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_6',A_1)
      | '#skF_5' = '#skF_6'
      | ~ v3_ordinal1('#skF_6')
      | r1_ordinal1(A_1,'#skF_5')
      | ~ v3_ordinal1('#skF_5')
      | ~ v3_ordinal1(A_1) ) ),
    inference(resolution,[status(thm)],[c_597,c_1151])).

tff(c_1170,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_6',A_1)
      | '#skF_5' = '#skF_6'
      | r1_ordinal1(A_1,'#skF_5')
      | ~ v3_ordinal1(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1158])).

tff(c_1232,plain,(
    ! [A_153] :
      ( r2_hidden('#skF_6',A_153)
      | r1_ordinal1(A_153,'#skF_5')
      | ~ v3_ordinal1(A_153) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1170])).

tff(c_1245,plain,(
    ! [B_75] :
      ( ~ r2_hidden('#skF_6',B_75)
      | ~ v3_ordinal1(B_75)
      | r1_ordinal1('#skF_6','#skF_5')
      | ~ v3_ordinal1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1232,c_220])).

tff(c_1267,plain,(
    ! [B_75] :
      ( ~ r2_hidden('#skF_6',B_75)
      | ~ v3_ordinal1(B_75)
      | r1_ordinal1('#skF_6','#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1245])).

tff(c_1273,plain,(
    ! [B_154] :
      ( ~ r2_hidden('#skF_6',B_154)
      | ~ v3_ordinal1(B_154) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1139,c_1267])).

tff(c_1279,plain,(
    ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1179,c_1273])).

tff(c_1304,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1279])).

tff(c_1305,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | ~ v2_wellord1(k1_wellord2('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_850])).

tff(c_1416,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1401,c_1305])).

tff(c_1419,plain,(
    ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_1416])).

tff(c_1423,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1419])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n019.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 10:43:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.46/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.61  
% 3.80/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.61  %$ r4_wellord1 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 3.80/1.61  
% 3.80/1.61  %Foreground sorts:
% 3.80/1.61  
% 3.80/1.61  
% 3.80/1.61  %Background operators:
% 3.80/1.61  
% 3.80/1.61  
% 3.80/1.61  %Foreground operators:
% 3.80/1.61  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.80/1.61  tff(r4_wellord1, type, r4_wellord1: ($i * $i) > $o).
% 3.80/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.80/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.80/1.61  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.80/1.61  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.80/1.61  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.80/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.80/1.61  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 3.80/1.61  tff('#skF_5', type, '#skF_5': $i).
% 3.80/1.61  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 3.80/1.61  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 3.80/1.61  tff('#skF_6', type, '#skF_6': $i).
% 3.80/1.61  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.80/1.61  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 3.80/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.80/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.80/1.61  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 3.80/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.80/1.61  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 3.80/1.61  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.80/1.61  
% 3.80/1.63  tff(f_140, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r4_wellord1(k1_wellord2(A), k1_wellord2(B)) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_wellord2)).
% 3.80/1.63  tff(f_126, axiom, (![A]: (v3_ordinal1(A) => v2_wellord1(k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_wellord2)).
% 3.80/1.63  tff(f_56, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 3.80/1.63  tff(f_33, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) | r1_ordinal1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', connectedness_r1_ordinal1)).
% 3.80/1.63  tff(f_41, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 3.80/1.63  tff(f_113, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 3.80/1.63  tff(f_86, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r4_wellord1(A, B) => r4_wellord1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_wellord1)).
% 3.80/1.63  tff(f_130, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_wellord2)).
% 3.80/1.63  tff(f_111, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 3.80/1.63  tff(f_122, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) => (A = k1_wellord1(k1_wellord2(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_wellord2)).
% 3.80/1.63  tff(f_96, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) => (![B]: ~(r2_hidden(B, k3_relat_1(A)) & r4_wellord1(A, k2_wellord1(A, k1_wellord1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_wellord1)).
% 3.80/1.63  tff(f_77, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k3_relat_1(k2_wellord1(C, B))) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_wellord1)).
% 3.80/1.63  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k1_wellord1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (~(D = B) & r2_hidden(k4_tarski(D, B), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord1)).
% 3.80/1.63  tff(c_68, plain, (v3_ordinal1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.80/1.63  tff(c_58, plain, (![A_41]: (v2_wellord1(k1_wellord2(A_41)) | ~v3_ordinal1(A_41))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.80/1.63  tff(c_62, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.80/1.63  tff(c_66, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.80/1.63  tff(c_8, plain, (![B_7, A_5]: (r2_hidden(B_7, A_5) | B_7=A_5 | r2_hidden(A_5, B_7) | ~v3_ordinal1(B_7) | ~v3_ordinal1(A_5))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.80/1.63  tff(c_2, plain, (![B_2, A_1]: (r1_ordinal1(B_2, A_1) | r1_ordinal1(A_1, B_2) | ~v3_ordinal1(B_2) | ~v3_ordinal1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.80/1.63  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~r1_ordinal1(A_3, B_4) | ~v3_ordinal1(B_4) | ~v3_ordinal1(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.80/1.63  tff(c_54, plain, (![A_37]: (v1_relat_1(k1_wellord2(A_37)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.80/1.63  tff(c_64, plain, (r4_wellord1(k1_wellord2('#skF_5'), k1_wellord2('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 3.80/1.63  tff(c_118, plain, (![B_59, A_60]: (r4_wellord1(B_59, A_60) | ~r4_wellord1(A_60, B_59) | ~v1_relat_1(B_59) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.80/1.63  tff(c_120, plain, (r4_wellord1(k1_wellord2('#skF_6'), k1_wellord2('#skF_5')) | ~v1_relat_1(k1_wellord2('#skF_6')) | ~v1_relat_1(k1_wellord2('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_118])).
% 3.80/1.63  tff(c_123, plain, (r4_wellord1(k1_wellord2('#skF_6'), k1_wellord2('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_54, c_120])).
% 3.80/1.63  tff(c_60, plain, (![B_43, A_42]: (k2_wellord1(k1_wellord2(B_43), A_42)=k1_wellord2(A_42) | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.80/1.63  tff(c_48, plain, (![A_29]: (k3_relat_1(k1_wellord2(A_29))=A_29 | ~v1_relat_1(k1_wellord2(A_29)))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.80/1.63  tff(c_74, plain, (![A_29]: (k3_relat_1(k1_wellord2(A_29))=A_29)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_48])).
% 3.80/1.63  tff(c_56, plain, (![B_40, A_38]: (k1_wellord1(k1_wellord2(B_40), A_38)=A_38 | ~r2_hidden(A_38, B_40) | ~v3_ordinal1(B_40) | ~v3_ordinal1(A_38))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.80/1.63  tff(c_322, plain, (![A_90, B_91]: (~r4_wellord1(A_90, k2_wellord1(A_90, k1_wellord1(A_90, B_91))) | ~r2_hidden(B_91, k3_relat_1(A_90)) | ~v2_wellord1(A_90) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.80/1.63  tff(c_325, plain, (![B_40, A_38]: (~r4_wellord1(k1_wellord2(B_40), k2_wellord1(k1_wellord2(B_40), A_38)) | ~r2_hidden(A_38, k3_relat_1(k1_wellord2(B_40))) | ~v2_wellord1(k1_wellord2(B_40)) | ~v1_relat_1(k1_wellord2(B_40)) | ~r2_hidden(A_38, B_40) | ~v3_ordinal1(B_40) | ~v3_ordinal1(A_38))), inference(superposition, [status(thm), theory('equality')], [c_56, c_322])).
% 3.80/1.63  tff(c_457, plain, (![B_112, A_113]: (~r4_wellord1(k1_wellord2(B_112), k2_wellord1(k1_wellord2(B_112), A_113)) | ~v2_wellord1(k1_wellord2(B_112)) | ~r2_hidden(A_113, B_112) | ~v3_ordinal1(B_112) | ~v3_ordinal1(A_113))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_74, c_325])).
% 3.80/1.63  tff(c_838, plain, (![B_146, A_147]: (~r4_wellord1(k1_wellord2(B_146), k1_wellord2(A_147)) | ~v2_wellord1(k1_wellord2(B_146)) | ~r2_hidden(A_147, B_146) | ~v3_ordinal1(B_146) | ~v3_ordinal1(A_147) | ~r1_tarski(A_147, B_146))), inference(superposition, [status(thm), theory('equality')], [c_60, c_457])).
% 3.80/1.63  tff(c_841, plain, (~v2_wellord1(k1_wellord2('#skF_6')) | ~r2_hidden('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5') | ~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_123, c_838])).
% 3.80/1.63  tff(c_847, plain, (~v2_wellord1(k1_wellord2('#skF_6')) | ~r2_hidden('#skF_5', '#skF_6') | ~r1_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_841])).
% 3.80/1.63  tff(c_851, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_847])).
% 3.80/1.63  tff(c_854, plain, (~r1_ordinal1('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_6, c_851])).
% 3.80/1.63  tff(c_857, plain, (~r1_ordinal1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_854])).
% 3.80/1.63  tff(c_861, plain, (r1_ordinal1('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_2, c_857])).
% 3.80/1.63  tff(c_867, plain, (r1_ordinal1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_861])).
% 3.80/1.63  tff(c_844, plain, (~v2_wellord1(k1_wellord2('#skF_5')) | ~r2_hidden('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6') | ~r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_64, c_838])).
% 3.80/1.63  tff(c_850, plain, (~v2_wellord1(k1_wellord2('#skF_5')) | ~r2_hidden('#skF_6', '#skF_5') | ~r1_tarski('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_844])).
% 3.80/1.63  tff(c_925, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_850])).
% 3.80/1.63  tff(c_928, plain, (~r1_ordinal1('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_6, c_925])).
% 3.80/1.63  tff(c_932, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_867, c_928])).
% 3.80/1.63  tff(c_933, plain, (~r2_hidden('#skF_6', '#skF_5') | ~v2_wellord1(k1_wellord2('#skF_5'))), inference(splitRight, [status(thm)], [c_850])).
% 3.80/1.63  tff(c_949, plain, (~v2_wellord1(k1_wellord2('#skF_5'))), inference(splitLeft, [status(thm)], [c_933])).
% 3.80/1.63  tff(c_952, plain, (~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_949])).
% 3.80/1.63  tff(c_956, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_952])).
% 3.80/1.63  tff(c_957, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_933])).
% 3.80/1.63  tff(c_934, plain, (r1_tarski('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_850])).
% 3.80/1.63  tff(c_158, plain, (![B_70, A_71]: (r2_hidden(B_70, A_71) | B_70=A_71 | r2_hidden(A_71, B_70) | ~v3_ordinal1(B_70) | ~v3_ordinal1(A_71))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.80/1.63  tff(c_135, plain, (![A_64, C_65, B_66]: (r2_hidden(A_64, k3_relat_1(C_65)) | ~r2_hidden(A_64, k3_relat_1(k2_wellord1(C_65, B_66))) | ~v1_relat_1(C_65))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.80/1.63  tff(c_138, plain, (![A_64, B_43, A_42]: (r2_hidden(A_64, k3_relat_1(k1_wellord2(B_43))) | ~r2_hidden(A_64, k3_relat_1(k1_wellord2(A_42))) | ~v1_relat_1(k1_wellord2(B_43)) | ~r1_tarski(A_42, B_43))), inference(superposition, [status(thm), theory('equality')], [c_60, c_135])).
% 3.80/1.63  tff(c_140, plain, (![A_64, B_43, A_42]: (r2_hidden(A_64, B_43) | ~r2_hidden(A_64, A_42) | ~r1_tarski(A_42, B_43))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_74, c_74, c_138])).
% 3.80/1.63  tff(c_186, plain, (![A_71, B_43, B_70]: (r2_hidden(A_71, B_43) | ~r1_tarski(B_70, B_43) | r2_hidden(B_70, A_71) | B_70=A_71 | ~v3_ordinal1(B_70) | ~v3_ordinal1(A_71))), inference(resolution, [status(thm)], [c_158, c_140])).
% 3.80/1.63  tff(c_938, plain, (![A_71]: (r2_hidden(A_71, '#skF_5') | r2_hidden('#skF_6', A_71) | A_71='#skF_6' | ~v3_ordinal1('#skF_6') | ~v3_ordinal1(A_71))), inference(resolution, [status(thm)], [c_934, c_186])).
% 3.80/1.63  tff(c_945, plain, (![A_71]: (r2_hidden(A_71, '#skF_5') | r2_hidden('#skF_6', A_71) | A_71='#skF_6' | ~v3_ordinal1(A_71))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_938])).
% 3.80/1.63  tff(c_968, plain, (![A_149]: (r2_hidden(A_149, '#skF_5') | r2_hidden('#skF_6', A_149) | A_149='#skF_6' | ~v3_ordinal1(A_149))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_938])).
% 3.80/1.63  tff(c_208, plain, (![B_75, A_76]: (k1_wellord1(k1_wellord2(B_75), A_76)=A_76 | ~r2_hidden(A_76, B_75) | ~v3_ordinal1(B_75) | ~v3_ordinal1(A_76))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.80/1.63  tff(c_14, plain, (![D_19, A_8]: (~r2_hidden(D_19, k1_wellord1(A_8, D_19)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.80/1.63  tff(c_214, plain, (![A_76, B_75]: (~r2_hidden(A_76, A_76) | ~v1_relat_1(k1_wellord2(B_75)) | ~r2_hidden(A_76, B_75) | ~v3_ordinal1(B_75) | ~v3_ordinal1(A_76))), inference(superposition, [status(thm), theory('equality')], [c_208, c_14])).
% 3.80/1.63  tff(c_220, plain, (![A_76, B_75]: (~r2_hidden(A_76, A_76) | ~r2_hidden(A_76, B_75) | ~v3_ordinal1(B_75) | ~v3_ordinal1(A_76))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_214])).
% 3.80/1.63  tff(c_995, plain, (![B_75]: (~r2_hidden('#skF_5', B_75) | ~v3_ordinal1(B_75) | r2_hidden('#skF_6', '#skF_5') | '#skF_5'='#skF_6' | ~v3_ordinal1('#skF_5'))), inference(resolution, [status(thm)], [c_968, c_220])).
% 3.80/1.63  tff(c_1028, plain, (![B_75]: (~r2_hidden('#skF_5', B_75) | ~v3_ordinal1(B_75) | r2_hidden('#skF_6', '#skF_5') | '#skF_5'='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_995])).
% 3.80/1.63  tff(c_1082, plain, (![B_151]: (~r2_hidden('#skF_5', B_151) | ~v3_ordinal1(B_151))), inference(negUnitSimplification, [status(thm)], [c_62, c_957, c_1028])).
% 3.80/1.63  tff(c_1086, plain, (r2_hidden('#skF_6', '#skF_5') | '#skF_5'='#skF_6' | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_945, c_1082])).
% 3.80/1.63  tff(c_1109, plain, (r2_hidden('#skF_6', '#skF_5') | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1086])).
% 3.80/1.63  tff(c_1111, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_957, c_1109])).
% 3.80/1.63  tff(c_1112, plain, (~r2_hidden('#skF_5', '#skF_6') | ~v2_wellord1(k1_wellord2('#skF_6'))), inference(splitRight, [status(thm)], [c_847])).
% 3.80/1.63  tff(c_1326, plain, (~v2_wellord1(k1_wellord2('#skF_6'))), inference(splitLeft, [status(thm)], [c_1112])).
% 3.80/1.63  tff(c_1329, plain, (~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_1326])).
% 3.80/1.63  tff(c_1333, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_1329])).
% 3.80/1.63  tff(c_1334, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_1112])).
% 3.80/1.63  tff(c_1387, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_8, c_1334])).
% 3.80/1.63  tff(c_1400, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_1387])).
% 3.80/1.63  tff(c_1401, plain, (r2_hidden('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_1400])).
% 3.80/1.63  tff(c_1143, plain, (~v2_wellord1(k1_wellord2('#skF_6'))), inference(splitLeft, [status(thm)], [c_1112])).
% 3.80/1.63  tff(c_1146, plain, (~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_1143])).
% 3.80/1.63  tff(c_1150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_1146])).
% 3.80/1.63  tff(c_1151, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_1112])).
% 3.80/1.63  tff(c_1164, plain, (r2_hidden('#skF_6', '#skF_5') | '#skF_5'='#skF_6' | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_8, c_1151])).
% 3.80/1.63  tff(c_1178, plain, (r2_hidden('#skF_6', '#skF_5') | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_1164])).
% 3.80/1.63  tff(c_1179, plain, (r2_hidden('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_1178])).
% 3.80/1.63  tff(c_1133, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_850])).
% 3.80/1.63  tff(c_1136, plain, (~r1_ordinal1('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_6, c_1133])).
% 3.80/1.63  tff(c_1139, plain, (~r1_ordinal1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_1136])).
% 3.80/1.63  tff(c_372, plain, (![A_98, B_99, B_100]: (r2_hidden(A_98, B_99) | ~r1_tarski(B_100, B_99) | r2_hidden(B_100, A_98) | B_100=A_98 | ~v3_ordinal1(B_100) | ~v3_ordinal1(A_98))), inference(resolution, [status(thm)], [c_158, c_140])).
% 3.80/1.63  tff(c_589, plain, (![A_125, B_126, A_127]: (r2_hidden(A_125, B_126) | r2_hidden(A_127, A_125) | A_127=A_125 | ~v3_ordinal1(A_125) | ~r1_ordinal1(A_127, B_126) | ~v3_ordinal1(B_126) | ~v3_ordinal1(A_127))), inference(resolution, [status(thm)], [c_6, c_372])).
% 3.80/1.63  tff(c_597, plain, (![A_125, A_1, B_2]: (r2_hidden(A_125, A_1) | r2_hidden(B_2, A_125) | B_2=A_125 | ~v3_ordinal1(A_125) | r1_ordinal1(A_1, B_2) | ~v3_ordinal1(B_2) | ~v3_ordinal1(A_1))), inference(resolution, [status(thm)], [c_2, c_589])).
% 3.80/1.63  tff(c_1158, plain, (![A_1]: (r2_hidden('#skF_6', A_1) | '#skF_5'='#skF_6' | ~v3_ordinal1('#skF_6') | r1_ordinal1(A_1, '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1(A_1))), inference(resolution, [status(thm)], [c_597, c_1151])).
% 3.80/1.63  tff(c_1170, plain, (![A_1]: (r2_hidden('#skF_6', A_1) | '#skF_5'='#skF_6' | r1_ordinal1(A_1, '#skF_5') | ~v3_ordinal1(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_1158])).
% 3.80/1.63  tff(c_1232, plain, (![A_153]: (r2_hidden('#skF_6', A_153) | r1_ordinal1(A_153, '#skF_5') | ~v3_ordinal1(A_153))), inference(negUnitSimplification, [status(thm)], [c_62, c_1170])).
% 3.80/1.63  tff(c_1245, plain, (![B_75]: (~r2_hidden('#skF_6', B_75) | ~v3_ordinal1(B_75) | r1_ordinal1('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_6'))), inference(resolution, [status(thm)], [c_1232, c_220])).
% 3.80/1.63  tff(c_1267, plain, (![B_75]: (~r2_hidden('#skF_6', B_75) | ~v3_ordinal1(B_75) | r1_ordinal1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1245])).
% 3.80/1.63  tff(c_1273, plain, (![B_154]: (~r2_hidden('#skF_6', B_154) | ~v3_ordinal1(B_154))), inference(negUnitSimplification, [status(thm)], [c_1139, c_1267])).
% 3.80/1.63  tff(c_1279, plain, (~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_1179, c_1273])).
% 3.80/1.63  tff(c_1304, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_1279])).
% 3.80/1.63  tff(c_1305, plain, (~r2_hidden('#skF_6', '#skF_5') | ~v2_wellord1(k1_wellord2('#skF_5'))), inference(splitRight, [status(thm)], [c_850])).
% 3.80/1.63  tff(c_1416, plain, (~v2_wellord1(k1_wellord2('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1401, c_1305])).
% 3.80/1.63  tff(c_1419, plain, (~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_1416])).
% 3.80/1.63  tff(c_1423, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_1419])).
% 3.80/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.63  
% 3.80/1.63  Inference rules
% 3.80/1.63  ----------------------
% 3.80/1.63  #Ref     : 0
% 3.80/1.63  #Sup     : 256
% 3.80/1.63  #Fact    : 6
% 3.80/1.63  #Define  : 0
% 3.80/1.63  #Split   : 6
% 3.80/1.63  #Chain   : 0
% 3.80/1.63  #Close   : 0
% 3.80/1.63  
% 3.80/1.63  Ordering : KBO
% 3.80/1.63  
% 3.80/1.63  Simplification rules
% 3.80/1.63  ----------------------
% 3.80/1.63  #Subsume      : 6
% 3.80/1.63  #Demod        : 189
% 3.80/1.63  #Tautology    : 46
% 3.80/1.63  #SimpNegUnit  : 9
% 3.80/1.63  #BackRed      : 0
% 3.80/1.63  
% 3.80/1.63  #Partial instantiations: 0
% 3.80/1.63  #Strategies tried      : 1
% 3.80/1.63  
% 3.80/1.63  Timing (in seconds)
% 3.80/1.63  ----------------------
% 3.80/1.64  Preprocessing        : 0.34
% 3.80/1.64  Parsing              : 0.17
% 3.80/1.64  CNF conversion       : 0.03
% 3.80/1.64  Main loop            : 0.51
% 3.80/1.64  Inferencing          : 0.17
% 3.80/1.64  Reduction            : 0.14
% 3.80/1.64  Demodulation         : 0.10
% 3.80/1.64  BG Simplification    : 0.03
% 3.80/1.64  Subsumption          : 0.13
% 3.80/1.64  Abstraction          : 0.03
% 3.80/1.64  MUC search           : 0.00
% 3.80/1.64  Cooper               : 0.00
% 3.80/1.64  Total                : 0.89
% 3.80/1.64  Index Insertion      : 0.00
% 3.80/1.64  Index Deletion       : 0.00
% 3.80/1.64  Index Matching       : 0.00
% 3.80/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
