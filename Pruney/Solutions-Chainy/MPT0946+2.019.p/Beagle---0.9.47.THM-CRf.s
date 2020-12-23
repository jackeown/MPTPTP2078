%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:34 EST 2020

% Result     : Theorem 5.56s
% Output     : CNFRefutation 5.56s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 492 expanded)
%              Number of leaves         :   35 ( 188 expanded)
%              Depth                    :   16
%              Number of atoms          :  266 (1337 expanded)
%              Number of equality atoms :   19 ( 169 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

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

tff(f_147,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r4_wellord1(k1_wellord2(A),k1_wellord2(B))
             => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).

tff(f_48,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_133,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v2_wellord1(k1_wellord2(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_120,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_93,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
           => r4_wellord1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

tff(f_137,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

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

tff(f_57,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v2_wellord1(B)
       => k3_relat_1(k2_wellord1(B,k1_wellord1(B,A))) = k1_wellord1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_wellord1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k3_relat_1(k2_wellord1(C,B)))
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_wellord1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k1_wellord1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( D != B
                & r2_hidden(k4_tarski(D,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

tff(c_70,plain,(
    v3_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_64,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_68,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_6,plain,(
    ! [B_5,A_3] :
      ( r2_hidden(B_5,A_3)
      | B_5 = A_3
      | r2_hidden(A_3,B_5)
      | ~ v3_ordinal1(B_5)
      | ~ v3_ordinal1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_60,plain,(
    ! [A_44] :
      ( v2_wellord1(k1_wellord2(A_44))
      | ~ v3_ordinal1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r1_ordinal1(A_1,B_2)
      | ~ v3_ordinal1(B_2)
      | ~ v3_ordinal1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_56,plain,(
    ! [A_40] : v1_relat_1(k1_wellord2(A_40)) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_66,plain,(
    r4_wellord1(k1_wellord2('#skF_5'),k1_wellord2('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_98,plain,(
    ! [B_55,A_56] :
      ( r4_wellord1(B_55,A_56)
      | ~ r4_wellord1(A_56,B_55)
      | ~ v1_relat_1(B_55)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_100,plain,
    ( r4_wellord1(k1_wellord2('#skF_6'),k1_wellord2('#skF_5'))
    | ~ v1_relat_1(k1_wellord2('#skF_6'))
    | ~ v1_relat_1(k1_wellord2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_66,c_98])).

tff(c_103,plain,(
    r4_wellord1(k1_wellord2('#skF_6'),k1_wellord2('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_56,c_100])).

tff(c_62,plain,(
    ! [B_46,A_45] :
      ( k2_wellord1(k1_wellord2(B_46),A_45) = k1_wellord2(A_45)
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_50,plain,(
    ! [A_32] :
      ( k3_relat_1(k1_wellord2(A_32)) = A_32
      | ~ v1_relat_1(k1_wellord2(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_76,plain,(
    ! [A_32] : k3_relat_1(k1_wellord2(A_32)) = A_32 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_50])).

tff(c_58,plain,(
    ! [B_43,A_41] :
      ( k1_wellord1(k1_wellord2(B_43),A_41) = A_41
      | ~ r2_hidden(A_41,B_43)
      | ~ v3_ordinal1(B_43)
      | ~ v3_ordinal1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_411,plain,(
    ! [A_104,B_105] :
      ( ~ r4_wellord1(A_104,k2_wellord1(A_104,k1_wellord1(A_104,B_105)))
      | ~ r2_hidden(B_105,k3_relat_1(A_104))
      | ~ v2_wellord1(A_104)
      | ~ v1_relat_1(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_414,plain,(
    ! [B_43,A_41] :
      ( ~ r4_wellord1(k1_wellord2(B_43),k2_wellord1(k1_wellord2(B_43),A_41))
      | ~ r2_hidden(A_41,k3_relat_1(k1_wellord2(B_43)))
      | ~ v2_wellord1(k1_wellord2(B_43))
      | ~ v1_relat_1(k1_wellord2(B_43))
      | ~ r2_hidden(A_41,B_43)
      | ~ v3_ordinal1(B_43)
      | ~ v3_ordinal1(A_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_411])).

tff(c_736,plain,(
    ! [B_141,A_142] :
      ( ~ r4_wellord1(k1_wellord2(B_141),k2_wellord1(k1_wellord2(B_141),A_142))
      | ~ v2_wellord1(k1_wellord2(B_141))
      | ~ r2_hidden(A_142,B_141)
      | ~ v3_ordinal1(B_141)
      | ~ v3_ordinal1(A_142) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_76,c_414])).

tff(c_917,plain,(
    ! [B_165,A_166] :
      ( ~ r4_wellord1(k1_wellord2(B_165),k1_wellord2(A_166))
      | ~ v2_wellord1(k1_wellord2(B_165))
      | ~ r2_hidden(A_166,B_165)
      | ~ v3_ordinal1(B_165)
      | ~ v3_ordinal1(A_166)
      | ~ r1_tarski(A_166,B_165) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_736])).

tff(c_920,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_6'))
    | ~ r2_hidden('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5')
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_103,c_917])).

tff(c_926,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_6'))
    | ~ r2_hidden('#skF_5','#skF_6')
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_920])).

tff(c_930,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_926])).

tff(c_933,plain,
    ( ~ r1_ordinal1('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_930])).

tff(c_936,plain,(
    ~ r1_ordinal1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_933])).

tff(c_8,plain,(
    ! [B_8,A_6] :
      ( r2_hidden(B_8,A_6)
      | r1_ordinal1(A_6,B_8)
      | ~ v3_ordinal1(B_8)
      | ~ v3_ordinal1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_923,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_5'))
    | ~ r2_hidden('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6')
    | ~ r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_917])).

tff(c_929,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_5'))
    | ~ r2_hidden('#skF_6','#skF_5')
    | ~ r1_tarski('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_923])).

tff(c_937,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_929])).

tff(c_940,plain,
    ( ~ r1_ordinal1('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_937])).

tff(c_943,plain,(
    ~ r1_ordinal1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_940])).

tff(c_309,plain,(
    ! [B_88,A_89] :
      ( k3_relat_1(k2_wellord1(B_88,k1_wellord1(B_88,A_89))) = k1_wellord1(B_88,A_89)
      | ~ v2_wellord1(B_88)
      | ~ v1_relat_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_30,plain,(
    ! [A_21,C_23,B_22] :
      ( r2_hidden(A_21,k3_relat_1(C_23))
      | ~ r2_hidden(A_21,k3_relat_1(k2_wellord1(C_23,B_22)))
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_423,plain,(
    ! [A_106,B_107,A_108] :
      ( r2_hidden(A_106,k3_relat_1(B_107))
      | ~ r2_hidden(A_106,k1_wellord1(B_107,A_108))
      | ~ v1_relat_1(B_107)
      | ~ v2_wellord1(B_107)
      | ~ v1_relat_1(B_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_309,c_30])).

tff(c_438,plain,(
    ! [A_106,B_43,A_41] :
      ( r2_hidden(A_106,k3_relat_1(k1_wellord2(B_43)))
      | ~ r2_hidden(A_106,A_41)
      | ~ v1_relat_1(k1_wellord2(B_43))
      | ~ v2_wellord1(k1_wellord2(B_43))
      | ~ v1_relat_1(k1_wellord2(B_43))
      | ~ r2_hidden(A_41,B_43)
      | ~ v3_ordinal1(B_43)
      | ~ v3_ordinal1(A_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_423])).

tff(c_528,plain,(
    ! [A_128,B_129,A_130] :
      ( r2_hidden(A_128,B_129)
      | ~ r2_hidden(A_128,A_130)
      | ~ v2_wellord1(k1_wellord2(B_129))
      | ~ r2_hidden(A_130,B_129)
      | ~ v3_ordinal1(B_129)
      | ~ v3_ordinal1(A_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_56,c_76,c_438])).

tff(c_949,plain,(
    ! [B_171,B_172,A_173] :
      ( r2_hidden(B_171,B_172)
      | ~ v2_wellord1(k1_wellord2(B_172))
      | ~ r2_hidden(A_173,B_172)
      | ~ v3_ordinal1(B_172)
      | r1_ordinal1(A_173,B_171)
      | ~ v3_ordinal1(B_171)
      | ~ v3_ordinal1(A_173) ) ),
    inference(resolution,[status(thm)],[c_8,c_528])).

tff(c_1002,plain,(
    ! [B_175,A_176,A_177] :
      ( r2_hidden(B_175,A_176)
      | ~ r2_hidden(A_177,A_176)
      | r1_ordinal1(A_177,B_175)
      | ~ v3_ordinal1(B_175)
      | ~ v3_ordinal1(A_177)
      | ~ v3_ordinal1(A_176) ) ),
    inference(resolution,[status(thm)],[c_60,c_949])).

tff(c_1044,plain,(
    ! [B_178,A_179,B_180] :
      ( r2_hidden(B_178,A_179)
      | r1_ordinal1(B_180,B_178)
      | ~ v3_ordinal1(B_178)
      | r1_ordinal1(A_179,B_180)
      | ~ v3_ordinal1(B_180)
      | ~ v3_ordinal1(A_179) ) ),
    inference(resolution,[status(thm)],[c_8,c_1002])).

tff(c_147,plain,(
    ! [B_72,A_73] :
      ( k1_wellord1(k1_wellord2(B_72),A_73) = A_73
      | ~ r2_hidden(A_73,B_72)
      | ~ v3_ordinal1(B_72)
      | ~ v3_ordinal1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_14,plain,(
    ! [D_20,A_9] :
      ( ~ r2_hidden(D_20,k1_wellord1(A_9,D_20))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_153,plain,(
    ! [A_73,B_72] :
      ( ~ r2_hidden(A_73,A_73)
      | ~ v1_relat_1(k1_wellord2(B_72))
      | ~ r2_hidden(A_73,B_72)
      | ~ v3_ordinal1(B_72)
      | ~ v3_ordinal1(A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_14])).

tff(c_159,plain,(
    ! [A_73,B_72] :
      ( ~ r2_hidden(A_73,A_73)
      | ~ r2_hidden(A_73,B_72)
      | ~ v3_ordinal1(B_72)
      | ~ v3_ordinal1(A_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_153])).

tff(c_1132,plain,(
    ! [A_181,B_182,B_183] :
      ( ~ r2_hidden(A_181,B_182)
      | ~ v3_ordinal1(B_182)
      | r1_ordinal1(B_183,A_181)
      | r1_ordinal1(A_181,B_183)
      | ~ v3_ordinal1(B_183)
      | ~ v3_ordinal1(A_181) ) ),
    inference(resolution,[status(thm)],[c_1044,c_159])).

tff(c_1281,plain,(
    ! [B_185,B_186,A_187] :
      ( r1_ordinal1(B_185,B_186)
      | r1_ordinal1(B_186,B_185)
      | ~ v3_ordinal1(B_185)
      | r1_ordinal1(A_187,B_186)
      | ~ v3_ordinal1(B_186)
      | ~ v3_ordinal1(A_187) ) ),
    inference(resolution,[status(thm)],[c_8,c_1132])).

tff(c_1285,plain,(
    ! [A_187] :
      ( r1_ordinal1('#skF_6','#skF_5')
      | ~ v3_ordinal1('#skF_5')
      | r1_ordinal1(A_187,'#skF_6')
      | ~ v3_ordinal1('#skF_6')
      | ~ v3_ordinal1(A_187) ) ),
    inference(resolution,[status(thm)],[c_1281,c_936])).

tff(c_1308,plain,(
    ! [A_187] :
      ( r1_ordinal1('#skF_6','#skF_5')
      | r1_ordinal1(A_187,'#skF_6')
      | ~ v3_ordinal1(A_187) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_1285])).

tff(c_1323,plain,(
    ! [A_188] :
      ( r1_ordinal1(A_188,'#skF_6')
      | ~ v3_ordinal1(A_188) ) ),
    inference(negUnitSimplification,[status(thm)],[c_943,c_1308])).

tff(c_1326,plain,(
    ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1323,c_936])).

tff(c_1334,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1326])).

tff(c_1335,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | ~ v2_wellord1(k1_wellord2('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_929])).

tff(c_1415,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1335])).

tff(c_1418,plain,(
    ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_1415])).

tff(c_1422,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1418])).

tff(c_1423,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_1335])).

tff(c_1429,plain,
    ( r1_ordinal1('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_1423])).

tff(c_1432,plain,(
    r1_ordinal1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1429])).

tff(c_1434,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_936,c_1432])).

tff(c_1435,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | ~ v2_wellord1(k1_wellord2('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_926])).

tff(c_1466,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1435])).

tff(c_1469,plain,(
    ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_1466])).

tff(c_1473,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1469])).

tff(c_1474,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_1435])).

tff(c_1481,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | '#skF_5' = '#skF_6'
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_1474])).

tff(c_1491,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1481])).

tff(c_1492,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1491])).

tff(c_1436,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_926])).

tff(c_132,plain,(
    ! [A_66,C_67,B_68] :
      ( r2_hidden(A_66,k3_relat_1(C_67))
      | ~ r2_hidden(A_66,k3_relat_1(k2_wellord1(C_67,B_68)))
      | ~ v1_relat_1(C_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_139,plain,(
    ! [A_66,B_46,A_45] :
      ( r2_hidden(A_66,k3_relat_1(k1_wellord2(B_46)))
      | ~ r2_hidden(A_66,k3_relat_1(k1_wellord2(A_45)))
      | ~ v1_relat_1(k1_wellord2(B_46))
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_132])).

tff(c_142,plain,(
    ! [A_66,B_46,A_45] :
      ( r2_hidden(A_66,B_46)
      | ~ r2_hidden(A_66,A_45)
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_76,c_76,c_139])).

tff(c_1554,plain,(
    ! [B_191] :
      ( r2_hidden('#skF_6',B_191)
      | ~ r1_tarski('#skF_5',B_191) ) ),
    inference(resolution,[status(thm)],[c_1492,c_142])).

tff(c_1571,plain,(
    ! [B_72] :
      ( ~ r2_hidden('#skF_6',B_72)
      | ~ v3_ordinal1(B_72)
      | ~ v3_ordinal1('#skF_6')
      | ~ r1_tarski('#skF_5','#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1554,c_159])).

tff(c_1607,plain,(
    ! [B_192] :
      ( ~ r2_hidden('#skF_6',B_192)
      | ~ v3_ordinal1(B_192) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1436,c_68,c_1571])).

tff(c_1613,plain,(
    ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1492,c_1607])).

tff(c_1634,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1613])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:55:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.56/2.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.56/2.44  
% 5.56/2.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.56/2.45  %$ r4_wellord1 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 5.56/2.45  
% 5.56/2.45  %Foreground sorts:
% 5.56/2.45  
% 5.56/2.45  
% 5.56/2.45  %Background operators:
% 5.56/2.45  
% 5.56/2.45  
% 5.56/2.45  %Foreground operators:
% 5.56/2.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.56/2.45  tff(r4_wellord1, type, r4_wellord1: ($i * $i) > $o).
% 5.56/2.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.56/2.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.56/2.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 5.56/2.45  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 5.56/2.45  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.56/2.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.56/2.45  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 5.56/2.45  tff('#skF_5', type, '#skF_5': $i).
% 5.56/2.45  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 5.56/2.45  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 5.56/2.45  tff('#skF_6', type, '#skF_6': $i).
% 5.56/2.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.56/2.45  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 5.56/2.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.56/2.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.56/2.45  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 5.56/2.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.56/2.45  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 5.56/2.45  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.56/2.45  
% 5.56/2.48  tff(f_147, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r4_wellord1(k1_wellord2(A), k1_wellord2(B)) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_wellord2)).
% 5.56/2.48  tff(f_48, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 5.56/2.48  tff(f_133, axiom, (![A]: (v3_ordinal1(A) => v2_wellord1(k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_wellord2)).
% 5.56/2.48  tff(f_33, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 5.56/2.48  tff(f_120, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 5.56/2.48  tff(f_93, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r4_wellord1(A, B) => r4_wellord1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_wellord1)).
% 5.56/2.48  tff(f_137, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_wellord2)).
% 5.56/2.48  tff(f_118, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 5.56/2.48  tff(f_129, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) => (A = k1_wellord1(k1_wellord2(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_wellord2)).
% 5.56/2.48  tff(f_103, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) => (![B]: ~(r2_hidden(B, k3_relat_1(A)) & r4_wellord1(A, k2_wellord1(A, k1_wellord1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_wellord1)).
% 5.56/2.48  tff(f_57, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_ordinal1)).
% 5.56/2.48  tff(f_84, axiom, (![A, B]: (v1_relat_1(B) => (v2_wellord1(B) => (k3_relat_1(k2_wellord1(B, k1_wellord1(B, A))) = k1_wellord1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_wellord1)).
% 5.56/2.48  tff(f_78, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k3_relat_1(k2_wellord1(C, B))) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_wellord1)).
% 5.56/2.48  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k1_wellord1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (~(D = B) & r2_hidden(k4_tarski(D, B), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord1)).
% 5.56/2.48  tff(c_70, plain, (v3_ordinal1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.56/2.48  tff(c_64, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.56/2.48  tff(c_68, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.56/2.48  tff(c_6, plain, (![B_5, A_3]: (r2_hidden(B_5, A_3) | B_5=A_3 | r2_hidden(A_3, B_5) | ~v3_ordinal1(B_5) | ~v3_ordinal1(A_3))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.56/2.48  tff(c_60, plain, (![A_44]: (v2_wellord1(k1_wellord2(A_44)) | ~v3_ordinal1(A_44))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.56/2.48  tff(c_4, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r1_ordinal1(A_1, B_2) | ~v3_ordinal1(B_2) | ~v3_ordinal1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.56/2.48  tff(c_56, plain, (![A_40]: (v1_relat_1(k1_wellord2(A_40)))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.56/2.48  tff(c_66, plain, (r4_wellord1(k1_wellord2('#skF_5'), k1_wellord2('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.56/2.48  tff(c_98, plain, (![B_55, A_56]: (r4_wellord1(B_55, A_56) | ~r4_wellord1(A_56, B_55) | ~v1_relat_1(B_55) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.56/2.48  tff(c_100, plain, (r4_wellord1(k1_wellord2('#skF_6'), k1_wellord2('#skF_5')) | ~v1_relat_1(k1_wellord2('#skF_6')) | ~v1_relat_1(k1_wellord2('#skF_5'))), inference(resolution, [status(thm)], [c_66, c_98])).
% 5.56/2.48  tff(c_103, plain, (r4_wellord1(k1_wellord2('#skF_6'), k1_wellord2('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_56, c_100])).
% 5.56/2.48  tff(c_62, plain, (![B_46, A_45]: (k2_wellord1(k1_wellord2(B_46), A_45)=k1_wellord2(A_45) | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_137])).
% 5.56/2.48  tff(c_50, plain, (![A_32]: (k3_relat_1(k1_wellord2(A_32))=A_32 | ~v1_relat_1(k1_wellord2(A_32)))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.56/2.48  tff(c_76, plain, (![A_32]: (k3_relat_1(k1_wellord2(A_32))=A_32)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_50])).
% 5.56/2.48  tff(c_58, plain, (![B_43, A_41]: (k1_wellord1(k1_wellord2(B_43), A_41)=A_41 | ~r2_hidden(A_41, B_43) | ~v3_ordinal1(B_43) | ~v3_ordinal1(A_41))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.56/2.48  tff(c_411, plain, (![A_104, B_105]: (~r4_wellord1(A_104, k2_wellord1(A_104, k1_wellord1(A_104, B_105))) | ~r2_hidden(B_105, k3_relat_1(A_104)) | ~v2_wellord1(A_104) | ~v1_relat_1(A_104))), inference(cnfTransformation, [status(thm)], [f_103])).
% 5.56/2.48  tff(c_414, plain, (![B_43, A_41]: (~r4_wellord1(k1_wellord2(B_43), k2_wellord1(k1_wellord2(B_43), A_41)) | ~r2_hidden(A_41, k3_relat_1(k1_wellord2(B_43))) | ~v2_wellord1(k1_wellord2(B_43)) | ~v1_relat_1(k1_wellord2(B_43)) | ~r2_hidden(A_41, B_43) | ~v3_ordinal1(B_43) | ~v3_ordinal1(A_41))), inference(superposition, [status(thm), theory('equality')], [c_58, c_411])).
% 5.56/2.48  tff(c_736, plain, (![B_141, A_142]: (~r4_wellord1(k1_wellord2(B_141), k2_wellord1(k1_wellord2(B_141), A_142)) | ~v2_wellord1(k1_wellord2(B_141)) | ~r2_hidden(A_142, B_141) | ~v3_ordinal1(B_141) | ~v3_ordinal1(A_142))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_76, c_414])).
% 5.56/2.48  tff(c_917, plain, (![B_165, A_166]: (~r4_wellord1(k1_wellord2(B_165), k1_wellord2(A_166)) | ~v2_wellord1(k1_wellord2(B_165)) | ~r2_hidden(A_166, B_165) | ~v3_ordinal1(B_165) | ~v3_ordinal1(A_166) | ~r1_tarski(A_166, B_165))), inference(superposition, [status(thm), theory('equality')], [c_62, c_736])).
% 5.56/2.48  tff(c_920, plain, (~v2_wellord1(k1_wellord2('#skF_6')) | ~r2_hidden('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5') | ~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_103, c_917])).
% 5.56/2.48  tff(c_926, plain, (~v2_wellord1(k1_wellord2('#skF_6')) | ~r2_hidden('#skF_5', '#skF_6') | ~r1_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_920])).
% 5.56/2.48  tff(c_930, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_926])).
% 5.56/2.48  tff(c_933, plain, (~r1_ordinal1('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_4, c_930])).
% 5.56/2.48  tff(c_936, plain, (~r1_ordinal1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_933])).
% 5.56/2.48  tff(c_8, plain, (![B_8, A_6]: (r2_hidden(B_8, A_6) | r1_ordinal1(A_6, B_8) | ~v3_ordinal1(B_8) | ~v3_ordinal1(A_6))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.56/2.48  tff(c_923, plain, (~v2_wellord1(k1_wellord2('#skF_5')) | ~r2_hidden('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6') | ~r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_66, c_917])).
% 5.56/2.48  tff(c_929, plain, (~v2_wellord1(k1_wellord2('#skF_5')) | ~r2_hidden('#skF_6', '#skF_5') | ~r1_tarski('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_70, c_923])).
% 5.56/2.48  tff(c_937, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_929])).
% 5.56/2.48  tff(c_940, plain, (~r1_ordinal1('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_4, c_937])).
% 5.56/2.48  tff(c_943, plain, (~r1_ordinal1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_70, c_940])).
% 5.56/2.48  tff(c_309, plain, (![B_88, A_89]: (k3_relat_1(k2_wellord1(B_88, k1_wellord1(B_88, A_89)))=k1_wellord1(B_88, A_89) | ~v2_wellord1(B_88) | ~v1_relat_1(B_88))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.56/2.48  tff(c_30, plain, (![A_21, C_23, B_22]: (r2_hidden(A_21, k3_relat_1(C_23)) | ~r2_hidden(A_21, k3_relat_1(k2_wellord1(C_23, B_22))) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.56/2.48  tff(c_423, plain, (![A_106, B_107, A_108]: (r2_hidden(A_106, k3_relat_1(B_107)) | ~r2_hidden(A_106, k1_wellord1(B_107, A_108)) | ~v1_relat_1(B_107) | ~v2_wellord1(B_107) | ~v1_relat_1(B_107))), inference(superposition, [status(thm), theory('equality')], [c_309, c_30])).
% 5.56/2.48  tff(c_438, plain, (![A_106, B_43, A_41]: (r2_hidden(A_106, k3_relat_1(k1_wellord2(B_43))) | ~r2_hidden(A_106, A_41) | ~v1_relat_1(k1_wellord2(B_43)) | ~v2_wellord1(k1_wellord2(B_43)) | ~v1_relat_1(k1_wellord2(B_43)) | ~r2_hidden(A_41, B_43) | ~v3_ordinal1(B_43) | ~v3_ordinal1(A_41))), inference(superposition, [status(thm), theory('equality')], [c_58, c_423])).
% 5.56/2.48  tff(c_528, plain, (![A_128, B_129, A_130]: (r2_hidden(A_128, B_129) | ~r2_hidden(A_128, A_130) | ~v2_wellord1(k1_wellord2(B_129)) | ~r2_hidden(A_130, B_129) | ~v3_ordinal1(B_129) | ~v3_ordinal1(A_130))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_56, c_76, c_438])).
% 5.56/2.48  tff(c_949, plain, (![B_171, B_172, A_173]: (r2_hidden(B_171, B_172) | ~v2_wellord1(k1_wellord2(B_172)) | ~r2_hidden(A_173, B_172) | ~v3_ordinal1(B_172) | r1_ordinal1(A_173, B_171) | ~v3_ordinal1(B_171) | ~v3_ordinal1(A_173))), inference(resolution, [status(thm)], [c_8, c_528])).
% 5.56/2.48  tff(c_1002, plain, (![B_175, A_176, A_177]: (r2_hidden(B_175, A_176) | ~r2_hidden(A_177, A_176) | r1_ordinal1(A_177, B_175) | ~v3_ordinal1(B_175) | ~v3_ordinal1(A_177) | ~v3_ordinal1(A_176))), inference(resolution, [status(thm)], [c_60, c_949])).
% 5.56/2.48  tff(c_1044, plain, (![B_178, A_179, B_180]: (r2_hidden(B_178, A_179) | r1_ordinal1(B_180, B_178) | ~v3_ordinal1(B_178) | r1_ordinal1(A_179, B_180) | ~v3_ordinal1(B_180) | ~v3_ordinal1(A_179))), inference(resolution, [status(thm)], [c_8, c_1002])).
% 5.56/2.48  tff(c_147, plain, (![B_72, A_73]: (k1_wellord1(k1_wellord2(B_72), A_73)=A_73 | ~r2_hidden(A_73, B_72) | ~v3_ordinal1(B_72) | ~v3_ordinal1(A_73))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.56/2.48  tff(c_14, plain, (![D_20, A_9]: (~r2_hidden(D_20, k1_wellord1(A_9, D_20)) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.56/2.48  tff(c_153, plain, (![A_73, B_72]: (~r2_hidden(A_73, A_73) | ~v1_relat_1(k1_wellord2(B_72)) | ~r2_hidden(A_73, B_72) | ~v3_ordinal1(B_72) | ~v3_ordinal1(A_73))), inference(superposition, [status(thm), theory('equality')], [c_147, c_14])).
% 5.56/2.48  tff(c_159, plain, (![A_73, B_72]: (~r2_hidden(A_73, A_73) | ~r2_hidden(A_73, B_72) | ~v3_ordinal1(B_72) | ~v3_ordinal1(A_73))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_153])).
% 5.56/2.48  tff(c_1132, plain, (![A_181, B_182, B_183]: (~r2_hidden(A_181, B_182) | ~v3_ordinal1(B_182) | r1_ordinal1(B_183, A_181) | r1_ordinal1(A_181, B_183) | ~v3_ordinal1(B_183) | ~v3_ordinal1(A_181))), inference(resolution, [status(thm)], [c_1044, c_159])).
% 5.56/2.48  tff(c_1281, plain, (![B_185, B_186, A_187]: (r1_ordinal1(B_185, B_186) | r1_ordinal1(B_186, B_185) | ~v3_ordinal1(B_185) | r1_ordinal1(A_187, B_186) | ~v3_ordinal1(B_186) | ~v3_ordinal1(A_187))), inference(resolution, [status(thm)], [c_8, c_1132])).
% 5.56/2.48  tff(c_1285, plain, (![A_187]: (r1_ordinal1('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | r1_ordinal1(A_187, '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1(A_187))), inference(resolution, [status(thm)], [c_1281, c_936])).
% 5.56/2.48  tff(c_1308, plain, (![A_187]: (r1_ordinal1('#skF_6', '#skF_5') | r1_ordinal1(A_187, '#skF_6') | ~v3_ordinal1(A_187))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_70, c_1285])).
% 5.56/2.48  tff(c_1323, plain, (![A_188]: (r1_ordinal1(A_188, '#skF_6') | ~v3_ordinal1(A_188))), inference(negUnitSimplification, [status(thm)], [c_943, c_1308])).
% 5.56/2.48  tff(c_1326, plain, (~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_1323, c_936])).
% 5.56/2.48  tff(c_1334, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_1326])).
% 5.56/2.48  tff(c_1335, plain, (~r2_hidden('#skF_6', '#skF_5') | ~v2_wellord1(k1_wellord2('#skF_5'))), inference(splitRight, [status(thm)], [c_929])).
% 5.56/2.48  tff(c_1415, plain, (~v2_wellord1(k1_wellord2('#skF_5'))), inference(splitLeft, [status(thm)], [c_1335])).
% 5.56/2.48  tff(c_1418, plain, (~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_1415])).
% 5.56/2.48  tff(c_1422, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_1418])).
% 5.56/2.48  tff(c_1423, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_1335])).
% 5.56/2.48  tff(c_1429, plain, (r1_ordinal1('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_8, c_1423])).
% 5.56/2.48  tff(c_1432, plain, (r1_ordinal1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1429])).
% 5.56/2.48  tff(c_1434, plain, $false, inference(negUnitSimplification, [status(thm)], [c_936, c_1432])).
% 5.56/2.48  tff(c_1435, plain, (~r2_hidden('#skF_5', '#skF_6') | ~v2_wellord1(k1_wellord2('#skF_6'))), inference(splitRight, [status(thm)], [c_926])).
% 5.56/2.48  tff(c_1466, plain, (~v2_wellord1(k1_wellord2('#skF_6'))), inference(splitLeft, [status(thm)], [c_1435])).
% 5.56/2.48  tff(c_1469, plain, (~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_60, c_1466])).
% 5.56/2.48  tff(c_1473, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_1469])).
% 5.56/2.48  tff(c_1474, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_1435])).
% 5.56/2.48  tff(c_1481, plain, (r2_hidden('#skF_6', '#skF_5') | '#skF_5'='#skF_6' | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_6, c_1474])).
% 5.56/2.48  tff(c_1491, plain, (r2_hidden('#skF_6', '#skF_5') | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1481])).
% 5.56/2.48  tff(c_1492, plain, (r2_hidden('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_64, c_1491])).
% 5.56/2.48  tff(c_1436, plain, (r1_tarski('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_926])).
% 5.56/2.48  tff(c_132, plain, (![A_66, C_67, B_68]: (r2_hidden(A_66, k3_relat_1(C_67)) | ~r2_hidden(A_66, k3_relat_1(k2_wellord1(C_67, B_68))) | ~v1_relat_1(C_67))), inference(cnfTransformation, [status(thm)], [f_78])).
% 5.56/2.48  tff(c_139, plain, (![A_66, B_46, A_45]: (r2_hidden(A_66, k3_relat_1(k1_wellord2(B_46))) | ~r2_hidden(A_66, k3_relat_1(k1_wellord2(A_45))) | ~v1_relat_1(k1_wellord2(B_46)) | ~r1_tarski(A_45, B_46))), inference(superposition, [status(thm), theory('equality')], [c_62, c_132])).
% 5.56/2.48  tff(c_142, plain, (![A_66, B_46, A_45]: (r2_hidden(A_66, B_46) | ~r2_hidden(A_66, A_45) | ~r1_tarski(A_45, B_46))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_76, c_76, c_139])).
% 5.56/2.48  tff(c_1554, plain, (![B_191]: (r2_hidden('#skF_6', B_191) | ~r1_tarski('#skF_5', B_191))), inference(resolution, [status(thm)], [c_1492, c_142])).
% 5.56/2.48  tff(c_1571, plain, (![B_72]: (~r2_hidden('#skF_6', B_72) | ~v3_ordinal1(B_72) | ~v3_ordinal1('#skF_6') | ~r1_tarski('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_1554, c_159])).
% 5.56/2.48  tff(c_1607, plain, (![B_192]: (~r2_hidden('#skF_6', B_192) | ~v3_ordinal1(B_192))), inference(demodulation, [status(thm), theory('equality')], [c_1436, c_68, c_1571])).
% 5.56/2.48  tff(c_1613, plain, (~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_1492, c_1607])).
% 5.56/2.48  tff(c_1634, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_1613])).
% 5.56/2.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.56/2.48  
% 5.56/2.48  Inference rules
% 5.56/2.48  ----------------------
% 5.56/2.48  #Ref     : 0
% 5.56/2.48  #Sup     : 321
% 5.56/2.48  #Fact    : 10
% 5.56/2.48  #Define  : 0
% 5.56/2.48  #Split   : 4
% 5.56/2.48  #Chain   : 0
% 5.56/2.48  #Close   : 0
% 5.56/2.48  
% 5.56/2.48  Ordering : KBO
% 5.56/2.48  
% 5.56/2.48  Simplification rules
% 5.56/2.48  ----------------------
% 5.56/2.48  #Subsume      : 16
% 5.56/2.48  #Demod        : 183
% 5.56/2.48  #Tautology    : 46
% 5.56/2.48  #SimpNegUnit  : 5
% 5.56/2.48  #BackRed      : 0
% 5.56/2.48  
% 5.56/2.48  #Partial instantiations: 0
% 5.56/2.48  #Strategies tried      : 1
% 5.56/2.48  
% 5.56/2.48  Timing (in seconds)
% 5.56/2.48  ----------------------
% 5.56/2.48  Preprocessing        : 0.56
% 5.56/2.48  Parsing              : 0.28
% 5.56/2.48  CNF conversion       : 0.05
% 5.56/2.49  Main loop            : 0.97
% 5.56/2.49  Inferencing          : 0.32
% 5.56/2.49  Reduction            : 0.27
% 5.56/2.49  Demodulation         : 0.19
% 5.56/2.49  BG Simplification    : 0.06
% 5.56/2.49  Subsumption          : 0.24
% 5.56/2.49  Abstraction          : 0.05
% 5.56/2.49  MUC search           : 0.00
% 5.56/2.49  Cooper               : 0.00
% 5.56/2.49  Total                : 1.60
% 5.56/2.49  Index Insertion      : 0.00
% 5.56/2.49  Index Deletion       : 0.00
% 5.56/2.49  Index Matching       : 0.00
% 5.56/2.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
