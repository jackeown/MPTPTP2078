%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:34 EST 2020

% Result     : Theorem 4.71s
% Output     : CNFRefutation 4.71s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 437 expanded)
%              Number of leaves         :   34 ( 168 expanded)
%              Depth                    :   14
%              Number of atoms          :  241 (1194 expanded)
%              Number of equality atoms :   17 ( 147 expanded)
%              Maximal formula depth    :   10 (   4 average)
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

tff(f_141,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r4_wellord1(k1_wellord2(A),k1_wellord2(B))
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).

tff(f_127,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v2_wellord1(k1_wellord2(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).

tff(f_56,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_114,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
           => r4_wellord1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

tff(f_131,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_112,axiom,(
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

tff(f_123,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
           => A = k1_wellord1(k1_wellord2(B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
       => ! [B] :
            ~ ( r2_hidden(B,k3_relat_1(A))
              & r4_wellord1(A,k2_wellord1(A,k1_wellord1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).

tff(f_65,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_78,axiom,(
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

tff(c_68,plain,(
    v3_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_58,plain,(
    ! [A_42] :
      ( v2_wellord1(k1_wellord2(A_42))
      | ~ v3_ordinal1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_62,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_66,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_10,plain,(
    ! [B_8,A_6] :
      ( r2_hidden(B_8,A_6)
      | B_8 = A_6
      | r2_hidden(A_6,B_8)
      | ~ v3_ordinal1(B_8)
      | ~ v3_ordinal1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ r1_ordinal1(A_4,B_5)
      | ~ v3_ordinal1(B_5)
      | ~ v3_ordinal1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_54,plain,(
    ! [A_38] : v1_relat_1(k1_wellord2(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_64,plain,(
    r4_wellord1(k1_wellord2('#skF_5'),k1_wellord2('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_102,plain,(
    ! [B_57,A_58] :
      ( r4_wellord1(B_57,A_58)
      | ~ r4_wellord1(A_58,B_57)
      | ~ v1_relat_1(B_57)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_104,plain,
    ( r4_wellord1(k1_wellord2('#skF_6'),k1_wellord2('#skF_5'))
    | ~ v1_relat_1(k1_wellord2('#skF_6'))
    | ~ v1_relat_1(k1_wellord2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_64,c_102])).

tff(c_107,plain,(
    r4_wellord1(k1_wellord2('#skF_6'),k1_wellord2('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_104])).

tff(c_60,plain,(
    ! [B_44,A_43] :
      ( k2_wellord1(k1_wellord2(B_44),A_43) = k1_wellord2(A_43)
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_48,plain,(
    ! [A_30] :
      ( k3_relat_1(k1_wellord2(A_30)) = A_30
      | ~ v1_relat_1(k1_wellord2(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_74,plain,(
    ! [A_30] : k3_relat_1(k1_wellord2(A_30)) = A_30 ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_48])).

tff(c_56,plain,(
    ! [B_41,A_39] :
      ( k1_wellord1(k1_wellord2(B_41),A_39) = A_39
      | ~ r2_hidden(A_39,B_41)
      | ~ v3_ordinal1(B_41)
      | ~ v3_ordinal1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_374,plain,(
    ! [A_100,B_101] :
      ( ~ r4_wellord1(A_100,k2_wellord1(A_100,k1_wellord1(A_100,B_101)))
      | ~ r2_hidden(B_101,k3_relat_1(A_100))
      | ~ v2_wellord1(A_100)
      | ~ v1_relat_1(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_377,plain,(
    ! [B_41,A_39] :
      ( ~ r4_wellord1(k1_wellord2(B_41),k2_wellord1(k1_wellord2(B_41),A_39))
      | ~ r2_hidden(A_39,k3_relat_1(k1_wellord2(B_41)))
      | ~ v2_wellord1(k1_wellord2(B_41))
      | ~ v1_relat_1(k1_wellord2(B_41))
      | ~ r2_hidden(A_39,B_41)
      | ~ v3_ordinal1(B_41)
      | ~ v3_ordinal1(A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_374])).

tff(c_838,plain,(
    ! [B_146,A_147] :
      ( ~ r4_wellord1(k1_wellord2(B_146),k2_wellord1(k1_wellord2(B_146),A_147))
      | ~ v2_wellord1(k1_wellord2(B_146))
      | ~ r2_hidden(A_147,B_146)
      | ~ v3_ordinal1(B_146)
      | ~ v3_ordinal1(A_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_74,c_377])).

tff(c_1647,plain,(
    ! [B_187,A_188] :
      ( ~ r4_wellord1(k1_wellord2(B_187),k1_wellord2(A_188))
      | ~ v2_wellord1(k1_wellord2(B_187))
      | ~ r2_hidden(A_188,B_187)
      | ~ v3_ordinal1(B_187)
      | ~ v3_ordinal1(A_188)
      | ~ r1_tarski(A_188,B_187) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_838])).

tff(c_1650,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_6'))
    | ~ r2_hidden('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5')
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_107,c_1647])).

tff(c_1656,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_6'))
    | ~ r2_hidden('#skF_5','#skF_6')
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1650])).

tff(c_1660,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1656])).

tff(c_1663,plain,
    ( ~ r1_ordinal1('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_1660])).

tff(c_1666,plain,(
    ~ r1_ordinal1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1663])).

tff(c_12,plain,(
    ! [B_11,A_9] :
      ( r2_hidden(B_11,A_9)
      | r1_ordinal1(A_9,B_11)
      | ~ v3_ordinal1(B_11)
      | ~ v3_ordinal1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_193,plain,(
    ! [D_73,B_74,A_75] :
      ( r2_hidden(k4_tarski(D_73,B_74),A_75)
      | ~ r2_hidden(D_73,k1_wellord1(A_75,B_74))
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4,plain,(
    ! [A_1,C_3,B_2] :
      ( r2_hidden(A_1,k3_relat_1(C_3))
      | ~ r2_hidden(k4_tarski(A_1,B_2),C_3)
      | ~ v1_relat_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_272,plain,(
    ! [D_85,A_86,B_87] :
      ( r2_hidden(D_85,k3_relat_1(A_86))
      | ~ r2_hidden(D_85,k1_wellord1(A_86,B_87))
      | ~ v1_relat_1(A_86) ) ),
    inference(resolution,[status(thm)],[c_193,c_4])).

tff(c_279,plain,(
    ! [D_85,B_41,A_39] :
      ( r2_hidden(D_85,k3_relat_1(k1_wellord2(B_41)))
      | ~ r2_hidden(D_85,A_39)
      | ~ v1_relat_1(k1_wellord2(B_41))
      | ~ r2_hidden(A_39,B_41)
      | ~ v3_ordinal1(B_41)
      | ~ v3_ordinal1(A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_272])).

tff(c_315,plain,(
    ! [D_91,B_92,A_93] :
      ( r2_hidden(D_91,B_92)
      | ~ r2_hidden(D_91,A_93)
      | ~ r2_hidden(A_93,B_92)
      | ~ v3_ordinal1(B_92)
      | ~ v3_ordinal1(A_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_74,c_279])).

tff(c_436,plain,(
    ! [B_108,B_109,A_110] :
      ( r2_hidden(B_108,B_109)
      | ~ r2_hidden(A_110,B_109)
      | ~ v3_ordinal1(B_109)
      | r1_ordinal1(A_110,B_108)
      | ~ v3_ordinal1(B_108)
      | ~ v3_ordinal1(A_110) ) ),
    inference(resolution,[status(thm)],[c_12,c_315])).

tff(c_460,plain,(
    ! [B_111,A_112,B_113] :
      ( r2_hidden(B_111,A_112)
      | r1_ordinal1(B_113,B_111)
      | ~ v3_ordinal1(B_111)
      | r1_ordinal1(A_112,B_113)
      | ~ v3_ordinal1(B_113)
      | ~ v3_ordinal1(A_112) ) ),
    inference(resolution,[status(thm)],[c_12,c_436])).

tff(c_172,plain,(
    ! [B_69,A_70] :
      ( k1_wellord1(k1_wellord2(B_69),A_70) = A_70
      | ~ r2_hidden(A_70,B_69)
      | ~ v3_ordinal1(B_69)
      | ~ v3_ordinal1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_18,plain,(
    ! [D_23,A_12] :
      ( ~ r2_hidden(D_23,k1_wellord1(A_12,D_23))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_178,plain,(
    ! [A_70,B_69] :
      ( ~ r2_hidden(A_70,A_70)
      | ~ v1_relat_1(k1_wellord2(B_69))
      | ~ r2_hidden(A_70,B_69)
      | ~ v3_ordinal1(B_69)
      | ~ v3_ordinal1(A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_18])).

tff(c_184,plain,(
    ! [A_70,B_69] :
      ( ~ r2_hidden(A_70,A_70)
      | ~ r2_hidden(A_70,B_69)
      | ~ v3_ordinal1(B_69)
      | ~ v3_ordinal1(A_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_178])).

tff(c_530,plain,(
    ! [A_117,B_118,B_119] :
      ( ~ r2_hidden(A_117,B_118)
      | ~ v3_ordinal1(B_118)
      | r1_ordinal1(B_119,A_117)
      | r1_ordinal1(A_117,B_119)
      | ~ v3_ordinal1(B_119)
      | ~ v3_ordinal1(A_117) ) ),
    inference(resolution,[status(thm)],[c_460,c_184])).

tff(c_557,plain,(
    ! [B_119,B_11,A_9] :
      ( r1_ordinal1(B_119,B_11)
      | r1_ordinal1(B_11,B_119)
      | ~ v3_ordinal1(B_119)
      | r1_ordinal1(A_9,B_11)
      | ~ v3_ordinal1(B_11)
      | ~ v3_ordinal1(A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_530])).

tff(c_595,plain,(
    ! [B_11,B_119] :
      ( r1_ordinal1(B_11,B_119)
      | ~ v3_ordinal1(B_11)
      | ~ v3_ordinal1(B_119)
      | r1_ordinal1(B_119,B_11) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_557])).

tff(c_1671,plain,
    ( ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6')
    | r1_ordinal1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_595,c_1666])).

tff(c_1679,plain,(
    r1_ordinal1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_1671])).

tff(c_1653,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_5'))
    | ~ r2_hidden('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6')
    | ~ r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_1647])).

tff(c_1659,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_5'))
    | ~ r2_hidden('#skF_6','#skF_5')
    | ~ r1_tarski('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_1653])).

tff(c_1732,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1659])).

tff(c_1735,plain,
    ( ~ r1_ordinal1('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_8,c_1732])).

tff(c_1739,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_1679,c_1735])).

tff(c_1740,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | ~ v2_wellord1(k1_wellord2('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1659])).

tff(c_1748,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_1740])).

tff(c_1751,plain,(
    ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_1748])).

tff(c_1755,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1751])).

tff(c_1756,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_1740])).

tff(c_1773,plain,
    ( r1_ordinal1('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_1756])).

tff(c_1786,plain,(
    r1_ordinal1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1773])).

tff(c_1788,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1666,c_1786])).

tff(c_1789,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | ~ v2_wellord1(k1_wellord2('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_1656])).

tff(c_1845,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1789])).

tff(c_1848,plain,(
    ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_1845])).

tff(c_1852,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1848])).

tff(c_1853,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_1789])).

tff(c_2003,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_10,c_1853])).

tff(c_2029,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_2003])).

tff(c_2030,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2029])).

tff(c_1879,plain,
    ( r1_ordinal1('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_12,c_1853])).

tff(c_1907,plain,(
    r1_ordinal1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_1879])).

tff(c_1855,plain,(
    ~ r1_tarski('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1659])).

tff(c_1910,plain,
    ( ~ r1_ordinal1('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_8,c_1855])).

tff(c_1913,plain,(
    ~ r1_ordinal1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_68,c_1910])).

tff(c_1983,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1907,c_1913])).

tff(c_1984,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | ~ v2_wellord1(k1_wellord2('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1659])).

tff(c_2114,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2030,c_1984])).

tff(c_2117,plain,(
    ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_2114])).

tff(c_2121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2117])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:09:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.71/1.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.71/1.83  
% 4.71/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.71/1.83  %$ r4_wellord1 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 4.71/1.83  
% 4.71/1.83  %Foreground sorts:
% 4.71/1.83  
% 4.71/1.83  
% 4.71/1.83  %Background operators:
% 4.71/1.83  
% 4.71/1.83  
% 4.71/1.83  %Foreground operators:
% 4.71/1.83  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.71/1.83  tff(r4_wellord1, type, r4_wellord1: ($i * $i) > $o).
% 4.71/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.71/1.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.71/1.83  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.71/1.83  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 4.71/1.83  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.71/1.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.71/1.83  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 4.71/1.83  tff('#skF_5', type, '#skF_5': $i).
% 4.71/1.83  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 4.71/1.83  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 4.71/1.83  tff('#skF_6', type, '#skF_6': $i).
% 4.71/1.83  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.71/1.83  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 4.71/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.71/1.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.71/1.83  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 4.71/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.71/1.83  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 4.71/1.83  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.71/1.83  
% 4.71/1.85  tff(f_141, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r4_wellord1(k1_wellord2(A), k1_wellord2(B)) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_wellord2)).
% 4.71/1.85  tff(f_127, axiom, (![A]: (v3_ordinal1(A) => v2_wellord1(k1_wellord2(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_wellord2)).
% 4.71/1.85  tff(f_56, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 4.71/1.85  tff(f_41, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 4.71/1.85  tff(f_114, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 4.71/1.85  tff(f_87, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r4_wellord1(A, B) => r4_wellord1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_wellord1)).
% 4.71/1.85  tff(f_131, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_wellord2)).
% 4.71/1.85  tff(f_112, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 4.71/1.85  tff(f_123, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) => (A = k1_wellord1(k1_wellord2(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_wellord2)).
% 4.71/1.85  tff(f_97, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) => (![B]: ~(r2_hidden(B, k3_relat_1(A)) & r4_wellord1(A, k2_wellord1(A, k1_wellord1(A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_wellord1)).
% 4.71/1.85  tff(f_65, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 4.71/1.85  tff(f_78, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k1_wellord1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (~(D = B) & r2_hidden(k4_tarski(D, B), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord1)).
% 4.71/1.85  tff(f_33, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relat_1)).
% 4.71/1.85  tff(c_68, plain, (v3_ordinal1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.71/1.85  tff(c_58, plain, (![A_42]: (v2_wellord1(k1_wellord2(A_42)) | ~v3_ordinal1(A_42))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.71/1.85  tff(c_62, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.71/1.85  tff(c_66, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.71/1.85  tff(c_10, plain, (![B_8, A_6]: (r2_hidden(B_8, A_6) | B_8=A_6 | r2_hidden(A_6, B_8) | ~v3_ordinal1(B_8) | ~v3_ordinal1(A_6))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.71/1.85  tff(c_8, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~r1_ordinal1(A_4, B_5) | ~v3_ordinal1(B_5) | ~v3_ordinal1(A_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.71/1.85  tff(c_54, plain, (![A_38]: (v1_relat_1(k1_wellord2(A_38)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.71/1.85  tff(c_64, plain, (r4_wellord1(k1_wellord2('#skF_5'), k1_wellord2('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.71/1.85  tff(c_102, plain, (![B_57, A_58]: (r4_wellord1(B_57, A_58) | ~r4_wellord1(A_58, B_57) | ~v1_relat_1(B_57) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.71/1.85  tff(c_104, plain, (r4_wellord1(k1_wellord2('#skF_6'), k1_wellord2('#skF_5')) | ~v1_relat_1(k1_wellord2('#skF_6')) | ~v1_relat_1(k1_wellord2('#skF_5'))), inference(resolution, [status(thm)], [c_64, c_102])).
% 4.71/1.85  tff(c_107, plain, (r4_wellord1(k1_wellord2('#skF_6'), k1_wellord2('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_54, c_104])).
% 4.71/1.85  tff(c_60, plain, (![B_44, A_43]: (k2_wellord1(k1_wellord2(B_44), A_43)=k1_wellord2(A_43) | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_131])).
% 4.71/1.85  tff(c_48, plain, (![A_30]: (k3_relat_1(k1_wellord2(A_30))=A_30 | ~v1_relat_1(k1_wellord2(A_30)))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.71/1.85  tff(c_74, plain, (![A_30]: (k3_relat_1(k1_wellord2(A_30))=A_30)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_48])).
% 4.71/1.85  tff(c_56, plain, (![B_41, A_39]: (k1_wellord1(k1_wellord2(B_41), A_39)=A_39 | ~r2_hidden(A_39, B_41) | ~v3_ordinal1(B_41) | ~v3_ordinal1(A_39))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.71/1.85  tff(c_374, plain, (![A_100, B_101]: (~r4_wellord1(A_100, k2_wellord1(A_100, k1_wellord1(A_100, B_101))) | ~r2_hidden(B_101, k3_relat_1(A_100)) | ~v2_wellord1(A_100) | ~v1_relat_1(A_100))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.71/1.85  tff(c_377, plain, (![B_41, A_39]: (~r4_wellord1(k1_wellord2(B_41), k2_wellord1(k1_wellord2(B_41), A_39)) | ~r2_hidden(A_39, k3_relat_1(k1_wellord2(B_41))) | ~v2_wellord1(k1_wellord2(B_41)) | ~v1_relat_1(k1_wellord2(B_41)) | ~r2_hidden(A_39, B_41) | ~v3_ordinal1(B_41) | ~v3_ordinal1(A_39))), inference(superposition, [status(thm), theory('equality')], [c_56, c_374])).
% 4.71/1.85  tff(c_838, plain, (![B_146, A_147]: (~r4_wellord1(k1_wellord2(B_146), k2_wellord1(k1_wellord2(B_146), A_147)) | ~v2_wellord1(k1_wellord2(B_146)) | ~r2_hidden(A_147, B_146) | ~v3_ordinal1(B_146) | ~v3_ordinal1(A_147))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_74, c_377])).
% 4.71/1.85  tff(c_1647, plain, (![B_187, A_188]: (~r4_wellord1(k1_wellord2(B_187), k1_wellord2(A_188)) | ~v2_wellord1(k1_wellord2(B_187)) | ~r2_hidden(A_188, B_187) | ~v3_ordinal1(B_187) | ~v3_ordinal1(A_188) | ~r1_tarski(A_188, B_187))), inference(superposition, [status(thm), theory('equality')], [c_60, c_838])).
% 4.71/1.85  tff(c_1650, plain, (~v2_wellord1(k1_wellord2('#skF_6')) | ~r2_hidden('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5') | ~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_107, c_1647])).
% 4.71/1.85  tff(c_1656, plain, (~v2_wellord1(k1_wellord2('#skF_6')) | ~r2_hidden('#skF_5', '#skF_6') | ~r1_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_1650])).
% 4.71/1.85  tff(c_1660, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_1656])).
% 4.71/1.85  tff(c_1663, plain, (~r1_ordinal1('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_8, c_1660])).
% 4.71/1.85  tff(c_1666, plain, (~r1_ordinal1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_1663])).
% 4.71/1.85  tff(c_12, plain, (![B_11, A_9]: (r2_hidden(B_11, A_9) | r1_ordinal1(A_9, B_11) | ~v3_ordinal1(B_11) | ~v3_ordinal1(A_9))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.71/1.85  tff(c_193, plain, (![D_73, B_74, A_75]: (r2_hidden(k4_tarski(D_73, B_74), A_75) | ~r2_hidden(D_73, k1_wellord1(A_75, B_74)) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.71/1.85  tff(c_4, plain, (![A_1, C_3, B_2]: (r2_hidden(A_1, k3_relat_1(C_3)) | ~r2_hidden(k4_tarski(A_1, B_2), C_3) | ~v1_relat_1(C_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.71/1.85  tff(c_272, plain, (![D_85, A_86, B_87]: (r2_hidden(D_85, k3_relat_1(A_86)) | ~r2_hidden(D_85, k1_wellord1(A_86, B_87)) | ~v1_relat_1(A_86))), inference(resolution, [status(thm)], [c_193, c_4])).
% 4.71/1.85  tff(c_279, plain, (![D_85, B_41, A_39]: (r2_hidden(D_85, k3_relat_1(k1_wellord2(B_41))) | ~r2_hidden(D_85, A_39) | ~v1_relat_1(k1_wellord2(B_41)) | ~r2_hidden(A_39, B_41) | ~v3_ordinal1(B_41) | ~v3_ordinal1(A_39))), inference(superposition, [status(thm), theory('equality')], [c_56, c_272])).
% 4.71/1.85  tff(c_315, plain, (![D_91, B_92, A_93]: (r2_hidden(D_91, B_92) | ~r2_hidden(D_91, A_93) | ~r2_hidden(A_93, B_92) | ~v3_ordinal1(B_92) | ~v3_ordinal1(A_93))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_74, c_279])).
% 4.71/1.85  tff(c_436, plain, (![B_108, B_109, A_110]: (r2_hidden(B_108, B_109) | ~r2_hidden(A_110, B_109) | ~v3_ordinal1(B_109) | r1_ordinal1(A_110, B_108) | ~v3_ordinal1(B_108) | ~v3_ordinal1(A_110))), inference(resolution, [status(thm)], [c_12, c_315])).
% 4.71/1.85  tff(c_460, plain, (![B_111, A_112, B_113]: (r2_hidden(B_111, A_112) | r1_ordinal1(B_113, B_111) | ~v3_ordinal1(B_111) | r1_ordinal1(A_112, B_113) | ~v3_ordinal1(B_113) | ~v3_ordinal1(A_112))), inference(resolution, [status(thm)], [c_12, c_436])).
% 4.71/1.85  tff(c_172, plain, (![B_69, A_70]: (k1_wellord1(k1_wellord2(B_69), A_70)=A_70 | ~r2_hidden(A_70, B_69) | ~v3_ordinal1(B_69) | ~v3_ordinal1(A_70))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.71/1.85  tff(c_18, plain, (![D_23, A_12]: (~r2_hidden(D_23, k1_wellord1(A_12, D_23)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.71/1.85  tff(c_178, plain, (![A_70, B_69]: (~r2_hidden(A_70, A_70) | ~v1_relat_1(k1_wellord2(B_69)) | ~r2_hidden(A_70, B_69) | ~v3_ordinal1(B_69) | ~v3_ordinal1(A_70))), inference(superposition, [status(thm), theory('equality')], [c_172, c_18])).
% 4.71/1.85  tff(c_184, plain, (![A_70, B_69]: (~r2_hidden(A_70, A_70) | ~r2_hidden(A_70, B_69) | ~v3_ordinal1(B_69) | ~v3_ordinal1(A_70))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_178])).
% 4.71/1.85  tff(c_530, plain, (![A_117, B_118, B_119]: (~r2_hidden(A_117, B_118) | ~v3_ordinal1(B_118) | r1_ordinal1(B_119, A_117) | r1_ordinal1(A_117, B_119) | ~v3_ordinal1(B_119) | ~v3_ordinal1(A_117))), inference(resolution, [status(thm)], [c_460, c_184])).
% 4.71/1.85  tff(c_557, plain, (![B_119, B_11, A_9]: (r1_ordinal1(B_119, B_11) | r1_ordinal1(B_11, B_119) | ~v3_ordinal1(B_119) | r1_ordinal1(A_9, B_11) | ~v3_ordinal1(B_11) | ~v3_ordinal1(A_9))), inference(resolution, [status(thm)], [c_12, c_530])).
% 4.71/1.85  tff(c_595, plain, (![B_11, B_119]: (r1_ordinal1(B_11, B_119) | ~v3_ordinal1(B_11) | ~v3_ordinal1(B_119) | r1_ordinal1(B_119, B_11))), inference(factorization, [status(thm), theory('equality')], [c_557])).
% 4.71/1.85  tff(c_1671, plain, (~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6') | r1_ordinal1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_595, c_1666])).
% 4.71/1.85  tff(c_1679, plain, (r1_ordinal1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_1671])).
% 4.71/1.85  tff(c_1653, plain, (~v2_wellord1(k1_wellord2('#skF_5')) | ~r2_hidden('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6') | ~r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_64, c_1647])).
% 4.71/1.85  tff(c_1659, plain, (~v2_wellord1(k1_wellord2('#skF_5')) | ~r2_hidden('#skF_6', '#skF_5') | ~r1_tarski('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_1653])).
% 4.71/1.85  tff(c_1732, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_1659])).
% 4.71/1.85  tff(c_1735, plain, (~r1_ordinal1('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_8, c_1732])).
% 4.71/1.85  tff(c_1739, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_1679, c_1735])).
% 4.71/1.85  tff(c_1740, plain, (~r2_hidden('#skF_6', '#skF_5') | ~v2_wellord1(k1_wellord2('#skF_5'))), inference(splitRight, [status(thm)], [c_1659])).
% 4.71/1.85  tff(c_1748, plain, (~v2_wellord1(k1_wellord2('#skF_5'))), inference(splitLeft, [status(thm)], [c_1740])).
% 4.71/1.85  tff(c_1751, plain, (~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_1748])).
% 4.71/1.85  tff(c_1755, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_1751])).
% 4.71/1.85  tff(c_1756, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_1740])).
% 4.71/1.85  tff(c_1773, plain, (r1_ordinal1('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_12, c_1756])).
% 4.71/1.85  tff(c_1786, plain, (r1_ordinal1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_1773])).
% 4.71/1.85  tff(c_1788, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1666, c_1786])).
% 4.71/1.85  tff(c_1789, plain, (~r2_hidden('#skF_5', '#skF_6') | ~v2_wellord1(k1_wellord2('#skF_6'))), inference(splitRight, [status(thm)], [c_1656])).
% 4.71/1.85  tff(c_1845, plain, (~v2_wellord1(k1_wellord2('#skF_6'))), inference(splitLeft, [status(thm)], [c_1789])).
% 4.71/1.85  tff(c_1848, plain, (~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_1845])).
% 4.71/1.85  tff(c_1852, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_1848])).
% 4.71/1.85  tff(c_1853, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_1789])).
% 4.71/1.85  tff(c_2003, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_10, c_1853])).
% 4.71/1.85  tff(c_2029, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_2003])).
% 4.71/1.85  tff(c_2030, plain, (r2_hidden('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_2029])).
% 4.71/1.85  tff(c_1879, plain, (r1_ordinal1('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_12, c_1853])).
% 4.71/1.85  tff(c_1907, plain, (r1_ordinal1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_1879])).
% 4.71/1.85  tff(c_1855, plain, (~r1_tarski('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_1659])).
% 4.71/1.85  tff(c_1910, plain, (~r1_ordinal1('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_8, c_1855])).
% 4.71/1.85  tff(c_1913, plain, (~r1_ordinal1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_68, c_1910])).
% 4.71/1.85  tff(c_1983, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1907, c_1913])).
% 4.71/1.85  tff(c_1984, plain, (~r2_hidden('#skF_6', '#skF_5') | ~v2_wellord1(k1_wellord2('#skF_5'))), inference(splitRight, [status(thm)], [c_1659])).
% 4.71/1.85  tff(c_2114, plain, (~v2_wellord1(k1_wellord2('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2030, c_1984])).
% 4.71/1.85  tff(c_2117, plain, (~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_2114])).
% 4.71/1.85  tff(c_2121, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_2117])).
% 4.71/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.71/1.85  
% 4.71/1.85  Inference rules
% 4.71/1.85  ----------------------
% 4.71/1.85  #Ref     : 0
% 4.71/1.85  #Sup     : 408
% 4.71/1.85  #Fact    : 16
% 4.71/1.85  #Define  : 0
% 4.71/1.85  #Split   : 5
% 4.71/1.85  #Chain   : 0
% 4.71/1.85  #Close   : 0
% 4.71/1.85  
% 4.71/1.85  Ordering : KBO
% 4.71/1.85  
% 4.71/1.85  Simplification rules
% 4.71/1.85  ----------------------
% 4.71/1.85  #Subsume      : 41
% 4.71/1.85  #Demod        : 171
% 4.71/1.85  #Tautology    : 40
% 4.71/1.85  #SimpNegUnit  : 10
% 4.71/1.85  #BackRed      : 0
% 4.71/1.85  
% 4.71/1.85  #Partial instantiations: 0
% 4.71/1.85  #Strategies tried      : 1
% 4.71/1.85  
% 4.71/1.85  Timing (in seconds)
% 4.71/1.85  ----------------------
% 4.71/1.85  Preprocessing        : 0.34
% 4.71/1.85  Parsing              : 0.18
% 4.71/1.85  CNF conversion       : 0.03
% 4.71/1.85  Main loop            : 0.74
% 4.71/1.86  Inferencing          : 0.23
% 4.71/1.86  Reduction            : 0.17
% 4.71/1.86  Demodulation         : 0.12
% 4.71/1.86  BG Simplification    : 0.04
% 4.71/1.86  Subsumption          : 0.24
% 4.71/1.86  Abstraction          : 0.04
% 4.71/1.86  MUC search           : 0.00
% 4.71/1.86  Cooper               : 0.00
% 4.71/1.86  Total                : 1.12
% 4.71/1.86  Index Insertion      : 0.00
% 4.71/1.86  Index Deletion       : 0.00
% 4.71/1.86  Index Matching       : 0.00
% 4.71/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
