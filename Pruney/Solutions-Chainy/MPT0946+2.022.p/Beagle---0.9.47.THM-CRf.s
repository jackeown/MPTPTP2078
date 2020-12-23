%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:34 EST 2020

% Result     : Theorem 4.23s
% Output     : CNFRefutation 4.23s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 519 expanded)
%              Number of leaves         :   31 ( 197 expanded)
%              Depth                    :   17
%              Number of atoms          :  205 (1430 expanded)
%              Number of equality atoms :   23 ( 197 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_wellord1 > r2_hidden > r1_tarski > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

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

tff(f_124,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r4_wellord1(k1_wellord2(A),k1_wellord2(B))
             => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).

tff(f_110,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v2_wellord1(k1_wellord2(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).

tff(f_47,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_114,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_97,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_95,axiom,(
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

tff(f_106,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
           => A = k1_wellord1(k1_wellord2(B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
       => ! [B] :
            ~ ( r2_hidden(B,k3_relat_1(A))
              & r4_wellord1(A,k2_wellord1(A,k1_wellord1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v2_wellord1(B)
       => k3_relat_1(k2_wellord1(B,k1_wellord1(B,A))) = k1_wellord1(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_wellord1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k3_relat_1(k2_wellord1(C,B)))
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_wellord1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
           => r4_wellord1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

tff(c_50,plain,(
    v3_ordinal1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_42,plain,(
    ! [A_32] :
      ( v2_wellord1(k1_wellord2(A_32))
      | ~ v3_ordinal1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_52,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_46,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_8,plain,(
    ! [B_8,A_6] :
      ( r2_hidden(B_8,A_6)
      | B_8 = A_6
      | r2_hidden(A_6,B_8)
      | ~ v3_ordinal1(B_8)
      | ~ v3_ordinal1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_48,plain,(
    r4_wellord1(k1_wellord2('#skF_4'),k1_wellord2('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_44,plain,(
    ! [B_34,A_33] :
      ( k2_wellord1(k1_wellord2(B_34),A_33) = k1_wellord2(A_33)
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_38,plain,(
    ! [A_28] : v1_relat_1(k1_wellord2(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_32,plain,(
    ! [A_20] :
      ( k3_relat_1(k1_wellord2(A_20)) = A_20
      | ~ v1_relat_1(k1_wellord2(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_58,plain,(
    ! [A_20] : k3_relat_1(k1_wellord2(A_20)) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_32])).

tff(c_40,plain,(
    ! [B_31,A_29] :
      ( k1_wellord1(k1_wellord2(B_31),A_29) = A_29
      | ~ r2_hidden(A_29,B_31)
      | ~ v3_ordinal1(B_31)
      | ~ v3_ordinal1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_304,plain,(
    ! [A_75,B_76] :
      ( ~ r4_wellord1(A_75,k2_wellord1(A_75,k1_wellord1(A_75,B_76)))
      | ~ r2_hidden(B_76,k3_relat_1(A_75))
      | ~ v2_wellord1(A_75)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_307,plain,(
    ! [B_31,A_29] :
      ( ~ r4_wellord1(k1_wellord2(B_31),k2_wellord1(k1_wellord2(B_31),A_29))
      | ~ r2_hidden(A_29,k3_relat_1(k1_wellord2(B_31)))
      | ~ v2_wellord1(k1_wellord2(B_31))
      | ~ v1_relat_1(k1_wellord2(B_31))
      | ~ r2_hidden(A_29,B_31)
      | ~ v3_ordinal1(B_31)
      | ~ v3_ordinal1(A_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_304])).

tff(c_756,plain,(
    ! [B_120,A_121] :
      ( ~ r4_wellord1(k1_wellord2(B_120),k2_wellord1(k1_wellord2(B_120),A_121))
      | ~ v2_wellord1(k1_wellord2(B_120))
      | ~ r2_hidden(A_121,B_120)
      | ~ v3_ordinal1(B_120)
      | ~ v3_ordinal1(A_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_58,c_307])).

tff(c_1297,plain,(
    ! [B_168,A_169] :
      ( ~ r4_wellord1(k1_wellord2(B_168),k1_wellord2(A_169))
      | ~ v2_wellord1(k1_wellord2(B_168))
      | ~ r2_hidden(A_169,B_168)
      | ~ v3_ordinal1(B_168)
      | ~ v3_ordinal1(A_169)
      | ~ r1_tarski(A_169,B_168) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_756])).

tff(c_1303,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_5','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_5')
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_1297])).

tff(c_1309,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_4'))
    | ~ r2_hidden('#skF_5','#skF_4')
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_1303])).

tff(c_1310,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1309])).

tff(c_14,plain,(
    ! [B_13,A_12] :
      ( k3_relat_1(k2_wellord1(B_13,k1_wellord1(B_13,A_12))) = k1_wellord1(B_13,A_12)
      | ~ v2_wellord1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_170,plain,(
    ! [A_59,C_60,B_61] :
      ( r2_hidden(A_59,k3_relat_1(C_60))
      | ~ r2_hidden(A_59,k3_relat_1(k2_wellord1(C_60,B_61)))
      | ~ v1_relat_1(C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_628,plain,(
    ! [C_107,B_108,B_109] :
      ( r2_hidden('#skF_1'(k3_relat_1(k2_wellord1(C_107,B_108)),B_109),k3_relat_1(C_107))
      | ~ v1_relat_1(C_107)
      | r1_tarski(k3_relat_1(k2_wellord1(C_107,B_108)),B_109) ) ),
    inference(resolution,[status(thm)],[c_6,c_170])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_666,plain,(
    ! [C_110,B_111] :
      ( ~ v1_relat_1(C_110)
      | r1_tarski(k3_relat_1(k2_wellord1(C_110,B_111)),k3_relat_1(C_110)) ) ),
    inference(resolution,[status(thm)],[c_628,c_4])).

tff(c_728,plain,(
    ! [B_116,A_117] :
      ( ~ v1_relat_1(B_116)
      | r1_tarski(k1_wellord1(B_116,A_117),k3_relat_1(B_116))
      | ~ v2_wellord1(B_116)
      | ~ v1_relat_1(B_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_666])).

tff(c_741,plain,(
    ! [B_31,A_29] :
      ( ~ v1_relat_1(k1_wellord2(B_31))
      | r1_tarski(A_29,k3_relat_1(k1_wellord2(B_31)))
      | ~ v2_wellord1(k1_wellord2(B_31))
      | ~ v1_relat_1(k1_wellord2(B_31))
      | ~ r2_hidden(A_29,B_31)
      | ~ v3_ordinal1(B_31)
      | ~ v3_ordinal1(A_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_728])).

tff(c_752,plain,(
    ! [A_118,B_119] :
      ( r1_tarski(A_118,B_119)
      | ~ v2_wellord1(k1_wellord2(B_119))
      | ~ r2_hidden(A_118,B_119)
      | ~ v3_ordinal1(B_119)
      | ~ v3_ordinal1(A_118) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_58,c_38,c_741])).

tff(c_760,plain,(
    ! [A_122,A_123] :
      ( r1_tarski(A_122,A_123)
      | ~ r2_hidden(A_122,A_123)
      | ~ v3_ordinal1(A_122)
      | ~ v3_ordinal1(A_123) ) ),
    inference(resolution,[status(thm)],[c_42,c_752])).

tff(c_810,plain,(
    ! [B_8,A_6] :
      ( r1_tarski(B_8,A_6)
      | B_8 = A_6
      | r2_hidden(A_6,B_8)
      | ~ v3_ordinal1(B_8)
      | ~ v3_ordinal1(A_6) ) ),
    inference(resolution,[status(thm)],[c_8,c_760])).

tff(c_813,plain,(
    ! [B_124,A_125] :
      ( r1_tarski(B_124,A_125)
      | B_124 = A_125
      | r2_hidden(A_125,B_124)
      | ~ v3_ordinal1(B_124)
      | ~ v3_ordinal1(A_125) ) ),
    inference(resolution,[status(thm)],[c_8,c_760])).

tff(c_755,plain,(
    ! [A_118,A_32] :
      ( r1_tarski(A_118,A_32)
      | ~ r2_hidden(A_118,A_32)
      | ~ v3_ordinal1(A_118)
      | ~ v3_ordinal1(A_32) ) ),
    inference(resolution,[status(thm)],[c_42,c_752])).

tff(c_844,plain,(
    ! [A_125,B_124] :
      ( r1_tarski(A_125,B_124)
      | r1_tarski(B_124,A_125)
      | B_124 = A_125
      | ~ v3_ordinal1(B_124)
      | ~ v3_ordinal1(A_125) ) ),
    inference(resolution,[status(thm)],[c_813,c_755])).

tff(c_1313,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | '#skF_5' = '#skF_4'
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_844,c_1310])).

tff(c_1319,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_1313])).

tff(c_1320,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1319])).

tff(c_91,plain,(
    ! [B_49,A_50] :
      ( r4_wellord1(B_49,A_50)
      | ~ r4_wellord1(A_50,B_49)
      | ~ v1_relat_1(B_49)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_93,plain,
    ( r4_wellord1(k1_wellord2('#skF_5'),k1_wellord2('#skF_4'))
    | ~ v1_relat_1(k1_wellord2('#skF_5'))
    | ~ v1_relat_1(k1_wellord2('#skF_4')) ),
    inference(resolution,[status(thm)],[c_48,c_91])).

tff(c_96,plain,(
    r4_wellord1(k1_wellord2('#skF_5'),k1_wellord2('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_93])).

tff(c_1300,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_5'))
    | ~ r2_hidden('#skF_4','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_4')
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_96,c_1297])).

tff(c_1306,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_5'))
    | ~ r2_hidden('#skF_4','#skF_5')
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1300])).

tff(c_1340,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_5'))
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1320,c_1306])).

tff(c_1341,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1340])).

tff(c_1344,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | '#skF_5' = '#skF_4'
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_810,c_1341])).

tff(c_1349,plain,
    ( r1_tarski('#skF_5','#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1344])).

tff(c_1351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1310,c_1349])).

tff(c_1352,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_1340])).

tff(c_1475,plain,(
    ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_1352])).

tff(c_1479,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1475])).

tff(c_1480,plain,
    ( ~ r2_hidden('#skF_5','#skF_4')
    | ~ v2_wellord1(k1_wellord2('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1309])).

tff(c_1495,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_1480])).

tff(c_1498,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_1495])).

tff(c_1502,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1498])).

tff(c_1503,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1480])).

tff(c_1510,plain,
    ( '#skF_5' = '#skF_4'
    | r2_hidden('#skF_4','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_1503])).

tff(c_1520,plain,
    ( '#skF_5' = '#skF_4'
    | r2_hidden('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1510])).

tff(c_1521,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1520])).

tff(c_1528,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1521,c_755])).

tff(c_1535,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_52,c_1528])).

tff(c_1820,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1535,c_1521,c_1306])).

tff(c_1823,plain,(
    ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_1820])).

tff(c_1827,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1823])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:08:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.23/1.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.23/1.70  
% 4.23/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.23/1.71  %$ r4_wellord1 > r2_hidden > r1_tarski > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 4.23/1.71  
% 4.23/1.71  %Foreground sorts:
% 4.23/1.71  
% 4.23/1.71  
% 4.23/1.71  %Background operators:
% 4.23/1.71  
% 4.23/1.71  
% 4.23/1.71  %Foreground operators:
% 4.23/1.71  tff(r4_wellord1, type, r4_wellord1: ($i * $i) > $o).
% 4.23/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.23/1.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.23/1.71  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.23/1.71  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 4.23/1.71  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.23/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.23/1.71  tff('#skF_5', type, '#skF_5': $i).
% 4.23/1.71  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 4.23/1.71  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 4.23/1.71  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 4.23/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.23/1.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.23/1.71  tff('#skF_4', type, '#skF_4': $i).
% 4.23/1.71  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 4.23/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.23/1.71  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.23/1.71  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 4.23/1.71  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.23/1.71  
% 4.23/1.72  tff(f_124, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r4_wellord1(k1_wellord2(A), k1_wellord2(B)) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_wellord2)).
% 4.23/1.72  tff(f_110, axiom, (![A]: (v3_ordinal1(A) => v2_wellord1(k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_wellord2)).
% 4.23/1.72  tff(f_47, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 4.23/1.72  tff(f_114, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_wellord2)).
% 4.23/1.72  tff(f_97, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 4.23/1.72  tff(f_95, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 4.23/1.72  tff(f_106, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) => (A = k1_wellord1(k1_wellord2(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_wellord2)).
% 4.23/1.72  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) => (![B]: ~(r2_hidden(B, k3_relat_1(A)) & r4_wellord1(A, k2_wellord1(A, k1_wellord1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_wellord1)).
% 4.23/1.72  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (v2_wellord1(B) => (k3_relat_1(k2_wellord1(B, k1_wellord1(B, A))) = k1_wellord1(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_wellord1)).
% 4.23/1.72  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.23/1.72  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k3_relat_1(k2_wellord1(C, B))) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_wellord1)).
% 4.23/1.72  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r4_wellord1(A, B) => r4_wellord1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_wellord1)).
% 4.23/1.72  tff(c_50, plain, (v3_ordinal1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.23/1.72  tff(c_42, plain, (![A_32]: (v2_wellord1(k1_wellord2(A_32)) | ~v3_ordinal1(A_32))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.23/1.72  tff(c_52, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.23/1.72  tff(c_46, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.23/1.72  tff(c_8, plain, (![B_8, A_6]: (r2_hidden(B_8, A_6) | B_8=A_6 | r2_hidden(A_6, B_8) | ~v3_ordinal1(B_8) | ~v3_ordinal1(A_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.23/1.72  tff(c_48, plain, (r4_wellord1(k1_wellord2('#skF_4'), k1_wellord2('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.23/1.72  tff(c_44, plain, (![B_34, A_33]: (k2_wellord1(k1_wellord2(B_34), A_33)=k1_wellord2(A_33) | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.23/1.72  tff(c_38, plain, (![A_28]: (v1_relat_1(k1_wellord2(A_28)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.23/1.72  tff(c_32, plain, (![A_20]: (k3_relat_1(k1_wellord2(A_20))=A_20 | ~v1_relat_1(k1_wellord2(A_20)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.23/1.72  tff(c_58, plain, (![A_20]: (k3_relat_1(k1_wellord2(A_20))=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_32])).
% 4.23/1.72  tff(c_40, plain, (![B_31, A_29]: (k1_wellord1(k1_wellord2(B_31), A_29)=A_29 | ~r2_hidden(A_29, B_31) | ~v3_ordinal1(B_31) | ~v3_ordinal1(A_29))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.23/1.72  tff(c_304, plain, (![A_75, B_76]: (~r4_wellord1(A_75, k2_wellord1(A_75, k1_wellord1(A_75, B_76))) | ~r2_hidden(B_76, k3_relat_1(A_75)) | ~v2_wellord1(A_75) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.23/1.72  tff(c_307, plain, (![B_31, A_29]: (~r4_wellord1(k1_wellord2(B_31), k2_wellord1(k1_wellord2(B_31), A_29)) | ~r2_hidden(A_29, k3_relat_1(k1_wellord2(B_31))) | ~v2_wellord1(k1_wellord2(B_31)) | ~v1_relat_1(k1_wellord2(B_31)) | ~r2_hidden(A_29, B_31) | ~v3_ordinal1(B_31) | ~v3_ordinal1(A_29))), inference(superposition, [status(thm), theory('equality')], [c_40, c_304])).
% 4.23/1.72  tff(c_756, plain, (![B_120, A_121]: (~r4_wellord1(k1_wellord2(B_120), k2_wellord1(k1_wellord2(B_120), A_121)) | ~v2_wellord1(k1_wellord2(B_120)) | ~r2_hidden(A_121, B_120) | ~v3_ordinal1(B_120) | ~v3_ordinal1(A_121))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_58, c_307])).
% 4.23/1.72  tff(c_1297, plain, (![B_168, A_169]: (~r4_wellord1(k1_wellord2(B_168), k1_wellord2(A_169)) | ~v2_wellord1(k1_wellord2(B_168)) | ~r2_hidden(A_169, B_168) | ~v3_ordinal1(B_168) | ~v3_ordinal1(A_169) | ~r1_tarski(A_169, B_168))), inference(superposition, [status(thm), theory('equality')], [c_44, c_756])).
% 4.23/1.72  tff(c_1303, plain, (~v2_wellord1(k1_wellord2('#skF_4')) | ~r2_hidden('#skF_5', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_5') | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_1297])).
% 4.23/1.72  tff(c_1309, plain, (~v2_wellord1(k1_wellord2('#skF_4')) | ~r2_hidden('#skF_5', '#skF_4') | ~r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_1303])).
% 4.23/1.72  tff(c_1310, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_1309])).
% 4.23/1.72  tff(c_14, plain, (![B_13, A_12]: (k3_relat_1(k2_wellord1(B_13, k1_wellord1(B_13, A_12)))=k1_wellord1(B_13, A_12) | ~v2_wellord1(B_13) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.23/1.72  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.23/1.72  tff(c_170, plain, (![A_59, C_60, B_61]: (r2_hidden(A_59, k3_relat_1(C_60)) | ~r2_hidden(A_59, k3_relat_1(k2_wellord1(C_60, B_61))) | ~v1_relat_1(C_60))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.23/1.72  tff(c_628, plain, (![C_107, B_108, B_109]: (r2_hidden('#skF_1'(k3_relat_1(k2_wellord1(C_107, B_108)), B_109), k3_relat_1(C_107)) | ~v1_relat_1(C_107) | r1_tarski(k3_relat_1(k2_wellord1(C_107, B_108)), B_109))), inference(resolution, [status(thm)], [c_6, c_170])).
% 4.23/1.72  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.23/1.72  tff(c_666, plain, (![C_110, B_111]: (~v1_relat_1(C_110) | r1_tarski(k3_relat_1(k2_wellord1(C_110, B_111)), k3_relat_1(C_110)))), inference(resolution, [status(thm)], [c_628, c_4])).
% 4.23/1.72  tff(c_728, plain, (![B_116, A_117]: (~v1_relat_1(B_116) | r1_tarski(k1_wellord1(B_116, A_117), k3_relat_1(B_116)) | ~v2_wellord1(B_116) | ~v1_relat_1(B_116))), inference(superposition, [status(thm), theory('equality')], [c_14, c_666])).
% 4.23/1.72  tff(c_741, plain, (![B_31, A_29]: (~v1_relat_1(k1_wellord2(B_31)) | r1_tarski(A_29, k3_relat_1(k1_wellord2(B_31))) | ~v2_wellord1(k1_wellord2(B_31)) | ~v1_relat_1(k1_wellord2(B_31)) | ~r2_hidden(A_29, B_31) | ~v3_ordinal1(B_31) | ~v3_ordinal1(A_29))), inference(superposition, [status(thm), theory('equality')], [c_40, c_728])).
% 4.23/1.72  tff(c_752, plain, (![A_118, B_119]: (r1_tarski(A_118, B_119) | ~v2_wellord1(k1_wellord2(B_119)) | ~r2_hidden(A_118, B_119) | ~v3_ordinal1(B_119) | ~v3_ordinal1(A_118))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_58, c_38, c_741])).
% 4.23/1.72  tff(c_760, plain, (![A_122, A_123]: (r1_tarski(A_122, A_123) | ~r2_hidden(A_122, A_123) | ~v3_ordinal1(A_122) | ~v3_ordinal1(A_123))), inference(resolution, [status(thm)], [c_42, c_752])).
% 4.23/1.72  tff(c_810, plain, (![B_8, A_6]: (r1_tarski(B_8, A_6) | B_8=A_6 | r2_hidden(A_6, B_8) | ~v3_ordinal1(B_8) | ~v3_ordinal1(A_6))), inference(resolution, [status(thm)], [c_8, c_760])).
% 4.23/1.72  tff(c_813, plain, (![B_124, A_125]: (r1_tarski(B_124, A_125) | B_124=A_125 | r2_hidden(A_125, B_124) | ~v3_ordinal1(B_124) | ~v3_ordinal1(A_125))), inference(resolution, [status(thm)], [c_8, c_760])).
% 4.23/1.72  tff(c_755, plain, (![A_118, A_32]: (r1_tarski(A_118, A_32) | ~r2_hidden(A_118, A_32) | ~v3_ordinal1(A_118) | ~v3_ordinal1(A_32))), inference(resolution, [status(thm)], [c_42, c_752])).
% 4.23/1.73  tff(c_844, plain, (![A_125, B_124]: (r1_tarski(A_125, B_124) | r1_tarski(B_124, A_125) | B_124=A_125 | ~v3_ordinal1(B_124) | ~v3_ordinal1(A_125))), inference(resolution, [status(thm)], [c_813, c_755])).
% 4.23/1.73  tff(c_1313, plain, (r1_tarski('#skF_4', '#skF_5') | '#skF_5'='#skF_4' | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_844, c_1310])).
% 4.23/1.73  tff(c_1319, plain, (r1_tarski('#skF_4', '#skF_5') | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_1313])).
% 4.23/1.73  tff(c_1320, plain, (r1_tarski('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_46, c_1319])).
% 4.23/1.73  tff(c_91, plain, (![B_49, A_50]: (r4_wellord1(B_49, A_50) | ~r4_wellord1(A_50, B_49) | ~v1_relat_1(B_49) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.23/1.73  tff(c_93, plain, (r4_wellord1(k1_wellord2('#skF_5'), k1_wellord2('#skF_4')) | ~v1_relat_1(k1_wellord2('#skF_5')) | ~v1_relat_1(k1_wellord2('#skF_4'))), inference(resolution, [status(thm)], [c_48, c_91])).
% 4.23/1.73  tff(c_96, plain, (r4_wellord1(k1_wellord2('#skF_5'), k1_wellord2('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_93])).
% 4.23/1.73  tff(c_1300, plain, (~v2_wellord1(k1_wellord2('#skF_5')) | ~r2_hidden('#skF_4', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_4') | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_96, c_1297])).
% 4.23/1.73  tff(c_1306, plain, (~v2_wellord1(k1_wellord2('#skF_5')) | ~r2_hidden('#skF_4', '#skF_5') | ~r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1300])).
% 4.23/1.73  tff(c_1340, plain, (~v2_wellord1(k1_wellord2('#skF_5')) | ~r2_hidden('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1320, c_1306])).
% 4.23/1.73  tff(c_1341, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_1340])).
% 4.23/1.73  tff(c_1344, plain, (r1_tarski('#skF_5', '#skF_4') | '#skF_5'='#skF_4' | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_810, c_1341])).
% 4.23/1.73  tff(c_1349, plain, (r1_tarski('#skF_5', '#skF_4') | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1344])).
% 4.23/1.73  tff(c_1351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_1310, c_1349])).
% 4.23/1.73  tff(c_1352, plain, (~v2_wellord1(k1_wellord2('#skF_5'))), inference(splitRight, [status(thm)], [c_1340])).
% 4.23/1.73  tff(c_1475, plain, (~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_1352])).
% 4.23/1.73  tff(c_1479, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_1475])).
% 4.23/1.73  tff(c_1480, plain, (~r2_hidden('#skF_5', '#skF_4') | ~v2_wellord1(k1_wellord2('#skF_4'))), inference(splitRight, [status(thm)], [c_1309])).
% 4.23/1.73  tff(c_1495, plain, (~v2_wellord1(k1_wellord2('#skF_4'))), inference(splitLeft, [status(thm)], [c_1480])).
% 4.23/1.73  tff(c_1498, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_1495])).
% 4.23/1.73  tff(c_1502, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_1498])).
% 4.23/1.73  tff(c_1503, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_1480])).
% 4.23/1.73  tff(c_1510, plain, ('#skF_5'='#skF_4' | r2_hidden('#skF_4', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_8, c_1503])).
% 4.23/1.73  tff(c_1520, plain, ('#skF_5'='#skF_4' | r2_hidden('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1510])).
% 4.23/1.73  tff(c_1521, plain, (r2_hidden('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_46, c_1520])).
% 4.23/1.73  tff(c_1528, plain, (r1_tarski('#skF_4', '#skF_5') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_1521, c_755])).
% 4.23/1.73  tff(c_1535, plain, (r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_52, c_1528])).
% 4.23/1.73  tff(c_1820, plain, (~v2_wellord1(k1_wellord2('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1535, c_1521, c_1306])).
% 4.23/1.73  tff(c_1823, plain, (~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_1820])).
% 4.23/1.73  tff(c_1827, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_1823])).
% 4.23/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.23/1.73  
% 4.23/1.73  Inference rules
% 4.23/1.73  ----------------------
% 4.23/1.73  #Ref     : 0
% 4.23/1.73  #Sup     : 407
% 4.23/1.73  #Fact    : 4
% 4.23/1.73  #Define  : 0
% 4.23/1.73  #Split   : 3
% 4.23/1.73  #Chain   : 0
% 4.23/1.73  #Close   : 0
% 4.23/1.73  
% 4.23/1.73  Ordering : KBO
% 4.23/1.73  
% 4.23/1.73  Simplification rules
% 4.23/1.73  ----------------------
% 4.23/1.73  #Subsume      : 45
% 4.23/1.73  #Demod        : 194
% 4.23/1.73  #Tautology    : 52
% 4.23/1.73  #SimpNegUnit  : 6
% 4.23/1.73  #BackRed      : 0
% 4.23/1.73  
% 4.23/1.73  #Partial instantiations: 0
% 4.23/1.73  #Strategies tried      : 1
% 4.23/1.73  
% 4.23/1.73  Timing (in seconds)
% 4.23/1.73  ----------------------
% 4.23/1.73  Preprocessing        : 0.32
% 4.23/1.73  Parsing              : 0.17
% 4.23/1.73  CNF conversion       : 0.02
% 4.23/1.73  Main loop            : 0.63
% 4.23/1.73  Inferencing          : 0.20
% 4.23/1.73  Reduction            : 0.18
% 4.23/1.73  Demodulation         : 0.13
% 4.23/1.73  BG Simplification    : 0.03
% 4.23/1.73  Subsumption          : 0.17
% 4.23/1.73  Abstraction          : 0.03
% 4.23/1.73  MUC search           : 0.00
% 4.23/1.73  Cooper               : 0.00
% 4.23/1.73  Total                : 0.99
% 4.23/1.73  Index Insertion      : 0.00
% 4.23/1.73  Index Deletion       : 0.00
% 4.23/1.73  Index Matching       : 0.00
% 4.23/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
