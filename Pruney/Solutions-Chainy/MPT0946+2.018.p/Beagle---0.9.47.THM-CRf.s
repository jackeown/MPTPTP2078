%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:34 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 625 expanded)
%              Number of leaves         :   34 ( 235 expanded)
%              Depth                    :   18
%              Number of atoms          :  238 (1715 expanded)
%              Number of equality atoms :   33 ( 272 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r4_wellord1 > r2_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

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

tff(f_146,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r4_wellord1(k1_wellord2(A),k1_wellord2(B))
             => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).

tff(f_47,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_132,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v2_wellord1(k1_wellord2(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).

tff(f_62,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_xboole_0(A,B)
              & A != B
              & ~ r2_xboole_0(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_119,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r4_wellord1(A,B)
           => r4_wellord1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

tff(f_136,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_117,axiom,(
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

tff(f_128,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
           => A = k1_wellord1(k1_wellord2(B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).

tff(f_102,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
       => ! [B] :
            ~ ( r2_hidden(B,k3_relat_1(A))
              & r4_wellord1(A,k2_wellord1(A,k1_wellord1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k3_relat_1(k2_wellord1(C,B)))
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_wellord1)).

tff(f_75,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_64,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_68,plain,(
    v3_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_8,plain,(
    ! [B_5,A_3] :
      ( r2_hidden(B_5,A_3)
      | B_5 = A_3
      | r2_hidden(A_3,B_5)
      | ~ v3_ordinal1(B_5)
      | ~ v3_ordinal1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_60,plain,(
    ! [A_42] :
      ( v2_wellord1(k1_wellord2(A_42))
      | ~ v3_ordinal1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_188,plain,(
    ! [B_74,A_75] :
      ( r2_xboole_0(B_74,A_75)
      | B_74 = A_75
      | r2_xboole_0(A_75,B_74)
      | ~ v3_ordinal1(B_74)
      | ~ v3_ordinal1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_255,plain,(
    ! [B_80,A_81] :
      ( r1_tarski(B_80,A_81)
      | B_80 = A_81
      | r2_xboole_0(A_81,B_80)
      | ~ v3_ordinal1(B_80)
      | ~ v3_ordinal1(A_81) ) ),
    inference(resolution,[status(thm)],[c_188,c_6])).

tff(c_263,plain,(
    ! [A_81,B_80] :
      ( r1_tarski(A_81,B_80)
      | r1_tarski(B_80,A_81)
      | B_80 = A_81
      | ~ v3_ordinal1(B_80)
      | ~ v3_ordinal1(A_81) ) ),
    inference(resolution,[status(thm)],[c_255,c_6])).

tff(c_56,plain,(
    ! [A_38] : v1_relat_1(k1_wellord2(A_38)) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_66,plain,(
    r4_wellord1(k1_wellord2('#skF_5'),k1_wellord2('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_111,plain,(
    ! [B_58,A_59] :
      ( r4_wellord1(B_58,A_59)
      | ~ r4_wellord1(A_59,B_58)
      | ~ v1_relat_1(B_58)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_113,plain,
    ( r4_wellord1(k1_wellord2('#skF_6'),k1_wellord2('#skF_5'))
    | ~ v1_relat_1(k1_wellord2('#skF_6'))
    | ~ v1_relat_1(k1_wellord2('#skF_5')) ),
    inference(resolution,[status(thm)],[c_66,c_111])).

tff(c_116,plain,(
    r4_wellord1(k1_wellord2('#skF_6'),k1_wellord2('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_56,c_113])).

tff(c_62,plain,(
    ! [B_44,A_43] :
      ( k2_wellord1(k1_wellord2(B_44),A_43) = k1_wellord2(A_43)
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_50,plain,(
    ! [A_30] :
      ( k3_relat_1(k1_wellord2(A_30)) = A_30
      | ~ v1_relat_1(k1_wellord2(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_76,plain,(
    ! [A_30] : k3_relat_1(k1_wellord2(A_30)) = A_30 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_50])).

tff(c_58,plain,(
    ! [B_41,A_39] :
      ( k1_wellord1(k1_wellord2(B_41),A_39) = A_39
      | ~ r2_hidden(A_39,B_41)
      | ~ v3_ordinal1(B_41)
      | ~ v3_ordinal1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_362,plain,(
    ! [A_92,B_93] :
      ( ~ r4_wellord1(A_92,k2_wellord1(A_92,k1_wellord1(A_92,B_93)))
      | ~ r2_hidden(B_93,k3_relat_1(A_92))
      | ~ v2_wellord1(A_92)
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_365,plain,(
    ! [B_41,A_39] :
      ( ~ r4_wellord1(k1_wellord2(B_41),k2_wellord1(k1_wellord2(B_41),A_39))
      | ~ r2_hidden(A_39,k3_relat_1(k1_wellord2(B_41)))
      | ~ v2_wellord1(k1_wellord2(B_41))
      | ~ v1_relat_1(k1_wellord2(B_41))
      | ~ r2_hidden(A_39,B_41)
      | ~ v3_ordinal1(B_41)
      | ~ v3_ordinal1(A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_362])).

tff(c_576,plain,(
    ! [B_123,A_124] :
      ( ~ r4_wellord1(k1_wellord2(B_123),k2_wellord1(k1_wellord2(B_123),A_124))
      | ~ v2_wellord1(k1_wellord2(B_123))
      | ~ r2_hidden(A_124,B_123)
      | ~ v3_ordinal1(B_123)
      | ~ v3_ordinal1(A_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_76,c_365])).

tff(c_675,plain,(
    ! [B_136,A_137] :
      ( ~ r4_wellord1(k1_wellord2(B_136),k1_wellord2(A_137))
      | ~ v2_wellord1(k1_wellord2(B_136))
      | ~ r2_hidden(A_137,B_136)
      | ~ v3_ordinal1(B_136)
      | ~ v3_ordinal1(A_137)
      | ~ r1_tarski(A_137,B_136) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_576])).

tff(c_678,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_6'))
    | ~ r2_hidden('#skF_5','#skF_6')
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5')
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_116,c_675])).

tff(c_684,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_6'))
    | ~ r2_hidden('#skF_5','#skF_6')
    | ~ r1_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_678])).

tff(c_688,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_684])).

tff(c_691,plain,
    ( r1_tarski('#skF_6','#skF_5')
    | '#skF_5' = '#skF_6'
    | ~ v3_ordinal1('#skF_6')
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_263,c_688])).

tff(c_697,plain,
    ( r1_tarski('#skF_6','#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_691])).

tff(c_698,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_697])).

tff(c_681,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_5'))
    | ~ r2_hidden('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6')
    | ~ r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_675])).

tff(c_687,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_5'))
    | ~ r2_hidden('#skF_6','#skF_5')
    | ~ r1_tarski('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_681])).

tff(c_713,plain,
    ( ~ v2_wellord1(k1_wellord2('#skF_5'))
    | ~ r2_hidden('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_698,c_687])).

tff(c_714,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_713])).

tff(c_222,plain,(
    ! [B_78,A_79] :
      ( r2_hidden(B_78,A_79)
      | B_78 = A_79
      | r2_hidden(A_79,B_78)
      | ~ v3_ordinal1(B_78)
      | ~ v3_ordinal1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_128,plain,(
    ! [A_63,C_64,B_65] :
      ( r2_hidden(A_63,k3_relat_1(C_64))
      | ~ r2_hidden(A_63,k3_relat_1(k2_wellord1(C_64,B_65)))
      | ~ v1_relat_1(C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_131,plain,(
    ! [A_63,B_44,A_43] :
      ( r2_hidden(A_63,k3_relat_1(k1_wellord2(B_44)))
      | ~ r2_hidden(A_63,k3_relat_1(k1_wellord2(A_43)))
      | ~ v1_relat_1(k1_wellord2(B_44))
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_128])).

tff(c_133,plain,(
    ! [A_63,B_44,A_43] :
      ( r2_hidden(A_63,B_44)
      | ~ r2_hidden(A_63,A_43)
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_76,c_76,c_131])).

tff(c_252,plain,(
    ! [A_79,B_44,B_78] :
      ( r2_hidden(A_79,B_44)
      | ~ r1_tarski(B_78,B_44)
      | r2_hidden(B_78,A_79)
      | B_78 = A_79
      | ~ v3_ordinal1(B_78)
      | ~ v3_ordinal1(A_79) ) ),
    inference(resolution,[status(thm)],[c_222,c_133])).

tff(c_704,plain,(
    ! [A_79] :
      ( r2_hidden(A_79,'#skF_5')
      | r2_hidden('#skF_6',A_79)
      | A_79 = '#skF_6'
      | ~ v3_ordinal1('#skF_6')
      | ~ v3_ordinal1(A_79) ) ),
    inference(resolution,[status(thm)],[c_698,c_252])).

tff(c_709,plain,(
    ! [A_79] :
      ( r2_hidden(A_79,'#skF_5')
      | r2_hidden('#skF_6',A_79)
      | A_79 = '#skF_6'
      | ~ v3_ordinal1(A_79) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_704])).

tff(c_717,plain,(
    ! [A_138] :
      ( r2_hidden(A_138,'#skF_5')
      | r2_hidden('#skF_6',A_138)
      | A_138 = '#skF_6'
      | ~ v3_ordinal1(A_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_704])).

tff(c_154,plain,(
    ! [B_72,A_73] :
      ( k1_wellord1(k1_wellord2(B_72),A_73) = A_73
      | ~ r2_hidden(A_73,B_72)
      | ~ v3_ordinal1(B_72)
      | ~ v3_ordinal1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_16,plain,(
    ! [D_20,A_9] :
      ( ~ r2_hidden(D_20,k1_wellord1(A_9,D_20))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_160,plain,(
    ! [A_73,B_72] :
      ( ~ r2_hidden(A_73,A_73)
      | ~ v1_relat_1(k1_wellord2(B_72))
      | ~ r2_hidden(A_73,B_72)
      | ~ v3_ordinal1(B_72)
      | ~ v3_ordinal1(A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_16])).

tff(c_166,plain,(
    ! [A_73,B_72] :
      ( ~ r2_hidden(A_73,A_73)
      | ~ r2_hidden(A_73,B_72)
      | ~ v3_ordinal1(B_72)
      | ~ v3_ordinal1(A_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_160])).

tff(c_731,plain,(
    ! [B_72] :
      ( ~ r2_hidden('#skF_5',B_72)
      | ~ v3_ordinal1(B_72)
      | r2_hidden('#skF_6','#skF_5')
      | '#skF_5' = '#skF_6'
      | ~ v3_ordinal1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_717,c_166])).

tff(c_756,plain,(
    ! [B_72] :
      ( ~ r2_hidden('#skF_5',B_72)
      | ~ v3_ordinal1(B_72)
      | r2_hidden('#skF_6','#skF_5')
      | '#skF_5' = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_731])).

tff(c_760,plain,(
    ! [B_139] :
      ( ~ r2_hidden('#skF_5',B_139)
      | ~ v3_ordinal1(B_139) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_714,c_756])).

tff(c_764,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | '#skF_5' = '#skF_6'
    | ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_709,c_760])).

tff(c_779,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_764])).

tff(c_781,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_714,c_779])).

tff(c_782,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_713])).

tff(c_814,plain,(
    ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_782])).

tff(c_818,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_814])).

tff(c_819,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | ~ v2_wellord1(k1_wellord2('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_684])).

tff(c_829,plain,(
    ~ v2_wellord1(k1_wellord2('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_819])).

tff(c_833,plain,(
    ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_829])).

tff(c_837,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_833])).

tff(c_838,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_819])).

tff(c_842,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_6','#skF_5')
    | ~ v3_ordinal1('#skF_5')
    | ~ v3_ordinal1('#skF_6') ),
    inference(resolution,[status(thm)],[c_8,c_838])).

tff(c_848,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70,c_842])).

tff(c_849,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_848])).

tff(c_820,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_684])).

tff(c_886,plain,(
    ! [B_146] :
      ( r2_hidden('#skF_6',B_146)
      | ~ r1_tarski('#skF_5',B_146) ) ),
    inference(resolution,[status(thm)],[c_849,c_133])).

tff(c_897,plain,(
    ! [B_72] :
      ( ~ r2_hidden('#skF_6',B_72)
      | ~ v3_ordinal1(B_72)
      | ~ v3_ordinal1('#skF_6')
      | ~ r1_tarski('#skF_5','#skF_6') ) ),
    inference(resolution,[status(thm)],[c_886,c_166])).

tff(c_921,plain,(
    ! [B_147] :
      ( ~ r2_hidden('#skF_6',B_147)
      | ~ v3_ordinal1(B_147) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_820,c_68,c_897])).

tff(c_927,plain,(
    ~ v3_ordinal1('#skF_5') ),
    inference(resolution,[status(thm)],[c_849,c_921])).

tff(c_944,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_927])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:51:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.53  
% 3.30/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.53  %$ r4_wellord1 > r2_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > v2_wellord1 > v1_relat_1 > k4_tarski > k2_wellord1 > k1_wellord1 > #nlpp > k3_relat_1 > k1_wellord2 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 3.30/1.53  
% 3.30/1.53  %Foreground sorts:
% 3.30/1.53  
% 3.30/1.53  
% 3.30/1.53  %Background operators:
% 3.30/1.53  
% 3.30/1.53  
% 3.30/1.53  %Foreground operators:
% 3.30/1.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.30/1.53  tff(r4_wellord1, type, r4_wellord1: ($i * $i) > $o).
% 3.30/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.30/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.30/1.53  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.30/1.53  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.30/1.53  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.30/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.30/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.30/1.53  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 3.30/1.53  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 3.30/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.30/1.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.30/1.53  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 3.30/1.53  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.30/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.30/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.30/1.53  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 3.30/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.30/1.53  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 3.30/1.53  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.30/1.53  
% 3.30/1.55  tff(f_146, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r4_wellord1(k1_wellord2(A), k1_wellord2(B)) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_wellord2)).
% 3.30/1.55  tff(f_47, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_ordinal1)).
% 3.30/1.55  tff(f_132, axiom, (![A]: (v3_ordinal1(A) => v2_wellord1(k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_wellord2)).
% 3.30/1.55  tff(f_62, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_xboole_0(A, B) & ~(A = B)) & ~r2_xboole_0(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_ordinal1)).
% 3.30/1.55  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.30/1.55  tff(f_119, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 3.30/1.55  tff(f_92, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r4_wellord1(A, B) => r4_wellord1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_wellord1)).
% 3.30/1.55  tff(f_136, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_wellord2)).
% 3.30/1.55  tff(f_117, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord2)).
% 3.30/1.55  tff(f_128, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) => (A = k1_wellord1(k1_wellord2(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_wellord2)).
% 3.30/1.55  tff(f_102, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) => (![B]: ~(r2_hidden(B, k3_relat_1(A)) & r4_wellord1(A, k2_wellord1(A, k1_wellord1(A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_wellord1)).
% 3.30/1.55  tff(f_83, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k3_relat_1(k2_wellord1(C, B))) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_wellord1)).
% 3.30/1.55  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k1_wellord1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (~(D = B) & r2_hidden(k4_tarski(D, B), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord1)).
% 3.30/1.55  tff(c_70, plain, (v3_ordinal1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.30/1.55  tff(c_64, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.30/1.55  tff(c_68, plain, (v3_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.30/1.55  tff(c_8, plain, (![B_5, A_3]: (r2_hidden(B_5, A_3) | B_5=A_3 | r2_hidden(A_3, B_5) | ~v3_ordinal1(B_5) | ~v3_ordinal1(A_3))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.30/1.55  tff(c_60, plain, (![A_42]: (v2_wellord1(k1_wellord2(A_42)) | ~v3_ordinal1(A_42))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.30/1.55  tff(c_188, plain, (![B_74, A_75]: (r2_xboole_0(B_74, A_75) | B_74=A_75 | r2_xboole_0(A_75, B_74) | ~v3_ordinal1(B_74) | ~v3_ordinal1(A_75))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.30/1.55  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.30/1.55  tff(c_255, plain, (![B_80, A_81]: (r1_tarski(B_80, A_81) | B_80=A_81 | r2_xboole_0(A_81, B_80) | ~v3_ordinal1(B_80) | ~v3_ordinal1(A_81))), inference(resolution, [status(thm)], [c_188, c_6])).
% 3.30/1.55  tff(c_263, plain, (![A_81, B_80]: (r1_tarski(A_81, B_80) | r1_tarski(B_80, A_81) | B_80=A_81 | ~v3_ordinal1(B_80) | ~v3_ordinal1(A_81))), inference(resolution, [status(thm)], [c_255, c_6])).
% 3.30/1.55  tff(c_56, plain, (![A_38]: (v1_relat_1(k1_wellord2(A_38)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.30/1.55  tff(c_66, plain, (r4_wellord1(k1_wellord2('#skF_5'), k1_wellord2('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.30/1.55  tff(c_111, plain, (![B_58, A_59]: (r4_wellord1(B_58, A_59) | ~r4_wellord1(A_59, B_58) | ~v1_relat_1(B_58) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.30/1.55  tff(c_113, plain, (r4_wellord1(k1_wellord2('#skF_6'), k1_wellord2('#skF_5')) | ~v1_relat_1(k1_wellord2('#skF_6')) | ~v1_relat_1(k1_wellord2('#skF_5'))), inference(resolution, [status(thm)], [c_66, c_111])).
% 3.30/1.55  tff(c_116, plain, (r4_wellord1(k1_wellord2('#skF_6'), k1_wellord2('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_56, c_113])).
% 3.30/1.55  tff(c_62, plain, (![B_44, A_43]: (k2_wellord1(k1_wellord2(B_44), A_43)=k1_wellord2(A_43) | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.30/1.55  tff(c_50, plain, (![A_30]: (k3_relat_1(k1_wellord2(A_30))=A_30 | ~v1_relat_1(k1_wellord2(A_30)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.30/1.55  tff(c_76, plain, (![A_30]: (k3_relat_1(k1_wellord2(A_30))=A_30)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_50])).
% 3.30/1.55  tff(c_58, plain, (![B_41, A_39]: (k1_wellord1(k1_wellord2(B_41), A_39)=A_39 | ~r2_hidden(A_39, B_41) | ~v3_ordinal1(B_41) | ~v3_ordinal1(A_39))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.30/1.55  tff(c_362, plain, (![A_92, B_93]: (~r4_wellord1(A_92, k2_wellord1(A_92, k1_wellord1(A_92, B_93))) | ~r2_hidden(B_93, k3_relat_1(A_92)) | ~v2_wellord1(A_92) | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.30/1.55  tff(c_365, plain, (![B_41, A_39]: (~r4_wellord1(k1_wellord2(B_41), k2_wellord1(k1_wellord2(B_41), A_39)) | ~r2_hidden(A_39, k3_relat_1(k1_wellord2(B_41))) | ~v2_wellord1(k1_wellord2(B_41)) | ~v1_relat_1(k1_wellord2(B_41)) | ~r2_hidden(A_39, B_41) | ~v3_ordinal1(B_41) | ~v3_ordinal1(A_39))), inference(superposition, [status(thm), theory('equality')], [c_58, c_362])).
% 3.30/1.55  tff(c_576, plain, (![B_123, A_124]: (~r4_wellord1(k1_wellord2(B_123), k2_wellord1(k1_wellord2(B_123), A_124)) | ~v2_wellord1(k1_wellord2(B_123)) | ~r2_hidden(A_124, B_123) | ~v3_ordinal1(B_123) | ~v3_ordinal1(A_124))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_76, c_365])).
% 3.30/1.55  tff(c_675, plain, (![B_136, A_137]: (~r4_wellord1(k1_wellord2(B_136), k1_wellord2(A_137)) | ~v2_wellord1(k1_wellord2(B_136)) | ~r2_hidden(A_137, B_136) | ~v3_ordinal1(B_136) | ~v3_ordinal1(A_137) | ~r1_tarski(A_137, B_136))), inference(superposition, [status(thm), theory('equality')], [c_62, c_576])).
% 3.30/1.55  tff(c_678, plain, (~v2_wellord1(k1_wellord2('#skF_6')) | ~r2_hidden('#skF_5', '#skF_6') | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5') | ~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_116, c_675])).
% 3.30/1.55  tff(c_684, plain, (~v2_wellord1(k1_wellord2('#skF_6')) | ~r2_hidden('#skF_5', '#skF_6') | ~r1_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_678])).
% 3.30/1.55  tff(c_688, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_684])).
% 3.30/1.55  tff(c_691, plain, (r1_tarski('#skF_6', '#skF_5') | '#skF_5'='#skF_6' | ~v3_ordinal1('#skF_6') | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_263, c_688])).
% 3.30/1.55  tff(c_697, plain, (r1_tarski('#skF_6', '#skF_5') | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_691])).
% 3.30/1.55  tff(c_698, plain, (r1_tarski('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_64, c_697])).
% 3.30/1.55  tff(c_681, plain, (~v2_wellord1(k1_wellord2('#skF_5')) | ~r2_hidden('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6') | ~r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_66, c_675])).
% 3.30/1.55  tff(c_687, plain, (~v2_wellord1(k1_wellord2('#skF_5')) | ~r2_hidden('#skF_6', '#skF_5') | ~r1_tarski('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_70, c_681])).
% 3.30/1.55  tff(c_713, plain, (~v2_wellord1(k1_wellord2('#skF_5')) | ~r2_hidden('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_698, c_687])).
% 3.30/1.55  tff(c_714, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_713])).
% 3.30/1.55  tff(c_222, plain, (![B_78, A_79]: (r2_hidden(B_78, A_79) | B_78=A_79 | r2_hidden(A_79, B_78) | ~v3_ordinal1(B_78) | ~v3_ordinal1(A_79))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.30/1.55  tff(c_128, plain, (![A_63, C_64, B_65]: (r2_hidden(A_63, k3_relat_1(C_64)) | ~r2_hidden(A_63, k3_relat_1(k2_wellord1(C_64, B_65))) | ~v1_relat_1(C_64))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.30/1.55  tff(c_131, plain, (![A_63, B_44, A_43]: (r2_hidden(A_63, k3_relat_1(k1_wellord2(B_44))) | ~r2_hidden(A_63, k3_relat_1(k1_wellord2(A_43))) | ~v1_relat_1(k1_wellord2(B_44)) | ~r1_tarski(A_43, B_44))), inference(superposition, [status(thm), theory('equality')], [c_62, c_128])).
% 3.30/1.55  tff(c_133, plain, (![A_63, B_44, A_43]: (r2_hidden(A_63, B_44) | ~r2_hidden(A_63, A_43) | ~r1_tarski(A_43, B_44))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_76, c_76, c_131])).
% 3.30/1.55  tff(c_252, plain, (![A_79, B_44, B_78]: (r2_hidden(A_79, B_44) | ~r1_tarski(B_78, B_44) | r2_hidden(B_78, A_79) | B_78=A_79 | ~v3_ordinal1(B_78) | ~v3_ordinal1(A_79))), inference(resolution, [status(thm)], [c_222, c_133])).
% 3.30/1.55  tff(c_704, plain, (![A_79]: (r2_hidden(A_79, '#skF_5') | r2_hidden('#skF_6', A_79) | A_79='#skF_6' | ~v3_ordinal1('#skF_6') | ~v3_ordinal1(A_79))), inference(resolution, [status(thm)], [c_698, c_252])).
% 3.30/1.55  tff(c_709, plain, (![A_79]: (r2_hidden(A_79, '#skF_5') | r2_hidden('#skF_6', A_79) | A_79='#skF_6' | ~v3_ordinal1(A_79))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_704])).
% 3.30/1.55  tff(c_717, plain, (![A_138]: (r2_hidden(A_138, '#skF_5') | r2_hidden('#skF_6', A_138) | A_138='#skF_6' | ~v3_ordinal1(A_138))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_704])).
% 3.30/1.55  tff(c_154, plain, (![B_72, A_73]: (k1_wellord1(k1_wellord2(B_72), A_73)=A_73 | ~r2_hidden(A_73, B_72) | ~v3_ordinal1(B_72) | ~v3_ordinal1(A_73))), inference(cnfTransformation, [status(thm)], [f_128])).
% 3.30/1.55  tff(c_16, plain, (![D_20, A_9]: (~r2_hidden(D_20, k1_wellord1(A_9, D_20)) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.30/1.55  tff(c_160, plain, (![A_73, B_72]: (~r2_hidden(A_73, A_73) | ~v1_relat_1(k1_wellord2(B_72)) | ~r2_hidden(A_73, B_72) | ~v3_ordinal1(B_72) | ~v3_ordinal1(A_73))), inference(superposition, [status(thm), theory('equality')], [c_154, c_16])).
% 3.30/1.55  tff(c_166, plain, (![A_73, B_72]: (~r2_hidden(A_73, A_73) | ~r2_hidden(A_73, B_72) | ~v3_ordinal1(B_72) | ~v3_ordinal1(A_73))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_160])).
% 3.30/1.55  tff(c_731, plain, (![B_72]: (~r2_hidden('#skF_5', B_72) | ~v3_ordinal1(B_72) | r2_hidden('#skF_6', '#skF_5') | '#skF_5'='#skF_6' | ~v3_ordinal1('#skF_5'))), inference(resolution, [status(thm)], [c_717, c_166])).
% 3.30/1.55  tff(c_756, plain, (![B_72]: (~r2_hidden('#skF_5', B_72) | ~v3_ordinal1(B_72) | r2_hidden('#skF_6', '#skF_5') | '#skF_5'='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_731])).
% 3.30/1.55  tff(c_760, plain, (![B_139]: (~r2_hidden('#skF_5', B_139) | ~v3_ordinal1(B_139))), inference(negUnitSimplification, [status(thm)], [c_64, c_714, c_756])).
% 3.30/1.55  tff(c_764, plain, (r2_hidden('#skF_6', '#skF_5') | '#skF_5'='#skF_6' | ~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_709, c_760])).
% 3.30/1.55  tff(c_779, plain, (r2_hidden('#skF_6', '#skF_5') | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_764])).
% 3.30/1.55  tff(c_781, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_714, c_779])).
% 3.30/1.55  tff(c_782, plain, (~v2_wellord1(k1_wellord2('#skF_5'))), inference(splitRight, [status(thm)], [c_713])).
% 3.30/1.55  tff(c_814, plain, (~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_60, c_782])).
% 3.30/1.55  tff(c_818, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_814])).
% 3.30/1.55  tff(c_819, plain, (~r2_hidden('#skF_5', '#skF_6') | ~v2_wellord1(k1_wellord2('#skF_6'))), inference(splitRight, [status(thm)], [c_684])).
% 3.30/1.55  tff(c_829, plain, (~v2_wellord1(k1_wellord2('#skF_6'))), inference(splitLeft, [status(thm)], [c_819])).
% 3.30/1.55  tff(c_833, plain, (~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_60, c_829])).
% 3.30/1.55  tff(c_837, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_833])).
% 3.30/1.55  tff(c_838, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_819])).
% 3.30/1.55  tff(c_842, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_6', '#skF_5') | ~v3_ordinal1('#skF_5') | ~v3_ordinal1('#skF_6')), inference(resolution, [status(thm)], [c_8, c_838])).
% 3.30/1.55  tff(c_848, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_70, c_842])).
% 3.30/1.55  tff(c_849, plain, (r2_hidden('#skF_6', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_64, c_848])).
% 3.30/1.55  tff(c_820, plain, (r1_tarski('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_684])).
% 3.30/1.55  tff(c_886, plain, (![B_146]: (r2_hidden('#skF_6', B_146) | ~r1_tarski('#skF_5', B_146))), inference(resolution, [status(thm)], [c_849, c_133])).
% 3.30/1.55  tff(c_897, plain, (![B_72]: (~r2_hidden('#skF_6', B_72) | ~v3_ordinal1(B_72) | ~v3_ordinal1('#skF_6') | ~r1_tarski('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_886, c_166])).
% 3.30/1.55  tff(c_921, plain, (![B_147]: (~r2_hidden('#skF_6', B_147) | ~v3_ordinal1(B_147))), inference(demodulation, [status(thm), theory('equality')], [c_820, c_68, c_897])).
% 3.30/1.55  tff(c_927, plain, (~v3_ordinal1('#skF_5')), inference(resolution, [status(thm)], [c_849, c_921])).
% 3.30/1.55  tff(c_944, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_927])).
% 3.30/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.55  
% 3.30/1.55  Inference rules
% 3.30/1.55  ----------------------
% 3.30/1.55  #Ref     : 0
% 3.30/1.55  #Sup     : 152
% 3.30/1.55  #Fact    : 6
% 3.30/1.55  #Define  : 0
% 3.30/1.55  #Split   : 4
% 3.30/1.55  #Chain   : 0
% 3.30/1.55  #Close   : 0
% 3.30/1.55  
% 3.30/1.55  Ordering : KBO
% 3.30/1.55  
% 3.30/1.55  Simplification rules
% 3.30/1.55  ----------------------
% 3.30/1.55  #Subsume      : 2
% 3.30/1.55  #Demod        : 82
% 3.30/1.55  #Tautology    : 36
% 3.30/1.55  #SimpNegUnit  : 8
% 3.30/1.55  #BackRed      : 0
% 3.30/1.55  
% 3.30/1.55  #Partial instantiations: 0
% 3.30/1.55  #Strategies tried      : 1
% 3.30/1.55  
% 3.30/1.55  Timing (in seconds)
% 3.30/1.55  ----------------------
% 3.30/1.55  Preprocessing        : 0.36
% 3.30/1.55  Parsing              : 0.18
% 3.30/1.55  CNF conversion       : 0.03
% 3.30/1.56  Main loop            : 0.38
% 3.30/1.56  Inferencing          : 0.14
% 3.30/1.56  Reduction            : 0.10
% 3.30/1.56  Demodulation         : 0.07
% 3.30/1.56  BG Simplification    : 0.03
% 3.30/1.56  Subsumption          : 0.08
% 3.30/1.56  Abstraction          : 0.02
% 3.30/1.56  MUC search           : 0.00
% 3.30/1.56  Cooper               : 0.00
% 3.30/1.56  Total                : 0.77
% 3.30/1.56  Index Insertion      : 0.00
% 3.30/1.56  Index Deletion       : 0.00
% 3.30/1.56  Index Matching       : 0.00
% 3.30/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
