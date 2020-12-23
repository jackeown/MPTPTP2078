%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:09 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 409 expanded)
%              Number of leaves         :   26 ( 137 expanded)
%              Depth                    :   11
%              Number of atoms          :  169 (1017 expanded)
%              Number of equality atoms :   88 ( 593 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_80,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_67,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_46,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_38,plain,(
    ! [A_18,B_22] :
      ( k1_relat_1('#skF_3'(A_18,B_22)) = A_18
      | k1_xboole_0 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_40,plain,(
    ! [A_18,B_22] :
      ( v1_funct_1('#skF_3'(A_18,B_22))
      | k1_xboole_0 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_42,plain,(
    ! [A_18,B_22] :
      ( v1_relat_1('#skF_3'(A_18,B_22))
      | k1_xboole_0 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(k1_tarski(A_9),B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_300,plain,(
    ! [A_67,B_68] :
      ( k2_relat_1('#skF_3'(A_67,B_68)) = k1_tarski(B_68)
      | k1_xboole_0 = A_67 ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_44,plain,(
    ! [C_25] :
      ( ~ r1_tarski(k2_relat_1(C_25),'#skF_4')
      | k1_relat_1(C_25) != '#skF_5'
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_365,plain,(
    ! [B_81,A_82] :
      ( ~ r1_tarski(k1_tarski(B_81),'#skF_4')
      | k1_relat_1('#skF_3'(A_82,B_81)) != '#skF_5'
      | ~ v1_funct_1('#skF_3'(A_82,B_81))
      | ~ v1_relat_1('#skF_3'(A_82,B_81))
      | k1_xboole_0 = A_82 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_44])).

tff(c_528,plain,(
    ! [A_103,A_104] :
      ( k1_relat_1('#skF_3'(A_103,A_104)) != '#skF_5'
      | ~ v1_funct_1('#skF_3'(A_103,A_104))
      | ~ v1_relat_1('#skF_3'(A_103,A_104))
      | k1_xboole_0 = A_103
      | ~ r2_hidden(A_104,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_365])).

tff(c_609,plain,(
    ! [A_118,B_119] :
      ( k1_relat_1('#skF_3'(A_118,B_119)) != '#skF_5'
      | ~ v1_funct_1('#skF_3'(A_118,B_119))
      | ~ r2_hidden(B_119,'#skF_4')
      | k1_xboole_0 = A_118 ) ),
    inference(resolution,[status(thm)],[c_42,c_528])).

tff(c_614,plain,(
    ! [A_120,B_121] :
      ( k1_relat_1('#skF_3'(A_120,B_121)) != '#skF_5'
      | ~ r2_hidden(B_121,'#skF_4')
      | k1_xboole_0 = A_120 ) ),
    inference(resolution,[status(thm)],[c_40,c_609])).

tff(c_617,plain,(
    ! [A_18,B_22] :
      ( A_18 != '#skF_5'
      | ~ r2_hidden(B_22,'#skF_4')
      | k1_xboole_0 = A_18
      | k1_xboole_0 = A_18 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_614])).

tff(c_624,plain,(
    ! [B_124] : ~ r2_hidden(B_124,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_617])).

tff(c_635,plain,(
    ! [B_125] : r1_tarski('#skF_4',B_125) ),
    inference(resolution,[status(thm)],[c_6,c_624])).

tff(c_14,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_242,plain,(
    ! [B_59,A_60] :
      ( B_59 = A_60
      | ~ r1_tarski(B_59,A_60)
      | ~ r1_tarski(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_254,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_14,c_242])).

tff(c_654,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_635,c_254])).

tff(c_667,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_654])).

tff(c_669,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_617])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_70,plain,(
    ! [C_31] :
      ( ~ r1_tarski(k2_relat_1(C_31),'#skF_4')
      | k1_relat_1(C_31) != '#skF_5'
      | ~ v1_funct_1(C_31)
      | ~ v1_relat_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_73,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_4')
    | k1_relat_1(k1_xboole_0) != '#skF_5'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_70])).

tff(c_75,plain,
    ( k1_xboole_0 != '#skF_5'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_14,c_73])).

tff(c_78,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_30,plain,(
    ! [A_12] : k1_relat_1('#skF_2'(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_34,plain,(
    ! [A_12] : v1_relat_1('#skF_2'(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_105,plain,(
    ! [A_42] :
      ( k1_relat_1(A_42) != k1_xboole_0
      | k1_xboole_0 = A_42
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_111,plain,(
    ! [A_12] :
      ( k1_relat_1('#skF_2'(A_12)) != k1_xboole_0
      | '#skF_2'(A_12) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_105])).

tff(c_121,plain,(
    ! [A_45] :
      ( k1_xboole_0 != A_45
      | '#skF_2'(A_45) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_111])).

tff(c_131,plain,(
    ! [A_45] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_45 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_34])).

tff(c_137,plain,(
    ! [A_45] : k1_xboole_0 != A_45 ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_131])).

tff(c_147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_20])).

tff(c_148,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_150,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_704,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_669,c_150])).

tff(c_706,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_705,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_707,plain,(
    ~ v1_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_706,c_705])).

tff(c_26,plain,(
    ! [A_11] :
      ( k1_relat_1(A_11) != k1_xboole_0
      | k1_xboole_0 = A_11
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_753,plain,(
    ! [A_134] :
      ( k1_relat_1(A_134) != '#skF_5'
      | A_134 = '#skF_5'
      | ~ v1_relat_1(A_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_706,c_706,c_26])).

tff(c_762,plain,(
    ! [A_12] :
      ( k1_relat_1('#skF_2'(A_12)) != '#skF_5'
      | '#skF_2'(A_12) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_34,c_753])).

tff(c_771,plain,(
    ! [A_135] :
      ( A_135 != '#skF_5'
      | '#skF_2'(A_135) = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_762])).

tff(c_32,plain,(
    ! [A_12] : v1_funct_1('#skF_2'(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_779,plain,(
    ! [A_135] :
      ( v1_funct_1('#skF_5')
      | A_135 != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_771,c_32])).

tff(c_787,plain,(
    ! [A_135] : A_135 != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_707,c_779])).

tff(c_713,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_706,c_706,c_22])).

tff(c_797,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_787,c_713])).

tff(c_799,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_798,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_808,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_799,c_798])).

tff(c_801,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_798,c_798,c_22])).

tff(c_820,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_808,c_801])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_800,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_798,c_798,c_20])).

tff(c_825,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_808,c_800])).

tff(c_854,plain,(
    ! [C_144] :
      ( ~ r1_tarski(k2_relat_1(C_144),'#skF_4')
      | k1_relat_1(C_144) != '#skF_4'
      | ~ v1_funct_1(C_144)
      | ~ v1_relat_1(C_144) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_44])).

tff(c_857,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | k1_relat_1('#skF_4') != '#skF_4'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_825,c_854])).

tff(c_859,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_820,c_12,c_857])).

tff(c_860,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_859])).

tff(c_844,plain,(
    ! [A_143] :
      ( k1_relat_1(A_143) != '#skF_4'
      | A_143 = '#skF_4'
      | ~ v1_relat_1(A_143) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_799,c_799,c_26])).

tff(c_850,plain,(
    ! [A_12] :
      ( k1_relat_1('#skF_2'(A_12)) != '#skF_4'
      | '#skF_2'(A_12) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_34,c_844])).

tff(c_862,plain,(
    ! [A_145] :
      ( A_145 != '#skF_4'
      | '#skF_2'(A_145) = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_850])).

tff(c_872,plain,(
    ! [A_145] :
      ( v1_relat_1('#skF_4')
      | A_145 != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_862,c_34])).

tff(c_878,plain,(
    ! [A_145] : A_145 != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_860,c_872])).

tff(c_888,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_878,c_825])).

tff(c_889,plain,(
    ~ v1_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_859])).

tff(c_915,plain,(
    ! [A_147] :
      ( A_147 != '#skF_4'
      | '#skF_2'(A_147) = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_850])).

tff(c_923,plain,(
    ! [A_147] :
      ( v1_funct_1('#skF_4')
      | A_147 != '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_915,c_32])).

tff(c_931,plain,(
    ! [A_147] : A_147 != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_889,c_923])).

tff(c_943,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_931,c_825])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n025.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:55:50 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.42  
% 2.86/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.43  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_4 > #skF_1
% 2.86/1.43  
% 2.86/1.43  %Foreground sorts:
% 2.86/1.43  
% 2.86/1.43  
% 2.86/1.43  %Background operators:
% 2.86/1.43  
% 2.86/1.43  
% 2.86/1.43  %Foreground operators:
% 2.86/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.86/1.43  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.86/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.86/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.86/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.86/1.43  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.86/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.86/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.86/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.86/1.43  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.86/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.86/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.86/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.86/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.86/1.43  
% 2.86/1.45  tff(f_98, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 2.86/1.45  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.86/1.45  tff(f_80, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 2.86/1.45  tff(f_44, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.86/1.45  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.86/1.45  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.86/1.45  tff(f_47, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.86/1.45  tff(f_67, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 2.86/1.45  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 2.86/1.45  tff(c_46, plain, (k1_xboole_0='#skF_5' | k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.86/1.45  tff(c_60, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_46])).
% 2.86/1.45  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.86/1.45  tff(c_38, plain, (![A_18, B_22]: (k1_relat_1('#skF_3'(A_18, B_22))=A_18 | k1_xboole_0=A_18)), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.86/1.45  tff(c_40, plain, (![A_18, B_22]: (v1_funct_1('#skF_3'(A_18, B_22)) | k1_xboole_0=A_18)), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.86/1.45  tff(c_42, plain, (![A_18, B_22]: (v1_relat_1('#skF_3'(A_18, B_22)) | k1_xboole_0=A_18)), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.86/1.45  tff(c_18, plain, (![A_9, B_10]: (r1_tarski(k1_tarski(A_9), B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.86/1.45  tff(c_300, plain, (![A_67, B_68]: (k2_relat_1('#skF_3'(A_67, B_68))=k1_tarski(B_68) | k1_xboole_0=A_67)), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.86/1.45  tff(c_44, plain, (![C_25]: (~r1_tarski(k2_relat_1(C_25), '#skF_4') | k1_relat_1(C_25)!='#skF_5' | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.86/1.45  tff(c_365, plain, (![B_81, A_82]: (~r1_tarski(k1_tarski(B_81), '#skF_4') | k1_relat_1('#skF_3'(A_82, B_81))!='#skF_5' | ~v1_funct_1('#skF_3'(A_82, B_81)) | ~v1_relat_1('#skF_3'(A_82, B_81)) | k1_xboole_0=A_82)), inference(superposition, [status(thm), theory('equality')], [c_300, c_44])).
% 2.86/1.45  tff(c_528, plain, (![A_103, A_104]: (k1_relat_1('#skF_3'(A_103, A_104))!='#skF_5' | ~v1_funct_1('#skF_3'(A_103, A_104)) | ~v1_relat_1('#skF_3'(A_103, A_104)) | k1_xboole_0=A_103 | ~r2_hidden(A_104, '#skF_4'))), inference(resolution, [status(thm)], [c_18, c_365])).
% 2.86/1.45  tff(c_609, plain, (![A_118, B_119]: (k1_relat_1('#skF_3'(A_118, B_119))!='#skF_5' | ~v1_funct_1('#skF_3'(A_118, B_119)) | ~r2_hidden(B_119, '#skF_4') | k1_xboole_0=A_118)), inference(resolution, [status(thm)], [c_42, c_528])).
% 2.86/1.45  tff(c_614, plain, (![A_120, B_121]: (k1_relat_1('#skF_3'(A_120, B_121))!='#skF_5' | ~r2_hidden(B_121, '#skF_4') | k1_xboole_0=A_120)), inference(resolution, [status(thm)], [c_40, c_609])).
% 2.86/1.45  tff(c_617, plain, (![A_18, B_22]: (A_18!='#skF_5' | ~r2_hidden(B_22, '#skF_4') | k1_xboole_0=A_18 | k1_xboole_0=A_18)), inference(superposition, [status(thm), theory('equality')], [c_38, c_614])).
% 2.86/1.45  tff(c_624, plain, (![B_124]: (~r2_hidden(B_124, '#skF_4'))), inference(splitLeft, [status(thm)], [c_617])).
% 2.86/1.45  tff(c_635, plain, (![B_125]: (r1_tarski('#skF_4', B_125))), inference(resolution, [status(thm)], [c_6, c_624])).
% 2.86/1.45  tff(c_14, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.86/1.45  tff(c_242, plain, (![B_59, A_60]: (B_59=A_60 | ~r1_tarski(B_59, A_60) | ~r1_tarski(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.86/1.45  tff(c_254, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_242])).
% 2.86/1.45  tff(c_654, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_635, c_254])).
% 2.86/1.45  tff(c_667, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_654])).
% 2.86/1.45  tff(c_669, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_617])).
% 2.86/1.45  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.86/1.45  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.86/1.45  tff(c_70, plain, (![C_31]: (~r1_tarski(k2_relat_1(C_31), '#skF_4') | k1_relat_1(C_31)!='#skF_5' | ~v1_funct_1(C_31) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.86/1.45  tff(c_73, plain, (~r1_tarski(k1_xboole_0, '#skF_4') | k1_relat_1(k1_xboole_0)!='#skF_5' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_20, c_70])).
% 2.86/1.45  tff(c_75, plain, (k1_xboole_0!='#skF_5' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_14, c_73])).
% 2.86/1.45  tff(c_78, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_75])).
% 2.86/1.45  tff(c_30, plain, (![A_12]: (k1_relat_1('#skF_2'(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.86/1.45  tff(c_34, plain, (![A_12]: (v1_relat_1('#skF_2'(A_12)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.86/1.45  tff(c_105, plain, (![A_42]: (k1_relat_1(A_42)!=k1_xboole_0 | k1_xboole_0=A_42 | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.86/1.45  tff(c_111, plain, (![A_12]: (k1_relat_1('#skF_2'(A_12))!=k1_xboole_0 | '#skF_2'(A_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_105])).
% 2.86/1.45  tff(c_121, plain, (![A_45]: (k1_xboole_0!=A_45 | '#skF_2'(A_45)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_111])).
% 2.86/1.45  tff(c_131, plain, (![A_45]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_45)), inference(superposition, [status(thm), theory('equality')], [c_121, c_34])).
% 2.86/1.45  tff(c_137, plain, (![A_45]: (k1_xboole_0!=A_45)), inference(negUnitSimplification, [status(thm)], [c_78, c_131])).
% 2.86/1.45  tff(c_147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_137, c_20])).
% 2.86/1.45  tff(c_148, plain, (~v1_funct_1(k1_xboole_0) | k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_75])).
% 2.86/1.45  tff(c_150, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_148])).
% 2.86/1.45  tff(c_704, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_669, c_150])).
% 2.86/1.45  tff(c_706, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_148])).
% 2.86/1.45  tff(c_705, plain, (~v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_148])).
% 2.86/1.45  tff(c_707, plain, (~v1_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_706, c_705])).
% 2.86/1.45  tff(c_26, plain, (![A_11]: (k1_relat_1(A_11)!=k1_xboole_0 | k1_xboole_0=A_11 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.86/1.45  tff(c_753, plain, (![A_134]: (k1_relat_1(A_134)!='#skF_5' | A_134='#skF_5' | ~v1_relat_1(A_134))), inference(demodulation, [status(thm), theory('equality')], [c_706, c_706, c_26])).
% 2.86/1.45  tff(c_762, plain, (![A_12]: (k1_relat_1('#skF_2'(A_12))!='#skF_5' | '#skF_2'(A_12)='#skF_5')), inference(resolution, [status(thm)], [c_34, c_753])).
% 2.86/1.45  tff(c_771, plain, (![A_135]: (A_135!='#skF_5' | '#skF_2'(A_135)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_762])).
% 2.86/1.45  tff(c_32, plain, (![A_12]: (v1_funct_1('#skF_2'(A_12)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.86/1.45  tff(c_779, plain, (![A_135]: (v1_funct_1('#skF_5') | A_135!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_771, c_32])).
% 2.86/1.45  tff(c_787, plain, (![A_135]: (A_135!='#skF_5')), inference(negUnitSimplification, [status(thm)], [c_707, c_779])).
% 2.86/1.45  tff(c_713, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_706, c_706, c_22])).
% 2.86/1.45  tff(c_797, plain, $false, inference(negUnitSimplification, [status(thm)], [c_787, c_713])).
% 2.86/1.45  tff(c_799, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_46])).
% 2.86/1.45  tff(c_798, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_46])).
% 2.86/1.45  tff(c_808, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_799, c_798])).
% 2.86/1.45  tff(c_801, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_798, c_798, c_22])).
% 2.86/1.45  tff(c_820, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_808, c_808, c_801])).
% 2.86/1.45  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.86/1.45  tff(c_800, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_798, c_798, c_20])).
% 2.86/1.45  tff(c_825, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_808, c_808, c_800])).
% 2.86/1.45  tff(c_854, plain, (![C_144]: (~r1_tarski(k2_relat_1(C_144), '#skF_4') | k1_relat_1(C_144)!='#skF_4' | ~v1_funct_1(C_144) | ~v1_relat_1(C_144))), inference(demodulation, [status(thm), theory('equality')], [c_808, c_44])).
% 2.86/1.45  tff(c_857, plain, (~r1_tarski('#skF_4', '#skF_4') | k1_relat_1('#skF_4')!='#skF_4' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_825, c_854])).
% 2.86/1.45  tff(c_859, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_820, c_12, c_857])).
% 2.86/1.45  tff(c_860, plain, (~v1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_859])).
% 2.86/1.45  tff(c_844, plain, (![A_143]: (k1_relat_1(A_143)!='#skF_4' | A_143='#skF_4' | ~v1_relat_1(A_143))), inference(demodulation, [status(thm), theory('equality')], [c_799, c_799, c_26])).
% 2.86/1.45  tff(c_850, plain, (![A_12]: (k1_relat_1('#skF_2'(A_12))!='#skF_4' | '#skF_2'(A_12)='#skF_4')), inference(resolution, [status(thm)], [c_34, c_844])).
% 2.86/1.45  tff(c_862, plain, (![A_145]: (A_145!='#skF_4' | '#skF_2'(A_145)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_850])).
% 2.86/1.45  tff(c_872, plain, (![A_145]: (v1_relat_1('#skF_4') | A_145!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_862, c_34])).
% 2.86/1.45  tff(c_878, plain, (![A_145]: (A_145!='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_860, c_872])).
% 2.86/1.45  tff(c_888, plain, $false, inference(negUnitSimplification, [status(thm)], [c_878, c_825])).
% 2.86/1.45  tff(c_889, plain, (~v1_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_859])).
% 2.86/1.45  tff(c_915, plain, (![A_147]: (A_147!='#skF_4' | '#skF_2'(A_147)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_850])).
% 2.86/1.45  tff(c_923, plain, (![A_147]: (v1_funct_1('#skF_4') | A_147!='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_915, c_32])).
% 2.86/1.45  tff(c_931, plain, (![A_147]: (A_147!='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_889, c_923])).
% 2.86/1.45  tff(c_943, plain, $false, inference(negUnitSimplification, [status(thm)], [c_931, c_825])).
% 2.86/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.45  
% 2.86/1.45  Inference rules
% 2.86/1.45  ----------------------
% 2.86/1.45  #Ref     : 0
% 2.86/1.45  #Sup     : 175
% 2.86/1.45  #Fact    : 0
% 2.86/1.45  #Define  : 0
% 2.86/1.45  #Split   : 6
% 2.86/1.45  #Chain   : 0
% 2.86/1.45  #Close   : 0
% 2.86/1.45  
% 2.86/1.45  Ordering : KBO
% 2.86/1.45  
% 2.86/1.45  Simplification rules
% 2.86/1.45  ----------------------
% 2.86/1.45  #Subsume      : 44
% 2.86/1.45  #Demod        : 128
% 2.86/1.45  #Tautology    : 87
% 2.86/1.45  #SimpNegUnit  : 44
% 2.86/1.45  #BackRed      : 72
% 2.86/1.45  
% 2.86/1.45  #Partial instantiations: 0
% 2.86/1.45  #Strategies tried      : 1
% 2.86/1.45  
% 2.86/1.45  Timing (in seconds)
% 2.86/1.45  ----------------------
% 2.86/1.45  Preprocessing        : 0.30
% 2.86/1.45  Parsing              : 0.16
% 2.86/1.45  CNF conversion       : 0.02
% 2.86/1.45  Main loop            : 0.38
% 2.86/1.45  Inferencing          : 0.14
% 2.86/1.45  Reduction            : 0.11
% 2.86/1.45  Demodulation         : 0.07
% 2.86/1.45  BG Simplification    : 0.02
% 2.86/1.45  Subsumption          : 0.07
% 2.86/1.45  Abstraction          : 0.02
% 2.86/1.45  MUC search           : 0.00
% 2.86/1.45  Cooper               : 0.00
% 2.86/1.45  Total                : 0.73
% 2.86/1.45  Index Insertion      : 0.00
% 2.86/1.45  Index Deletion       : 0.00
% 2.86/1.45  Index Matching       : 0.00
% 2.86/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
