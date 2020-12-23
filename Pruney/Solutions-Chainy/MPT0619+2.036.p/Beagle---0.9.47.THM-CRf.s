%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:56 EST 2020

% Result     : Theorem 37.54s
% Output     : CNFRefutation 37.54s
% Verified   : 
% Statistics : Number of formulae       :  122 (1858 expanded)
%              Number of leaves         :   29 ( 647 expanded)
%              Depth                    :   32
%              Number of atoms          :  260 (4465 expanded)
%              Number of equality atoms :  122 (2347 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_10 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( k1_relat_1(B) = k1_tarski(A)
         => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k1_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(c_48,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_44,plain,(
    k1_tarski('#skF_9') = k1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_4,plain,(
    ! [C_5] : r2_hidden(C_5,k1_tarski(C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_53,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_4])).

tff(c_76,plain,(
    ! [A_63,B_64] :
      ( k2_xboole_0(k1_tarski(A_63),B_64) = B_64
      | ~ r2_hidden(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_20,plain,(
    ! [A_11,B_12] : k2_xboole_0(k1_tarski(A_11),B_12) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_91,plain,(
    ! [B_65,A_66] :
      ( k1_xboole_0 != B_65
      | ~ r2_hidden(A_66,B_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_20])).

tff(c_98,plain,(
    k1_relat_1('#skF_10') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_53,c_91])).

tff(c_115,plain,(
    ! [A_71,B_72] :
      ( r2_hidden('#skF_3'(A_71,B_72),A_71)
      | k1_xboole_0 = A_71
      | k1_tarski(B_72) = A_71 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_61,plain,(
    ! [C_60,A_61] :
      ( C_60 = A_61
      | ~ r2_hidden(C_60,k1_tarski(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_64,plain,(
    ! [C_60] :
      ( C_60 = '#skF_9'
      | ~ r2_hidden(C_60,k1_relat_1('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_61])).

tff(c_122,plain,(
    ! [B_72] :
      ( '#skF_3'(k1_relat_1('#skF_10'),B_72) = '#skF_9'
      | k1_relat_1('#skF_10') = k1_xboole_0
      | k1_tarski(B_72) = k1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_115,c_64])).

tff(c_159,plain,(
    ! [B_75] :
      ( '#skF_3'(k1_relat_1('#skF_10'),B_75) = '#skF_9'
      | k1_tarski(B_75) = k1_relat_1('#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_122])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( '#skF_3'(A_8,B_9) != B_9
      | k1_xboole_0 = A_8
      | k1_tarski(B_9) = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_167,plain,(
    ! [B_75] :
      ( B_75 != '#skF_9'
      | k1_relat_1('#skF_10') = k1_xboole_0
      | k1_tarski(B_75) = k1_relat_1('#skF_10')
      | k1_tarski(B_75) = k1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_16])).

tff(c_174,plain,(
    ! [B_75] :
      ( B_75 != '#skF_9'
      | k1_tarski(B_75) = k1_relat_1('#skF_10')
      | k1_tarski(B_75) = k1_relat_1('#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_167])).

tff(c_212,plain,(
    ! [B_77] :
      ( B_77 != '#skF_9'
      | k1_tarski(B_77) = k1_relat_1('#skF_10') ) ),
    inference(factorization,[status(thm),theory(equality)],[c_174])).

tff(c_234,plain,(
    ! [B_77] :
      ( r2_hidden(B_77,k1_relat_1('#skF_10'))
      | B_77 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_4])).

tff(c_939,plain,(
    ! [A_975,B_976] :
      ( r2_hidden('#skF_4'(A_975,B_976),k2_relat_1(B_976))
      | ~ r2_hidden(A_975,k1_relat_1(B_976))
      | ~ v1_relat_1(B_976) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_81,plain,(
    ! [B_64,A_63] :
      ( k1_xboole_0 != B_64
      | ~ r2_hidden(A_63,B_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_20])).

tff(c_949,plain,(
    ! [B_1001,A_1002] :
      ( k2_relat_1(B_1001) != k1_xboole_0
      | ~ r2_hidden(A_1002,k1_relat_1(B_1001))
      | ~ v1_relat_1(B_1001) ) ),
    inference(resolution,[status(thm)],[c_939,c_81])).

tff(c_957,plain,(
    ! [B_77] :
      ( k2_relat_1('#skF_10') != k1_xboole_0
      | ~ v1_relat_1('#skF_10')
      | B_77 != '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_234,c_949])).

tff(c_965,plain,(
    ! [B_77] :
      ( k2_relat_1('#skF_10') != k1_xboole_0
      | B_77 != '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_957])).

tff(c_967,plain,(
    k2_relat_1('#skF_10') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_965])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_3'(A_8,B_9),A_8)
      | k1_xboole_0 = A_8
      | k1_tarski(B_9) = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_46,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_28,plain,(
    ! [A_16,C_52] :
      ( r2_hidden('#skF_8'(A_16,k2_relat_1(A_16),C_52),k1_relat_1(A_16))
      | ~ r2_hidden(C_52,k2_relat_1(A_16))
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_24,plain,(
    ! [A_16,D_55] :
      ( r2_hidden(k1_funct_1(A_16,D_55),k2_relat_1(A_16))
      | ~ r2_hidden(D_55,k1_relat_1(A_16))
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_4'(A_13,B_14),k2_relat_1(B_14))
      | ~ r2_hidden(A_13,k1_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_90,plain,(
    ! [A_63] : ~ r2_hidden(A_63,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_20])).

tff(c_240,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_4])).

tff(c_4884,plain,(
    ! [A_6479,B_6480] :
      ( r2_hidden('#skF_6'(A_6479,B_6480),k1_relat_1(A_6479))
      | r2_hidden('#skF_7'(A_6479,B_6480),B_6480)
      | k2_relat_1(A_6479) = B_6480
      | ~ v1_funct_1(A_6479)
      | ~ v1_relat_1(A_6479) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4899,plain,(
    ! [B_6480] :
      ( '#skF_6'('#skF_10',B_6480) = '#skF_9'
      | r2_hidden('#skF_7'('#skF_10',B_6480),B_6480)
      | k2_relat_1('#skF_10') = B_6480
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_4884,c_64])).

tff(c_5061,plain,(
    ! [B_6626] :
      ( '#skF_6'('#skF_10',B_6626) = '#skF_9'
      | r2_hidden('#skF_7'('#skF_10',B_6626),B_6626)
      | k2_relat_1('#skF_10') = B_6626 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_4899])).

tff(c_5461,plain,
    ( '#skF_6'('#skF_10',k1_xboole_0) = '#skF_9'
    | k2_relat_1('#skF_10') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5061,c_81])).

tff(c_5464,plain,(
    ! [D_55] :
      ( r2_hidden(k1_funct_1('#skF_10',D_55),k1_xboole_0)
      | ~ r2_hidden(D_55,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | '#skF_6'('#skF_10',k1_xboole_0) = '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5461,c_24])).

tff(c_5628,plain,(
    ! [D_55] :
      ( r2_hidden(k1_funct_1('#skF_10',D_55),k1_xboole_0)
      | ~ r2_hidden(D_55,k1_relat_1('#skF_10'))
      | '#skF_6'('#skF_10',k1_xboole_0) = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_5464])).

tff(c_5629,plain,(
    ! [D_55] :
      ( ~ r2_hidden(D_55,k1_relat_1('#skF_10'))
      | '#skF_6'('#skF_10',k1_xboole_0) = '#skF_9' ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_5628])).

tff(c_5694,plain,(
    ! [D_55] : ~ r2_hidden(D_55,k1_relat_1('#skF_10')) ),
    inference(splitLeft,[status(thm)],[c_5629])).

tff(c_5697,plain,(
    ! [B_77] : B_77 != '#skF_9' ),
    inference(negUnitSimplification,[status(thm)],[c_5694,c_234])).

tff(c_99,plain,(
    ! [C_5] : k1_tarski(C_5) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_91])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_126,plain,(
    ! [A_1,B_72] :
      ( '#skF_3'(k1_tarski(A_1),B_72) = A_1
      | k1_tarski(A_1) = k1_xboole_0
      | k1_tarski(B_72) = k1_tarski(A_1) ) ),
    inference(resolution,[status(thm)],[c_115,c_2])).

tff(c_133,plain,(
    ! [A_1,B_72] :
      ( '#skF_3'(k1_tarski(A_1),B_72) = A_1
      | k1_tarski(B_72) = k1_tarski(A_1) ) ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_126])).

tff(c_1017,plain,(
    ! [B_1103,B_1104] :
      ( B_1103 = '#skF_3'(k1_relat_1('#skF_10'),B_1104)
      | k1_tarski(B_1104) = k1_tarski(B_1103)
      | B_1103 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_133])).

tff(c_2155,plain,(
    ! [B_3318,B_3319] :
      ( r2_hidden(B_3318,k1_tarski(B_3319))
      | B_3319 = '#skF_3'(k1_relat_1('#skF_10'),B_3318)
      | B_3319 != '#skF_9' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1017,c_4])).

tff(c_2254,plain,(
    ! [B_3319,B_3318] :
      ( B_3319 = B_3318
      | B_3319 = '#skF_3'(k1_relat_1('#skF_10'),B_3318)
      | B_3319 != '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_2155,c_2])).

tff(c_2306,plain,(
    ! [B_3318] :
      ( B_3318 = '#skF_9'
      | '#skF_3'(k1_relat_1('#skF_10'),B_3318) = '#skF_9' ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_2254])).

tff(c_5756,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5697,c_5697,c_2306])).

tff(c_5757,plain,(
    '#skF_6'('#skF_10',k1_xboole_0) = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_5629])).

tff(c_5771,plain,(
    ! [A_9247,B_9248] :
      ( k1_funct_1(A_9247,'#skF_6'(A_9247,B_9248)) = '#skF_5'(A_9247,B_9248)
      | r2_hidden('#skF_7'(A_9247,B_9248),B_9248)
      | k2_relat_1(A_9247) = B_9248
      | ~ v1_funct_1(A_9247)
      | ~ v1_relat_1(A_9247) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_42374,plain,(
    ! [A_26075,B_26076] :
      ( r2_hidden('#skF_5'(A_26075,B_26076),k2_relat_1(A_26075))
      | ~ r2_hidden('#skF_6'(A_26075,B_26076),k1_relat_1(A_26075))
      | ~ v1_funct_1(A_26075)
      | ~ v1_relat_1(A_26075)
      | r2_hidden('#skF_7'(A_26075,B_26076),B_26076)
      | k2_relat_1(A_26075) = B_26076
      | ~ v1_funct_1(A_26075)
      | ~ v1_relat_1(A_26075) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5771,c_24])).

tff(c_42536,plain,
    ( r2_hidden('#skF_5'('#skF_10',k1_xboole_0),k2_relat_1('#skF_10'))
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10')
    | r2_hidden('#skF_7'('#skF_10',k1_xboole_0),k1_xboole_0)
    | k2_relat_1('#skF_10') = k1_xboole_0
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_5757,c_42374])).

tff(c_42603,plain,
    ( r2_hidden('#skF_5'('#skF_10',k1_xboole_0),k2_relat_1('#skF_10'))
    | r2_hidden('#skF_7'('#skF_10',k1_xboole_0),k1_xboole_0)
    | k2_relat_1('#skF_10') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_48,c_46,c_240,c_42536])).

tff(c_42604,plain,(
    r2_hidden('#skF_5'('#skF_10',k1_xboole_0),k2_relat_1('#skF_10')) ),
    inference(negUnitSimplification,[status(thm)],[c_967,c_90,c_42603])).

tff(c_3825,plain,(
    ! [A_5158,C_5159] :
      ( r2_hidden('#skF_8'(A_5158,k2_relat_1(A_5158),C_5159),k1_relat_1(A_5158))
      | ~ r2_hidden(C_5159,k2_relat_1(A_5158))
      | ~ v1_funct_1(A_5158)
      | ~ v1_relat_1(A_5158) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_3840,plain,(
    ! [C_5159] :
      ( '#skF_8'('#skF_10',k2_relat_1('#skF_10'),C_5159) = '#skF_9'
      | ~ r2_hidden(C_5159,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_3825,c_64])).

tff(c_3897,plain,(
    ! [C_5159] :
      ( '#skF_8'('#skF_10',k2_relat_1('#skF_10'),C_5159) = '#skF_9'
      | ~ r2_hidden(C_5159,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_3840])).

tff(c_42858,plain,(
    '#skF_8'('#skF_10',k2_relat_1('#skF_10'),'#skF_5'('#skF_10',k1_xboole_0)) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_42604,c_3897])).

tff(c_26,plain,(
    ! [A_16,C_52] :
      ( k1_funct_1(A_16,'#skF_8'(A_16,k2_relat_1(A_16),C_52)) = C_52
      | ~ r2_hidden(C_52,k2_relat_1(A_16))
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_42870,plain,
    ( k1_funct_1('#skF_10','#skF_9') = '#skF_5'('#skF_10',k1_xboole_0)
    | ~ r2_hidden('#skF_5'('#skF_10',k1_xboole_0),k2_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_42858,c_26])).

tff(c_43243,plain,(
    k1_funct_1('#skF_10','#skF_9') = '#skF_5'('#skF_10',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_42604,c_42870])).

tff(c_3906,plain,(
    ! [C_5232] :
      ( '#skF_8'('#skF_10',k2_relat_1('#skF_10'),C_5232) = '#skF_9'
      | ~ r2_hidden(C_5232,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_3840])).

tff(c_3919,plain,(
    ! [A_13] :
      ( '#skF_8'('#skF_10',k2_relat_1('#skF_10'),'#skF_4'(A_13,'#skF_10')) = '#skF_9'
      | ~ r2_hidden(A_13,k1_relat_1('#skF_10'))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_22,c_3906])).

tff(c_4063,plain,(
    ! [A_5526] :
      ( '#skF_8'('#skF_10',k2_relat_1('#skF_10'),'#skF_4'(A_5526,'#skF_10')) = '#skF_9'
      | ~ r2_hidden(A_5526,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_3919])).

tff(c_4072,plain,(
    ! [A_5526] :
      ( k1_funct_1('#skF_10','#skF_9') = '#skF_4'(A_5526,'#skF_10')
      | ~ r2_hidden('#skF_4'(A_5526,'#skF_10'),k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(A_5526,k1_relat_1('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4063,c_26])).

tff(c_4092,plain,(
    ! [A_5526] :
      ( k1_funct_1('#skF_10','#skF_9') = '#skF_4'(A_5526,'#skF_10')
      | ~ r2_hidden('#skF_4'(A_5526,'#skF_10'),k2_relat_1('#skF_10'))
      | ~ r2_hidden(A_5526,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_4072])).

tff(c_150871,plain,(
    ! [A_125895] :
      ( '#skF_5'('#skF_10',k1_xboole_0) = '#skF_4'(A_125895,'#skF_10')
      | ~ r2_hidden('#skF_4'(A_125895,'#skF_10'),k2_relat_1('#skF_10'))
      | ~ r2_hidden(A_125895,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43243,c_4092])).

tff(c_151134,plain,(
    ! [A_13] :
      ( '#skF_5'('#skF_10',k1_xboole_0) = '#skF_4'(A_13,'#skF_10')
      | ~ r2_hidden(A_13,k1_relat_1('#skF_10'))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_22,c_150871])).

tff(c_151140,plain,(
    ! [A_126328] :
      ( '#skF_5'('#skF_10',k1_xboole_0) = '#skF_4'(A_126328,'#skF_10')
      | ~ r2_hidden(A_126328,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_151134])).

tff(c_151478,plain,(
    '#skF_5'('#skF_10',k1_xboole_0) = '#skF_4'('#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_234,c_151140])).

tff(c_151506,plain,(
    k1_funct_1('#skF_10','#skF_9') = '#skF_4'('#skF_9','#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151478,c_43243])).

tff(c_3910,plain,(
    ! [D_55] :
      ( '#skF_8'('#skF_10',k2_relat_1('#skF_10'),k1_funct_1('#skF_10',D_55)) = '#skF_9'
      | ~ r2_hidden(D_55,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_24,c_3906])).

tff(c_3969,plain,(
    ! [D_5379] :
      ( '#skF_8'('#skF_10',k2_relat_1('#skF_10'),k1_funct_1('#skF_10',D_5379)) = '#skF_9'
      | ~ r2_hidden(D_5379,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_3910])).

tff(c_3978,plain,(
    ! [D_5379] :
      ( k1_funct_1('#skF_10',D_5379) = k1_funct_1('#skF_10','#skF_9')
      | ~ r2_hidden(k1_funct_1('#skF_10',D_5379),k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(D_5379,k1_relat_1('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3969,c_26])).

tff(c_4002,plain,(
    ! [D_5379] :
      ( k1_funct_1('#skF_10',D_5379) = k1_funct_1('#skF_10','#skF_9')
      | ~ r2_hidden(k1_funct_1('#skF_10',D_5379),k2_relat_1('#skF_10'))
      | ~ r2_hidden(D_5379,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_3978])).

tff(c_205949,plain,(
    ! [D_179936] :
      ( k1_funct_1('#skF_10',D_179936) = '#skF_4'('#skF_9','#skF_10')
      | ~ r2_hidden(k1_funct_1('#skF_10',D_179936),k2_relat_1('#skF_10'))
      | ~ r2_hidden(D_179936,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151506,c_4002])).

tff(c_206247,plain,(
    ! [D_55] :
      ( k1_funct_1('#skF_10',D_55) = '#skF_4'('#skF_9','#skF_10')
      | ~ r2_hidden(D_55,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_24,c_205949])).

tff(c_206274,plain,(
    ! [D_180441] :
      ( k1_funct_1('#skF_10',D_180441) = '#skF_4'('#skF_9','#skF_10')
      | ~ r2_hidden(D_180441,k1_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_206247])).

tff(c_206552,plain,(
    ! [C_52] :
      ( k1_funct_1('#skF_10','#skF_8'('#skF_10',k2_relat_1('#skF_10'),C_52)) = '#skF_4'('#skF_9','#skF_10')
      | ~ r2_hidden(C_52,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_28,c_206274])).

tff(c_212951,plain,(
    ! [C_183471] :
      ( k1_funct_1('#skF_10','#skF_8'('#skF_10',k2_relat_1('#skF_10'),C_183471)) = '#skF_4'('#skF_9','#skF_10')
      | ~ r2_hidden(C_183471,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_206552])).

tff(c_212979,plain,(
    ! [C_183471] :
      ( C_183471 = '#skF_4'('#skF_9','#skF_10')
      | ~ r2_hidden(C_183471,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(C_183471,k2_relat_1('#skF_10')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_212951,c_26])).

tff(c_213856,plain,(
    ! [C_183976] :
      ( C_183976 = '#skF_4'('#skF_9','#skF_10')
      | ~ r2_hidden(C_183976,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_212979])).

tff(c_214083,plain,(
    ! [B_9] :
      ( '#skF_3'(k2_relat_1('#skF_10'),B_9) = '#skF_4'('#skF_9','#skF_10')
      | k2_relat_1('#skF_10') = k1_xboole_0
      | k2_relat_1('#skF_10') = k1_tarski(B_9) ) ),
    inference(resolution,[status(thm)],[c_18,c_213856])).

tff(c_214136,plain,(
    ! [B_184481] :
      ( '#skF_3'(k2_relat_1('#skF_10'),B_184481) = '#skF_4'('#skF_9','#skF_10')
      | k2_relat_1('#skF_10') = k1_tarski(B_184481) ) ),
    inference(negUnitSimplification,[status(thm)],[c_967,c_214083])).

tff(c_214162,plain,(
    ! [B_184481] :
      ( B_184481 != '#skF_4'('#skF_9','#skF_10')
      | k2_relat_1('#skF_10') = k1_xboole_0
      | k2_relat_1('#skF_10') = k1_tarski(B_184481)
      | k2_relat_1('#skF_10') = k1_tarski(B_184481) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_214136,c_16])).

tff(c_214962,plain,(
    k1_tarski('#skF_4'('#skF_9','#skF_10')) = k2_relat_1('#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_967,c_214162])).

tff(c_42,plain,(
    k1_tarski(k1_funct_1('#skF_10','#skF_9')) != k2_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_43261,plain,(
    k1_tarski('#skF_5'('#skF_10',k1_xboole_0)) != k2_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_43243,c_42])).

tff(c_151505,plain,(
    k1_tarski('#skF_4'('#skF_9','#skF_10')) != k2_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_151478,c_43261])).

tff(c_214968,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_214962,c_151505])).

tff(c_214969,plain,(
    ! [B_77] : B_77 != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_965])).

tff(c_214976,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_214969])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:21:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 37.54/25.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 37.54/25.96  
% 37.54/25.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 37.54/25.96  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k2_xboole_0 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_3 > #skF_10 > #skF_9 > #skF_2 > #skF_8 > #skF_7 > #skF_1 > #skF_5 > #skF_4
% 37.54/25.96  
% 37.54/25.96  %Foreground sorts:
% 37.54/25.96  
% 37.54/25.96  
% 37.54/25.96  %Background operators:
% 37.54/25.96  
% 37.54/25.96  
% 37.54/25.96  %Foreground operators:
% 37.54/25.96  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 37.54/25.96  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 37.54/25.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 37.54/25.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 37.54/25.96  tff(k1_tarski, type, k1_tarski: $i > $i).
% 37.54/25.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 37.54/25.96  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 37.54/25.96  tff('#skF_10', type, '#skF_10': $i).
% 37.54/25.96  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 37.54/25.96  tff('#skF_9', type, '#skF_9': $i).
% 37.54/25.96  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 37.54/25.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 37.54/25.96  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 37.54/25.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 37.54/25.96  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 37.54/25.96  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 37.54/25.96  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 37.54/25.96  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 37.54/25.96  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 37.54/25.96  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 37.54/25.96  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 37.54/25.96  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 37.54/25.96  
% 37.54/25.98  tff(f_86, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 37.54/25.98  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 37.54/25.98  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 37.54/25.98  tff(f_53, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 37.54/25.98  tff(f_50, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l44_zfmisc_1)).
% 37.54/25.98  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k1_relat_1(B)) & (![C]: ~r2_hidden(C, k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_relat_1)).
% 37.54/25.98  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 37.54/25.98  tff(c_48, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_86])).
% 37.54/25.98  tff(c_44, plain, (k1_tarski('#skF_9')=k1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_86])).
% 37.54/25.98  tff(c_4, plain, (![C_5]: (r2_hidden(C_5, k1_tarski(C_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 37.54/25.98  tff(c_53, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_4])).
% 37.54/25.98  tff(c_76, plain, (![A_63, B_64]: (k2_xboole_0(k1_tarski(A_63), B_64)=B_64 | ~r2_hidden(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_36])).
% 37.54/25.98  tff(c_20, plain, (![A_11, B_12]: (k2_xboole_0(k1_tarski(A_11), B_12)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 37.54/25.98  tff(c_91, plain, (![B_65, A_66]: (k1_xboole_0!=B_65 | ~r2_hidden(A_66, B_65))), inference(superposition, [status(thm), theory('equality')], [c_76, c_20])).
% 37.54/25.98  tff(c_98, plain, (k1_relat_1('#skF_10')!=k1_xboole_0), inference(resolution, [status(thm)], [c_53, c_91])).
% 37.54/25.98  tff(c_115, plain, (![A_71, B_72]: (r2_hidden('#skF_3'(A_71, B_72), A_71) | k1_xboole_0=A_71 | k1_tarski(B_72)=A_71)), inference(cnfTransformation, [status(thm)], [f_50])).
% 37.54/25.98  tff(c_61, plain, (![C_60, A_61]: (C_60=A_61 | ~r2_hidden(C_60, k1_tarski(A_61)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 37.54/25.98  tff(c_64, plain, (![C_60]: (C_60='#skF_9' | ~r2_hidden(C_60, k1_relat_1('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_44, c_61])).
% 37.54/25.98  tff(c_122, plain, (![B_72]: ('#skF_3'(k1_relat_1('#skF_10'), B_72)='#skF_9' | k1_relat_1('#skF_10')=k1_xboole_0 | k1_tarski(B_72)=k1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_115, c_64])).
% 37.54/25.98  tff(c_159, plain, (![B_75]: ('#skF_3'(k1_relat_1('#skF_10'), B_75)='#skF_9' | k1_tarski(B_75)=k1_relat_1('#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_98, c_122])).
% 37.54/25.98  tff(c_16, plain, (![A_8, B_9]: ('#skF_3'(A_8, B_9)!=B_9 | k1_xboole_0=A_8 | k1_tarski(B_9)=A_8)), inference(cnfTransformation, [status(thm)], [f_50])).
% 37.54/25.98  tff(c_167, plain, (![B_75]: (B_75!='#skF_9' | k1_relat_1('#skF_10')=k1_xboole_0 | k1_tarski(B_75)=k1_relat_1('#skF_10') | k1_tarski(B_75)=k1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_159, c_16])).
% 37.54/25.98  tff(c_174, plain, (![B_75]: (B_75!='#skF_9' | k1_tarski(B_75)=k1_relat_1('#skF_10') | k1_tarski(B_75)=k1_relat_1('#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_98, c_167])).
% 37.54/25.98  tff(c_212, plain, (![B_77]: (B_77!='#skF_9' | k1_tarski(B_77)=k1_relat_1('#skF_10'))), inference(factorization, [status(thm), theory('equality')], [c_174])).
% 37.54/25.98  tff(c_234, plain, (![B_77]: (r2_hidden(B_77, k1_relat_1('#skF_10')) | B_77!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_212, c_4])).
% 37.54/25.98  tff(c_939, plain, (![A_975, B_976]: (r2_hidden('#skF_4'(A_975, B_976), k2_relat_1(B_976)) | ~r2_hidden(A_975, k1_relat_1(B_976)) | ~v1_relat_1(B_976))), inference(cnfTransformation, [status(thm)], [f_62])).
% 37.54/25.98  tff(c_81, plain, (![B_64, A_63]: (k1_xboole_0!=B_64 | ~r2_hidden(A_63, B_64))), inference(superposition, [status(thm), theory('equality')], [c_76, c_20])).
% 37.54/25.98  tff(c_949, plain, (![B_1001, A_1002]: (k2_relat_1(B_1001)!=k1_xboole_0 | ~r2_hidden(A_1002, k1_relat_1(B_1001)) | ~v1_relat_1(B_1001))), inference(resolution, [status(thm)], [c_939, c_81])).
% 37.54/25.98  tff(c_957, plain, (![B_77]: (k2_relat_1('#skF_10')!=k1_xboole_0 | ~v1_relat_1('#skF_10') | B_77!='#skF_9')), inference(resolution, [status(thm)], [c_234, c_949])).
% 37.54/25.98  tff(c_965, plain, (![B_77]: (k2_relat_1('#skF_10')!=k1_xboole_0 | B_77!='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_957])).
% 37.54/25.98  tff(c_967, plain, (k2_relat_1('#skF_10')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_965])).
% 37.54/25.98  tff(c_18, plain, (![A_8, B_9]: (r2_hidden('#skF_3'(A_8, B_9), A_8) | k1_xboole_0=A_8 | k1_tarski(B_9)=A_8)), inference(cnfTransformation, [status(thm)], [f_50])).
% 37.54/25.98  tff(c_46, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_86])).
% 37.54/25.98  tff(c_28, plain, (![A_16, C_52]: (r2_hidden('#skF_8'(A_16, k2_relat_1(A_16), C_52), k1_relat_1(A_16)) | ~r2_hidden(C_52, k2_relat_1(A_16)) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_77])).
% 37.54/25.98  tff(c_24, plain, (![A_16, D_55]: (r2_hidden(k1_funct_1(A_16, D_55), k2_relat_1(A_16)) | ~r2_hidden(D_55, k1_relat_1(A_16)) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_77])).
% 37.54/25.98  tff(c_22, plain, (![A_13, B_14]: (r2_hidden('#skF_4'(A_13, B_14), k2_relat_1(B_14)) | ~r2_hidden(A_13, k1_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 37.54/25.98  tff(c_90, plain, (![A_63]: (~r2_hidden(A_63, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_76, c_20])).
% 37.54/25.98  tff(c_240, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_212, c_4])).
% 37.54/25.98  tff(c_4884, plain, (![A_6479, B_6480]: (r2_hidden('#skF_6'(A_6479, B_6480), k1_relat_1(A_6479)) | r2_hidden('#skF_7'(A_6479, B_6480), B_6480) | k2_relat_1(A_6479)=B_6480 | ~v1_funct_1(A_6479) | ~v1_relat_1(A_6479))), inference(cnfTransformation, [status(thm)], [f_77])).
% 37.54/25.98  tff(c_4899, plain, (![B_6480]: ('#skF_6'('#skF_10', B_6480)='#skF_9' | r2_hidden('#skF_7'('#skF_10', B_6480), B_6480) | k2_relat_1('#skF_10')=B_6480 | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_4884, c_64])).
% 37.54/25.98  tff(c_5061, plain, (![B_6626]: ('#skF_6'('#skF_10', B_6626)='#skF_9' | r2_hidden('#skF_7'('#skF_10', B_6626), B_6626) | k2_relat_1('#skF_10')=B_6626)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_4899])).
% 37.54/25.98  tff(c_5461, plain, ('#skF_6'('#skF_10', k1_xboole_0)='#skF_9' | k2_relat_1('#skF_10')=k1_xboole_0), inference(resolution, [status(thm)], [c_5061, c_81])).
% 37.54/25.98  tff(c_5464, plain, (![D_55]: (r2_hidden(k1_funct_1('#skF_10', D_55), k1_xboole_0) | ~r2_hidden(D_55, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | '#skF_6'('#skF_10', k1_xboole_0)='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_5461, c_24])).
% 37.54/25.98  tff(c_5628, plain, (![D_55]: (r2_hidden(k1_funct_1('#skF_10', D_55), k1_xboole_0) | ~r2_hidden(D_55, k1_relat_1('#skF_10')) | '#skF_6'('#skF_10', k1_xboole_0)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_5464])).
% 37.54/25.98  tff(c_5629, plain, (![D_55]: (~r2_hidden(D_55, k1_relat_1('#skF_10')) | '#skF_6'('#skF_10', k1_xboole_0)='#skF_9')), inference(negUnitSimplification, [status(thm)], [c_90, c_5628])).
% 37.54/25.98  tff(c_5694, plain, (![D_55]: (~r2_hidden(D_55, k1_relat_1('#skF_10')))), inference(splitLeft, [status(thm)], [c_5629])).
% 37.54/25.98  tff(c_5697, plain, (![B_77]: (B_77!='#skF_9')), inference(negUnitSimplification, [status(thm)], [c_5694, c_234])).
% 37.54/25.98  tff(c_99, plain, (![C_5]: (k1_tarski(C_5)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_91])).
% 37.54/25.98  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 37.54/25.98  tff(c_126, plain, (![A_1, B_72]: ('#skF_3'(k1_tarski(A_1), B_72)=A_1 | k1_tarski(A_1)=k1_xboole_0 | k1_tarski(B_72)=k1_tarski(A_1))), inference(resolution, [status(thm)], [c_115, c_2])).
% 37.54/25.98  tff(c_133, plain, (![A_1, B_72]: ('#skF_3'(k1_tarski(A_1), B_72)=A_1 | k1_tarski(B_72)=k1_tarski(A_1))), inference(negUnitSimplification, [status(thm)], [c_99, c_126])).
% 37.54/25.98  tff(c_1017, plain, (![B_1103, B_1104]: (B_1103='#skF_3'(k1_relat_1('#skF_10'), B_1104) | k1_tarski(B_1104)=k1_tarski(B_1103) | B_1103!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_212, c_133])).
% 37.54/25.98  tff(c_2155, plain, (![B_3318, B_3319]: (r2_hidden(B_3318, k1_tarski(B_3319)) | B_3319='#skF_3'(k1_relat_1('#skF_10'), B_3318) | B_3319!='#skF_9')), inference(superposition, [status(thm), theory('equality')], [c_1017, c_4])).
% 37.54/25.98  tff(c_2254, plain, (![B_3319, B_3318]: (B_3319=B_3318 | B_3319='#skF_3'(k1_relat_1('#skF_10'), B_3318) | B_3319!='#skF_9')), inference(resolution, [status(thm)], [c_2155, c_2])).
% 37.54/25.98  tff(c_2306, plain, (![B_3318]: (B_3318='#skF_9' | '#skF_3'(k1_relat_1('#skF_10'), B_3318)='#skF_9')), inference(reflexivity, [status(thm), theory('equality')], [c_2254])).
% 37.54/25.98  tff(c_5756, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5697, c_5697, c_2306])).
% 37.54/25.98  tff(c_5757, plain, ('#skF_6'('#skF_10', k1_xboole_0)='#skF_9'), inference(splitRight, [status(thm)], [c_5629])).
% 37.54/25.98  tff(c_5771, plain, (![A_9247, B_9248]: (k1_funct_1(A_9247, '#skF_6'(A_9247, B_9248))='#skF_5'(A_9247, B_9248) | r2_hidden('#skF_7'(A_9247, B_9248), B_9248) | k2_relat_1(A_9247)=B_9248 | ~v1_funct_1(A_9247) | ~v1_relat_1(A_9247))), inference(cnfTransformation, [status(thm)], [f_77])).
% 37.54/25.98  tff(c_42374, plain, (![A_26075, B_26076]: (r2_hidden('#skF_5'(A_26075, B_26076), k2_relat_1(A_26075)) | ~r2_hidden('#skF_6'(A_26075, B_26076), k1_relat_1(A_26075)) | ~v1_funct_1(A_26075) | ~v1_relat_1(A_26075) | r2_hidden('#skF_7'(A_26075, B_26076), B_26076) | k2_relat_1(A_26075)=B_26076 | ~v1_funct_1(A_26075) | ~v1_relat_1(A_26075))), inference(superposition, [status(thm), theory('equality')], [c_5771, c_24])).
% 37.54/25.98  tff(c_42536, plain, (r2_hidden('#skF_5'('#skF_10', k1_xboole_0), k2_relat_1('#skF_10')) | ~r2_hidden('#skF_9', k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | r2_hidden('#skF_7'('#skF_10', k1_xboole_0), k1_xboole_0) | k2_relat_1('#skF_10')=k1_xboole_0 | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_5757, c_42374])).
% 37.54/25.98  tff(c_42603, plain, (r2_hidden('#skF_5'('#skF_10', k1_xboole_0), k2_relat_1('#skF_10')) | r2_hidden('#skF_7'('#skF_10', k1_xboole_0), k1_xboole_0) | k2_relat_1('#skF_10')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_48, c_46, c_240, c_42536])).
% 37.54/25.98  tff(c_42604, plain, (r2_hidden('#skF_5'('#skF_10', k1_xboole_0), k2_relat_1('#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_967, c_90, c_42603])).
% 37.54/25.98  tff(c_3825, plain, (![A_5158, C_5159]: (r2_hidden('#skF_8'(A_5158, k2_relat_1(A_5158), C_5159), k1_relat_1(A_5158)) | ~r2_hidden(C_5159, k2_relat_1(A_5158)) | ~v1_funct_1(A_5158) | ~v1_relat_1(A_5158))), inference(cnfTransformation, [status(thm)], [f_77])).
% 37.54/25.98  tff(c_3840, plain, (![C_5159]: ('#skF_8'('#skF_10', k2_relat_1('#skF_10'), C_5159)='#skF_9' | ~r2_hidden(C_5159, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_3825, c_64])).
% 37.54/25.98  tff(c_3897, plain, (![C_5159]: ('#skF_8'('#skF_10', k2_relat_1('#skF_10'), C_5159)='#skF_9' | ~r2_hidden(C_5159, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_3840])).
% 37.54/25.98  tff(c_42858, plain, ('#skF_8'('#skF_10', k2_relat_1('#skF_10'), '#skF_5'('#skF_10', k1_xboole_0))='#skF_9'), inference(resolution, [status(thm)], [c_42604, c_3897])).
% 37.54/25.98  tff(c_26, plain, (![A_16, C_52]: (k1_funct_1(A_16, '#skF_8'(A_16, k2_relat_1(A_16), C_52))=C_52 | ~r2_hidden(C_52, k2_relat_1(A_16)) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_77])).
% 37.54/25.98  tff(c_42870, plain, (k1_funct_1('#skF_10', '#skF_9')='#skF_5'('#skF_10', k1_xboole_0) | ~r2_hidden('#skF_5'('#skF_10', k1_xboole_0), k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_42858, c_26])).
% 37.54/25.98  tff(c_43243, plain, (k1_funct_1('#skF_10', '#skF_9')='#skF_5'('#skF_10', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_42604, c_42870])).
% 37.54/25.98  tff(c_3906, plain, (![C_5232]: ('#skF_8'('#skF_10', k2_relat_1('#skF_10'), C_5232)='#skF_9' | ~r2_hidden(C_5232, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_3840])).
% 37.54/25.98  tff(c_3919, plain, (![A_13]: ('#skF_8'('#skF_10', k2_relat_1('#skF_10'), '#skF_4'(A_13, '#skF_10'))='#skF_9' | ~r2_hidden(A_13, k1_relat_1('#skF_10')) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_22, c_3906])).
% 37.54/25.98  tff(c_4063, plain, (![A_5526]: ('#skF_8'('#skF_10', k2_relat_1('#skF_10'), '#skF_4'(A_5526, '#skF_10'))='#skF_9' | ~r2_hidden(A_5526, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_3919])).
% 37.54/25.98  tff(c_4072, plain, (![A_5526]: (k1_funct_1('#skF_10', '#skF_9')='#skF_4'(A_5526, '#skF_10') | ~r2_hidden('#skF_4'(A_5526, '#skF_10'), k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden(A_5526, k1_relat_1('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_4063, c_26])).
% 37.54/25.98  tff(c_4092, plain, (![A_5526]: (k1_funct_1('#skF_10', '#skF_9')='#skF_4'(A_5526, '#skF_10') | ~r2_hidden('#skF_4'(A_5526, '#skF_10'), k2_relat_1('#skF_10')) | ~r2_hidden(A_5526, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_4072])).
% 37.54/25.98  tff(c_150871, plain, (![A_125895]: ('#skF_5'('#skF_10', k1_xboole_0)='#skF_4'(A_125895, '#skF_10') | ~r2_hidden('#skF_4'(A_125895, '#skF_10'), k2_relat_1('#skF_10')) | ~r2_hidden(A_125895, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_43243, c_4092])).
% 37.54/25.98  tff(c_151134, plain, (![A_13]: ('#skF_5'('#skF_10', k1_xboole_0)='#skF_4'(A_13, '#skF_10') | ~r2_hidden(A_13, k1_relat_1('#skF_10')) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_22, c_150871])).
% 37.54/25.98  tff(c_151140, plain, (![A_126328]: ('#skF_5'('#skF_10', k1_xboole_0)='#skF_4'(A_126328, '#skF_10') | ~r2_hidden(A_126328, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_151134])).
% 37.54/25.98  tff(c_151478, plain, ('#skF_5'('#skF_10', k1_xboole_0)='#skF_4'('#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_234, c_151140])).
% 37.54/25.98  tff(c_151506, plain, (k1_funct_1('#skF_10', '#skF_9')='#skF_4'('#skF_9', '#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_151478, c_43243])).
% 37.54/25.98  tff(c_3910, plain, (![D_55]: ('#skF_8'('#skF_10', k2_relat_1('#skF_10'), k1_funct_1('#skF_10', D_55))='#skF_9' | ~r2_hidden(D_55, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_24, c_3906])).
% 37.54/25.98  tff(c_3969, plain, (![D_5379]: ('#skF_8'('#skF_10', k2_relat_1('#skF_10'), k1_funct_1('#skF_10', D_5379))='#skF_9' | ~r2_hidden(D_5379, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_3910])).
% 37.54/25.98  tff(c_3978, plain, (![D_5379]: (k1_funct_1('#skF_10', D_5379)=k1_funct_1('#skF_10', '#skF_9') | ~r2_hidden(k1_funct_1('#skF_10', D_5379), k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden(D_5379, k1_relat_1('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_3969, c_26])).
% 37.54/25.98  tff(c_4002, plain, (![D_5379]: (k1_funct_1('#skF_10', D_5379)=k1_funct_1('#skF_10', '#skF_9') | ~r2_hidden(k1_funct_1('#skF_10', D_5379), k2_relat_1('#skF_10')) | ~r2_hidden(D_5379, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_3978])).
% 37.54/25.98  tff(c_205949, plain, (![D_179936]: (k1_funct_1('#skF_10', D_179936)='#skF_4'('#skF_9', '#skF_10') | ~r2_hidden(k1_funct_1('#skF_10', D_179936), k2_relat_1('#skF_10')) | ~r2_hidden(D_179936, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_151506, c_4002])).
% 37.54/25.98  tff(c_206247, plain, (![D_55]: (k1_funct_1('#skF_10', D_55)='#skF_4'('#skF_9', '#skF_10') | ~r2_hidden(D_55, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_24, c_205949])).
% 37.54/25.98  tff(c_206274, plain, (![D_180441]: (k1_funct_1('#skF_10', D_180441)='#skF_4'('#skF_9', '#skF_10') | ~r2_hidden(D_180441, k1_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_206247])).
% 37.54/25.98  tff(c_206552, plain, (![C_52]: (k1_funct_1('#skF_10', '#skF_8'('#skF_10', k2_relat_1('#skF_10'), C_52))='#skF_4'('#skF_9', '#skF_10') | ~r2_hidden(C_52, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_28, c_206274])).
% 37.54/25.98  tff(c_212951, plain, (![C_183471]: (k1_funct_1('#skF_10', '#skF_8'('#skF_10', k2_relat_1('#skF_10'), C_183471))='#skF_4'('#skF_9', '#skF_10') | ~r2_hidden(C_183471, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_206552])).
% 37.54/25.98  tff(c_212979, plain, (![C_183471]: (C_183471='#skF_4'('#skF_9', '#skF_10') | ~r2_hidden(C_183471, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | ~r2_hidden(C_183471, k2_relat_1('#skF_10')))), inference(superposition, [status(thm), theory('equality')], [c_212951, c_26])).
% 37.54/25.98  tff(c_213856, plain, (![C_183976]: (C_183976='#skF_4'('#skF_9', '#skF_10') | ~r2_hidden(C_183976, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_212979])).
% 37.54/25.98  tff(c_214083, plain, (![B_9]: ('#skF_3'(k2_relat_1('#skF_10'), B_9)='#skF_4'('#skF_9', '#skF_10') | k2_relat_1('#skF_10')=k1_xboole_0 | k2_relat_1('#skF_10')=k1_tarski(B_9))), inference(resolution, [status(thm)], [c_18, c_213856])).
% 37.54/25.98  tff(c_214136, plain, (![B_184481]: ('#skF_3'(k2_relat_1('#skF_10'), B_184481)='#skF_4'('#skF_9', '#skF_10') | k2_relat_1('#skF_10')=k1_tarski(B_184481))), inference(negUnitSimplification, [status(thm)], [c_967, c_214083])).
% 37.54/25.98  tff(c_214162, plain, (![B_184481]: (B_184481!='#skF_4'('#skF_9', '#skF_10') | k2_relat_1('#skF_10')=k1_xboole_0 | k2_relat_1('#skF_10')=k1_tarski(B_184481) | k2_relat_1('#skF_10')=k1_tarski(B_184481))), inference(superposition, [status(thm), theory('equality')], [c_214136, c_16])).
% 37.54/25.98  tff(c_214962, plain, (k1_tarski('#skF_4'('#skF_9', '#skF_10'))=k2_relat_1('#skF_10')), inference(negUnitSimplification, [status(thm)], [c_967, c_214162])).
% 37.54/25.98  tff(c_42, plain, (k1_tarski(k1_funct_1('#skF_10', '#skF_9'))!=k2_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_86])).
% 37.54/25.98  tff(c_43261, plain, (k1_tarski('#skF_5'('#skF_10', k1_xboole_0))!=k2_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_43243, c_42])).
% 37.54/25.98  tff(c_151505, plain, (k1_tarski('#skF_4'('#skF_9', '#skF_10'))!=k2_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_151478, c_43261])).
% 37.54/25.98  tff(c_214968, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_214962, c_151505])).
% 37.54/25.98  tff(c_214969, plain, (![B_77]: (B_77!='#skF_9')), inference(splitRight, [status(thm)], [c_965])).
% 37.54/25.98  tff(c_214976, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_214969])).
% 37.54/25.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 37.54/25.98  
% 37.54/25.98  Inference rules
% 37.54/25.98  ----------------------
% 37.54/25.98  #Ref     : 32
% 37.54/25.98  #Sup     : 29746
% 37.54/25.98  #Fact    : 7
% 37.54/25.98  #Define  : 0
% 37.54/25.98  #Split   : 28
% 37.54/25.98  #Chain   : 0
% 37.54/25.98  #Close   : 0
% 37.54/25.98  
% 37.54/25.98  Ordering : KBO
% 37.54/25.98  
% 37.54/25.98  Simplification rules
% 37.54/25.98  ----------------------
% 37.54/25.98  #Subsume      : 9846
% 37.54/25.98  #Demod        : 3587
% 37.54/25.98  #Tautology    : 3736
% 37.54/25.98  #SimpNegUnit  : 690
% 37.54/25.98  #BackRed      : 98
% 37.54/25.98  
% 37.54/25.98  #Partial instantiations: 118858
% 37.54/25.98  #Strategies tried      : 1
% 37.54/25.98  
% 37.54/25.98  Timing (in seconds)
% 37.54/25.98  ----------------------
% 37.54/25.99  Preprocessing        : 0.38
% 37.54/25.99  Parsing              : 0.19
% 37.54/25.99  CNF conversion       : 0.04
% 37.54/25.99  Main loop            : 24.78
% 37.54/25.99  Inferencing          : 3.56
% 37.54/25.99  Reduction            : 4.41
% 37.54/25.99  Demodulation         : 2.84
% 37.54/25.99  BG Simplification    : 0.43
% 37.54/25.99  Subsumption          : 15.54
% 37.54/25.99  Abstraction          : 0.51
% 37.54/25.99  MUC search           : 0.00
% 37.54/25.99  Cooper               : 0.00
% 37.54/25.99  Total                : 25.20
% 37.54/25.99  Index Insertion      : 0.00
% 37.54/25.99  Index Deletion       : 0.00
% 37.54/25.99  Index Matching       : 0.00
% 37.54/25.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
