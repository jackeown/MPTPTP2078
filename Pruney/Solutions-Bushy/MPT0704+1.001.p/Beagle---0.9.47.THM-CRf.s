%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0704+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:44 EST 2020

% Result     : Theorem 18.90s
% Output     : CNFRefutation 19.00s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 495 expanded)
%              Number of leaves         :   43 ( 191 expanded)
%              Depth                    :   22
%              Number of atoms          :  208 (1290 expanded)
%              Number of equality atoms :   51 ( 218 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_9 > #skF_6 > #skF_1 > #skF_11 > #skF_3 > #skF_10 > #skF_2 > #skF_13 > #skF_8 > #skF_7 > #skF_5 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_87,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
        <=> ! [B] :
            ? [C] : r1_tarski(k10_relat_1(A,k1_tarski(B)),k1_tarski(C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_funct_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( ! [B] :
            ~ ( r2_hidden(B,k2_relat_1(A))
              & ! [C] : k10_relat_1(A,k1_tarski(B)) != k1_tarski(C) )
      <=> v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_funct_1)).

tff(f_60,axiom,(
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

tff(f_61,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_102,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_38,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( r2_hidden(D,k1_relat_1(A))
                & r2_hidden(k1_funct_1(A,D),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).

tff(f_107,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(c_64,plain,(
    ! [A_73] : r1_tarski(k1_xboole_0,A_73) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_68,plain,(
    ! [B_75] : r1_tarski(k1_tarski(B_75),k1_tarski(B_75)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_80,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_78,plain,(
    v1_funct_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_82,plain,(
    ! [C_88] :
      ( ~ r1_tarski(k10_relat_1('#skF_11',k1_tarski('#skF_12')),k1_tarski(C_88))
      | ~ v2_funct_1('#skF_11') ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_112,plain,(
    ~ v2_funct_1('#skF_11') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_58,plain,(
    ! [A_60] :
      ( r2_hidden('#skF_9'(A_60),k2_relat_1(A_60))
      | v2_funct_1(A_60)
      | ~ v1_funct_1(A_60)
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_34,plain,(
    ! [A_18,C_54] :
      ( k1_funct_1(A_18,'#skF_8'(A_18,k2_relat_1(A_18),C_54)) = C_54
      | ~ r2_hidden(C_54,k2_relat_1(A_18))
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_36,plain,(
    ! [A_18,C_54] :
      ( r2_hidden('#skF_8'(A_18,k2_relat_1(A_18),C_54),k1_relat_1(A_18))
      | ~ r2_hidden(C_54,k2_relat_1(A_18))
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_50,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_92,plain,(
    ! [A_93] :
      ( k1_xboole_0 = A_93
      | ~ v1_xboole_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_96,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_92])).

tff(c_97,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_50])).

tff(c_88,plain,(
    ! [B_89] :
      ( v2_funct_1('#skF_11')
      | r1_tarski(k10_relat_1('#skF_11',k1_tarski(B_89)),k1_tarski('#skF_13'(B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_143,plain,(
    ! [B_108] : r1_tarski(k10_relat_1('#skF_11',k1_tarski(B_108)),k1_tarski('#skF_13'(B_108))) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_88])).

tff(c_66,plain,(
    ! [B_75,A_74] :
      ( k1_tarski(B_75) = A_74
      | k1_xboole_0 = A_74
      | ~ r1_tarski(A_74,k1_tarski(B_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_147,plain,(
    ! [B_108] :
      ( k10_relat_1('#skF_11',k1_tarski(B_108)) = k1_tarski('#skF_13'(B_108))
      | k10_relat_1('#skF_11',k1_tarski(B_108)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_143,c_66])).

tff(c_22,plain,(
    ! [C_17] : r2_hidden(C_17,k1_tarski(C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3139,plain,(
    ! [D_3026,A_3027,B_3028] :
      ( r2_hidden(D_3026,k10_relat_1(A_3027,B_3028))
      | ~ r2_hidden(k1_funct_1(A_3027,D_3026),B_3028)
      | ~ r2_hidden(D_3026,k1_relat_1(A_3027))
      | ~ v1_funct_1(A_3027)
      | ~ v1_relat_1(A_3027) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3668,plain,(
    ! [D_3504,A_3505] :
      ( r2_hidden(D_3504,k10_relat_1(A_3505,k1_tarski(k1_funct_1(A_3505,D_3504))))
      | ~ r2_hidden(D_3504,k1_relat_1(A_3505))
      | ~ v1_funct_1(A_3505)
      | ~ v1_relat_1(A_3505) ) ),
    inference(resolution,[status(thm)],[c_22,c_3139])).

tff(c_3706,plain,(
    ! [D_3504] :
      ( r2_hidden(D_3504,k1_tarski('#skF_13'(k1_funct_1('#skF_11',D_3504))))
      | ~ r2_hidden(D_3504,k1_relat_1('#skF_11'))
      | ~ v1_funct_1('#skF_11')
      | ~ v1_relat_1('#skF_11')
      | k10_relat_1('#skF_11',k1_tarski(k1_funct_1('#skF_11',D_3504))) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_3668])).

tff(c_81976,plain,(
    ! [D_25223] :
      ( r2_hidden(D_25223,k1_tarski('#skF_13'(k1_funct_1('#skF_11',D_25223))))
      | ~ r2_hidden(D_25223,k1_relat_1('#skF_11'))
      | k10_relat_1('#skF_11',k1_tarski(k1_funct_1('#skF_11',D_25223))) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_3706])).

tff(c_20,plain,(
    ! [C_17,A_13] :
      ( C_17 = A_13
      | ~ r2_hidden(C_17,k1_tarski(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_82933,plain,(
    ! [D_25314] :
      ( '#skF_13'(k1_funct_1('#skF_11',D_25314)) = D_25314
      | ~ r2_hidden(D_25314,k1_relat_1('#skF_11'))
      | k10_relat_1('#skF_11',k1_tarski(k1_funct_1('#skF_11',D_25314))) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_81976,c_20])).

tff(c_76,plain,(
    ! [B_80,A_79] :
      ( ~ v1_xboole_0(B_80)
      | ~ r2_hidden(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_3771,plain,(
    ! [A_3505,D_3504] :
      ( ~ v1_xboole_0(k10_relat_1(A_3505,k1_tarski(k1_funct_1(A_3505,D_3504))))
      | ~ r2_hidden(D_3504,k1_relat_1(A_3505))
      | ~ v1_funct_1(A_3505)
      | ~ v1_relat_1(A_3505) ) ),
    inference(resolution,[status(thm)],[c_3668,c_76])).

tff(c_82969,plain,(
    ! [D_25314] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ r2_hidden(D_25314,k1_relat_1('#skF_11'))
      | ~ v1_funct_1('#skF_11')
      | ~ v1_relat_1('#skF_11')
      | '#skF_13'(k1_funct_1('#skF_11',D_25314)) = D_25314
      | ~ r2_hidden(D_25314,k1_relat_1('#skF_11')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82933,c_3771])).

tff(c_83896,plain,(
    ! [D_25405] :
      ( '#skF_13'(k1_funct_1('#skF_11',D_25405)) = D_25405
      | ~ r2_hidden(D_25405,k1_relat_1('#skF_11')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_97,c_82969])).

tff(c_84109,plain,(
    ! [C_54] :
      ( '#skF_13'(k1_funct_1('#skF_11','#skF_8'('#skF_11',k2_relat_1('#skF_11'),C_54))) = '#skF_8'('#skF_11',k2_relat_1('#skF_11'),C_54)
      | ~ r2_hidden(C_54,k2_relat_1('#skF_11'))
      | ~ v1_funct_1('#skF_11')
      | ~ v1_relat_1('#skF_11') ) ),
    inference(resolution,[status(thm)],[c_36,c_83896])).

tff(c_94970,plain,(
    ! [C_26771] :
      ( '#skF_13'(k1_funct_1('#skF_11','#skF_8'('#skF_11',k2_relat_1('#skF_11'),C_26771))) = '#skF_8'('#skF_11',k2_relat_1('#skF_11'),C_26771)
      | ~ r2_hidden(C_26771,k2_relat_1('#skF_11')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_84109])).

tff(c_95927,plain,(
    ! [C_54] :
      ( '#skF_8'('#skF_11',k2_relat_1('#skF_11'),C_54) = '#skF_13'(C_54)
      | ~ r2_hidden(C_54,k2_relat_1('#skF_11'))
      | ~ r2_hidden(C_54,k2_relat_1('#skF_11'))
      | ~ v1_funct_1('#skF_11')
      | ~ v1_relat_1('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_94970])).

tff(c_96808,plain,(
    ! [C_26954] :
      ( '#skF_8'('#skF_11',k2_relat_1('#skF_11'),C_26954) = '#skF_13'(C_26954)
      | ~ r2_hidden(C_26954,k2_relat_1('#skF_11')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_95927])).

tff(c_97098,plain,
    ( '#skF_8'('#skF_11',k2_relat_1('#skF_11'),'#skF_9'('#skF_11')) = '#skF_13'('#skF_9'('#skF_11'))
    | v2_funct_1('#skF_11')
    | ~ v1_funct_1('#skF_11')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_58,c_96808])).

tff(c_97125,plain,
    ( '#skF_8'('#skF_11',k2_relat_1('#skF_11'),'#skF_9'('#skF_11')) = '#skF_13'('#skF_9'('#skF_11'))
    | v2_funct_1('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_97098])).

tff(c_97126,plain,(
    '#skF_8'('#skF_11',k2_relat_1('#skF_11'),'#skF_9'('#skF_11')) = '#skF_13'('#skF_9'('#skF_11')) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_97125])).

tff(c_97133,plain,
    ( r2_hidden('#skF_13'('#skF_9'('#skF_11')),k1_relat_1('#skF_11'))
    | ~ r2_hidden('#skF_9'('#skF_11'),k2_relat_1('#skF_11'))
    | ~ v1_funct_1('#skF_11')
    | ~ v1_relat_1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_97126,c_36])).

tff(c_97615,plain,
    ( r2_hidden('#skF_13'('#skF_9'('#skF_11')),k1_relat_1('#skF_11'))
    | ~ r2_hidden('#skF_9'('#skF_11'),k2_relat_1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_97133])).

tff(c_97619,plain,(
    ~ r2_hidden('#skF_9'('#skF_11'),k2_relat_1('#skF_11')) ),
    inference(splitLeft,[status(thm)],[c_97615])).

tff(c_99099,plain,
    ( v2_funct_1('#skF_11')
    | ~ v1_funct_1('#skF_11')
    | ~ v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_58,c_97619])).

tff(c_99107,plain,(
    v2_funct_1('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_99099])).

tff(c_99109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_99107])).

tff(c_99110,plain,(
    r2_hidden('#skF_13'('#skF_9'('#skF_11')),k1_relat_1('#skF_11')) ),
    inference(splitRight,[status(thm)],[c_97615])).

tff(c_1593,plain,(
    ! [C_1610,A_1611] :
      ( k1_tarski(C_1610) != k10_relat_1(A_1611,k1_tarski('#skF_9'(A_1611)))
      | v2_funct_1(A_1611)
      | ~ v1_funct_1(A_1611)
      | ~ v1_relat_1(A_1611) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1597,plain,(
    ! [C_1610] :
      ( k1_tarski(C_1610) != k1_tarski('#skF_13'('#skF_9'('#skF_11')))
      | v2_funct_1('#skF_11')
      | ~ v1_funct_1('#skF_11')
      | ~ v1_relat_1('#skF_11')
      | k10_relat_1('#skF_11',k1_tarski('#skF_9'('#skF_11'))) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_1593])).

tff(c_1608,plain,(
    ! [C_1610] :
      ( k1_tarski(C_1610) != k1_tarski('#skF_13'('#skF_9'('#skF_11')))
      | v2_funct_1('#skF_11')
      | k10_relat_1('#skF_11',k1_tarski('#skF_9'('#skF_11'))) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_1597])).

tff(c_1609,plain,(
    ! [C_1610] :
      ( k1_tarski(C_1610) != k1_tarski('#skF_13'('#skF_9'('#skF_11')))
      | k10_relat_1('#skF_11',k1_tarski('#skF_9'('#skF_11'))) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_1608])).

tff(c_1648,plain,(
    ! [C_1610] : k1_tarski(C_1610) != k1_tarski('#skF_13'('#skF_9'('#skF_11'))) ),
    inference(splitLeft,[status(thm)],[c_1609])).

tff(c_1652,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1648])).

tff(c_1653,plain,(
    k10_relat_1('#skF_11',k1_tarski('#skF_9'('#skF_11'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1609])).

tff(c_99111,plain,(
    r2_hidden('#skF_9'('#skF_11'),k2_relat_1('#skF_11')) ),
    inference(splitRight,[status(thm)],[c_97615])).

tff(c_97136,plain,
    ( k1_funct_1('#skF_11','#skF_13'('#skF_9'('#skF_11'))) = '#skF_9'('#skF_11')
    | ~ r2_hidden('#skF_9'('#skF_11'),k2_relat_1('#skF_11'))
    | ~ v1_funct_1('#skF_11')
    | ~ v1_relat_1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_97126,c_34])).

tff(c_97617,plain,
    ( k1_funct_1('#skF_11','#skF_13'('#skF_9'('#skF_11'))) = '#skF_9'('#skF_11')
    | ~ r2_hidden('#skF_9'('#skF_11'),k2_relat_1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_97136])).

tff(c_102204,plain,(
    k1_funct_1('#skF_11','#skF_13'('#skF_9'('#skF_11'))) = '#skF_9'('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99111,c_97617])).

tff(c_102228,plain,
    ( ~ v1_xboole_0(k10_relat_1('#skF_11',k1_tarski('#skF_9'('#skF_11'))))
    | ~ r2_hidden('#skF_13'('#skF_9'('#skF_11')),k1_relat_1('#skF_11'))
    | ~ v1_funct_1('#skF_11')
    | ~ v1_relat_1('#skF_11') ),
    inference(superposition,[status(thm),theory(equality)],[c_102204,c_3771])).

tff(c_102757,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_99110,c_97,c_1653,c_102228])).

tff(c_102759,plain,(
    v2_funct_1('#skF_11') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_102770,plain,(
    ! [A_27866,B_27867] :
      ( r1_xboole_0(k1_tarski(A_27866),B_27867)
      | r2_hidden(A_27866,B_27867) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_52,plain,(
    ! [B_59,A_58] :
      ( r1_xboole_0(B_59,A_58)
      | ~ r1_xboole_0(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_102773,plain,(
    ! [B_27867,A_27866] :
      ( r1_xboole_0(B_27867,k1_tarski(A_27866))
      | r2_hidden(A_27866,B_27867) ) ),
    inference(resolution,[status(thm)],[c_102770,c_52])).

tff(c_102795,plain,(
    ! [B_27875,A_27876] :
      ( k10_relat_1(B_27875,A_27876) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_27875),A_27876)
      | ~ v1_relat_1(B_27875) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_102804,plain,(
    ! [B_27875,A_27866] :
      ( k10_relat_1(B_27875,k1_tarski(A_27866)) = k1_xboole_0
      | ~ v1_relat_1(B_27875)
      | r2_hidden(A_27866,k2_relat_1(B_27875)) ) ),
    inference(resolution,[status(thm)],[c_102773,c_102795])).

tff(c_104666,plain,(
    ! [A_30064,B_30065] :
      ( k10_relat_1(A_30064,k1_tarski(B_30065)) = k1_tarski('#skF_10'(A_30064,B_30065))
      | ~ r2_hidden(B_30065,k2_relat_1(A_30064))
      | ~ v2_funct_1(A_30064)
      | ~ v1_funct_1(A_30064)
      | ~ v1_relat_1(A_30064) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_113265,plain,(
    ! [B_43587,A_43588] :
      ( k10_relat_1(B_43587,k1_tarski(A_43588)) = k1_tarski('#skF_10'(B_43587,A_43588))
      | ~ v2_funct_1(B_43587)
      | ~ v1_funct_1(B_43587)
      | k10_relat_1(B_43587,k1_tarski(A_43588)) = k1_xboole_0
      | ~ v1_relat_1(B_43587) ) ),
    inference(resolution,[status(thm)],[c_102804,c_104666])).

tff(c_102758,plain,(
    ! [C_88] : ~ r1_tarski(k10_relat_1('#skF_11',k1_tarski('#skF_12')),k1_tarski(C_88)) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_113329,plain,(
    ! [C_88] :
      ( ~ r1_tarski(k1_tarski('#skF_10'('#skF_11','#skF_12')),k1_tarski(C_88))
      | ~ v2_funct_1('#skF_11')
      | ~ v1_funct_1('#skF_11')
      | k10_relat_1('#skF_11',k1_tarski('#skF_12')) = k1_xboole_0
      | ~ v1_relat_1('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113265,c_102758])).

tff(c_113544,plain,(
    ! [C_88] :
      ( ~ r1_tarski(k1_tarski('#skF_10'('#skF_11','#skF_12')),k1_tarski(C_88))
      | k10_relat_1('#skF_11',k1_tarski('#skF_12')) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_102759,c_113329])).

tff(c_113695,plain,(
    ! [C_43772] : ~ r1_tarski(k1_tarski('#skF_10'('#skF_11','#skF_12')),k1_tarski(C_43772)) ),
    inference(splitLeft,[status(thm)],[c_113544])).

tff(c_113721,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_68,c_113695])).

tff(c_113722,plain,(
    k10_relat_1('#skF_11',k1_tarski('#skF_12')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_113544])).

tff(c_113724,plain,(
    ! [C_88] : ~ r1_tarski(k1_xboole_0,k1_tarski(C_88)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113722,c_102758])).

tff(c_113729,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_113724])).

%------------------------------------------------------------------------------
