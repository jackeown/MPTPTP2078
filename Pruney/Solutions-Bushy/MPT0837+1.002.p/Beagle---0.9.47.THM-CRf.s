%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0837+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:56 EST 2020

% Result     : Theorem 9.15s
% Output     : CNFRefutation 9.15s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 432 expanded)
%              Number of leaves         :   31 ( 152 expanded)
%              Depth                    :    9
%              Number of atoms          :  240 (1027 expanded)
%              Number of equality atoms :   10 (  45 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k2_relset_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_5 > #skF_11 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_9 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ! [D] :
                    ( r2_hidden(D,k2_relset_1(B,A,C))
                  <=> ? [E] :
                        ( m1_subset_1(E,B)
                        & r2_hidden(k4_tarski(E,D),C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_35,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_32,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3474,plain,(
    ! [A_300,B_301,C_302] :
      ( k2_relset_1(A_300,B_301,C_302) = k2_relat_1(C_302)
      | ~ m1_subset_1(C_302,k1_zfmisc_1(k2_zfmisc_1(A_300,B_301))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3482,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_32,c_3474])).

tff(c_48,plain,
    ( m1_subset_1('#skF_10','#skF_7')
    | r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_61,plain,(
    r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_3486,plain,(
    r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3482,c_61])).

tff(c_2,plain,(
    ! [A_1,C_16] :
      ( r2_hidden(k4_tarski('#skF_4'(A_1,k2_relat_1(A_1),C_16),C_16),A_1)
      | ~ r2_hidden(C_16,k2_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_20] : m1_subset_1('#skF_5'(A_20),A_20) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_26,plain,(
    ! [A_31,B_32] :
      ( r2_hidden(A_31,B_32)
      | v1_xboole_0(B_32)
      | ~ m1_subset_1(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_34,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3447,plain,(
    ! [A_287,C_288,B_289] :
      ( m1_subset_1(A_287,C_288)
      | ~ m1_subset_1(B_289,k1_zfmisc_1(C_288))
      | ~ r2_hidden(A_287,B_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3453,plain,(
    ! [A_287] :
      ( m1_subset_1(A_287,k2_zfmisc_1('#skF_7','#skF_6'))
      | ~ r2_hidden(A_287,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_32,c_3447])).

tff(c_3436,plain,(
    ! [C_280,A_281,D_282] :
      ( r2_hidden(C_280,k2_relat_1(A_281))
      | ~ r2_hidden(k4_tarski(D_282,C_280),A_281) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3468,plain,(
    ! [C_297,B_298,D_299] :
      ( r2_hidden(C_297,k2_relat_1(B_298))
      | v1_xboole_0(B_298)
      | ~ m1_subset_1(k4_tarski(D_299,C_297),B_298) ) ),
    inference(resolution,[status(thm)],[c_26,c_3436])).

tff(c_3472,plain,(
    ! [C_297,D_299] :
      ( r2_hidden(C_297,k2_relat_1(k2_zfmisc_1('#skF_7','#skF_6')))
      | v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_6'))
      | ~ r2_hidden(k4_tarski(D_299,C_297),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_3453,c_3468])).

tff(c_6910,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_3472])).

tff(c_6963,plain,(
    ! [A_484,B_485,C_486,D_487] :
      ( r2_hidden(k4_tarski(A_484,B_485),k2_zfmisc_1(C_486,D_487))
      | ~ r2_hidden(B_485,D_487)
      | ~ r2_hidden(A_484,C_486) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_30,plain,(
    ! [B_37,A_36] :
      ( ~ v1_xboole_0(B_37)
      | ~ r2_hidden(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_7005,plain,(
    ! [C_491,D_492,B_493,A_494] :
      ( ~ v1_xboole_0(k2_zfmisc_1(C_491,D_492))
      | ~ r2_hidden(B_493,D_492)
      | ~ r2_hidden(A_494,C_491) ) ),
    inference(resolution,[status(thm)],[c_6963,c_30])).

tff(c_7008,plain,(
    ! [B_493,A_494] :
      ( ~ r2_hidden(B_493,'#skF_6')
      | ~ r2_hidden(A_494,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_6910,c_7005])).

tff(c_7010,plain,(
    ! [A_495] : ~ r2_hidden(A_495,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_7008])).

tff(c_7022,plain,(
    ! [A_31] :
      ( v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_31,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_26,c_7010])).

tff(c_7027,plain,(
    ! [A_31] : ~ m1_subset_1(A_31,'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_7022])).

tff(c_115,plain,(
    ! [A_109,B_110,C_111] :
      ( k2_relset_1(A_109,B_110,C_111) = k2_relat_1(C_111)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_109,B_110))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_123,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_32,c_115])).

tff(c_127,plain,(
    r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_61])).

tff(c_82,plain,(
    ! [A_91,C_92,B_93] :
      ( m1_subset_1(A_91,C_92)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(C_92))
      | ~ r2_hidden(A_91,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_88,plain,(
    ! [A_91] :
      ( m1_subset_1(A_91,k2_zfmisc_1('#skF_7','#skF_6'))
      | ~ r2_hidden(A_91,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_32,c_82])).

tff(c_76,plain,(
    ! [C_88,A_89,D_90] :
      ( r2_hidden(C_88,k2_relat_1(A_89))
      | ~ r2_hidden(k4_tarski(D_90,C_88),A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_110,plain,(
    ! [C_106,B_107,D_108] :
      ( r2_hidden(C_106,k2_relat_1(B_107))
      | v1_xboole_0(B_107)
      | ~ m1_subset_1(k4_tarski(D_108,C_106),B_107) ) ),
    inference(resolution,[status(thm)],[c_26,c_76])).

tff(c_114,plain,(
    ! [C_106,D_108] :
      ( r2_hidden(C_106,k2_relat_1(k2_zfmisc_1('#skF_7','#skF_6')))
      | v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_6'))
      | ~ r2_hidden(k4_tarski(D_108,C_106),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_88,c_110])).

tff(c_346,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_170,plain,(
    ! [A_115,B_116,C_117,D_118] :
      ( r2_hidden(k4_tarski(A_115,B_116),k2_zfmisc_1(C_117,D_118))
      | ~ r2_hidden(B_116,D_118)
      | ~ r2_hidden(A_115,C_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_190,plain,(
    ! [C_117,D_118,B_116,A_115] :
      ( ~ v1_xboole_0(k2_zfmisc_1(C_117,D_118))
      | ~ r2_hidden(B_116,D_118)
      | ~ r2_hidden(A_115,C_117) ) ),
    inference(resolution,[status(thm)],[c_170,c_30])).

tff(c_349,plain,(
    ! [B_116,A_115] :
      ( ~ r2_hidden(B_116,'#skF_6')
      | ~ r2_hidden(A_115,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_346,c_190])).

tff(c_351,plain,(
    ! [A_141] : ~ r2_hidden(A_141,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_349])).

tff(c_363,plain,(
    ! [A_31] :
      ( v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_31,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_26,c_351])).

tff(c_369,plain,(
    ! [A_142] : ~ m1_subset_1(A_142,'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_363])).

tff(c_379,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_14,c_369])).

tff(c_381,plain,(
    ! [B_143] : ~ r2_hidden(B_143,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_349])).

tff(c_393,plain,(
    ! [A_31] :
      ( v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_31,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_26,c_381])).

tff(c_404,plain,(
    ! [A_147] : ~ m1_subset_1(A_147,'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_393])).

tff(c_414,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_14,c_404])).

tff(c_416,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_90,plain,(
    ! [A_94,C_95,B_96,D_97] :
      ( r2_hidden(A_94,C_95)
      | ~ r2_hidden(k4_tarski(A_94,B_96),k2_zfmisc_1(C_95,D_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3290,plain,(
    ! [A_267,C_268,D_269,B_270] :
      ( r2_hidden(A_267,C_268)
      | v1_xboole_0(k2_zfmisc_1(C_268,D_269))
      | ~ m1_subset_1(k4_tarski(A_267,B_270),k2_zfmisc_1(C_268,D_269)) ) ),
    inference(resolution,[status(thm)],[c_26,c_90])).

tff(c_3301,plain,(
    ! [A_267,B_270] :
      ( r2_hidden(A_267,'#skF_7')
      | v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_6'))
      | ~ r2_hidden(k4_tarski(A_267,B_270),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_88,c_3290])).

tff(c_3307,plain,(
    ! [A_271,B_272] :
      ( r2_hidden(A_271,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_271,B_272),'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_416,c_3301])).

tff(c_3330,plain,(
    ! [C_275] :
      ( r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_275),'#skF_7')
      | ~ r2_hidden(C_275,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_2,c_3307])).

tff(c_24,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(A_29,B_30)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3427,plain,(
    ! [C_279] :
      ( m1_subset_1('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_279),'#skF_7')
      | ~ r2_hidden(C_279,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_3330,c_24])).

tff(c_191,plain,(
    ! [A_119,C_120] :
      ( r2_hidden(k4_tarski('#skF_4'(A_119,k2_relat_1(A_119),C_120),C_120),A_119)
      | ~ r2_hidden(C_120,k2_relat_1(A_119)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_42,plain,(
    ! [E_79] :
      ( m1_subset_1('#skF_10','#skF_7')
      | ~ r2_hidden(k4_tarski(E_79,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_79,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_70,plain,(
    ! [E_79] :
      ( ~ r2_hidden(k4_tarski(E_79,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_79,'#skF_7') ) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_210,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_8',k2_relat_1('#skF_8'),'#skF_11'),'#skF_7')
    | ~ r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_191,c_70])).

tff(c_223,plain,(
    ~ m1_subset_1('#skF_4'('#skF_8',k2_relat_1('#skF_8'),'#skF_11'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_210])).

tff(c_3430,plain,(
    ~ r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_3427,c_223])).

tff(c_3434,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_3430])).

tff(c_3435,plain,(
    m1_subset_1('#skF_10','#skF_7') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_7029,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7027,c_3435])).

tff(c_7031,plain,(
    ! [B_496] : ~ r2_hidden(B_496,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_7008])).

tff(c_7043,plain,(
    ! [A_31] :
      ( v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_31,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_26,c_7031])).

tff(c_7049,plain,(
    ! [A_497] : ~ m1_subset_1(A_497,'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_7043])).

tff(c_7059,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_14,c_7049])).

tff(c_7061,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_3472])).

tff(c_3442,plain,(
    ! [A_283,C_284,B_285,D_286] :
      ( r2_hidden(A_283,C_284)
      | ~ r2_hidden(k4_tarski(A_283,B_285),k2_zfmisc_1(C_284,D_286)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_9374,plain,(
    ! [A_663,C_664,D_665,B_666] :
      ( r2_hidden(A_663,C_664)
      | v1_xboole_0(k2_zfmisc_1(C_664,D_665))
      | ~ m1_subset_1(k4_tarski(A_663,B_666),k2_zfmisc_1(C_664,D_665)) ) ),
    inference(resolution,[status(thm)],[c_26,c_3442])).

tff(c_9385,plain,(
    ! [A_663,B_666] :
      ( r2_hidden(A_663,'#skF_7')
      | v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_6'))
      | ~ r2_hidden(k4_tarski(A_663,B_666),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_3453,c_9374])).

tff(c_9391,plain,(
    ! [A_667,B_668] :
      ( r2_hidden(A_667,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_667,B_668),'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_7061,c_9385])).

tff(c_10441,plain,(
    ! [C_742] :
      ( r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_742),'#skF_7')
      | ~ r2_hidden(C_742,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_2,c_9391])).

tff(c_11435,plain,(
    ! [C_770] :
      ( m1_subset_1('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_770),'#skF_7')
      | ~ r2_hidden(C_770,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_10441,c_24])).

tff(c_6835,plain,(
    ! [A_471,C_472] :
      ( r2_hidden(k4_tarski('#skF_4'(A_471,k2_relat_1(A_471),C_472),C_472),A_471)
      | ~ r2_hidden(C_472,k2_relat_1(A_471)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3664,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_3472])).

tff(c_3543,plain,(
    ! [A_310,B_311,C_312,D_313] :
      ( r2_hidden(k4_tarski(A_310,B_311),k2_zfmisc_1(C_312,D_313))
      | ~ r2_hidden(B_311,D_313)
      | ~ r2_hidden(A_310,C_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3563,plain,(
    ! [C_312,D_313,B_311,A_310] :
      ( ~ v1_xboole_0(k2_zfmisc_1(C_312,D_313))
      | ~ r2_hidden(B_311,D_313)
      | ~ r2_hidden(A_310,C_312) ) ),
    inference(resolution,[status(thm)],[c_3543,c_30])).

tff(c_3667,plain,(
    ! [B_311,A_310] :
      ( ~ r2_hidden(B_311,'#skF_6')
      | ~ r2_hidden(A_310,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_3664,c_3563])).

tff(c_3669,plain,(
    ! [A_332] : ~ r2_hidden(A_332,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_3667])).

tff(c_3681,plain,(
    ! [A_31] :
      ( v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_31,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_26,c_3669])).

tff(c_3686,plain,(
    ! [A_31] : ~ m1_subset_1(A_31,'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_3681])).

tff(c_3688,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3686,c_3435])).

tff(c_3690,plain,(
    ! [B_333] : ~ r2_hidden(B_333,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_3667])).

tff(c_3702,plain,(
    ! [A_31] :
      ( v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_31,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_26,c_3690])).

tff(c_3717,plain,(
    ! [A_337] : ~ m1_subset_1(A_337,'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_3702])).

tff(c_3727,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_14,c_3717])).

tff(c_3729,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_3472])).

tff(c_6623,plain,(
    ! [A_451,C_452,D_453,B_454] :
      ( r2_hidden(A_451,C_452)
      | v1_xboole_0(k2_zfmisc_1(C_452,D_453))
      | ~ m1_subset_1(k4_tarski(A_451,B_454),k2_zfmisc_1(C_452,D_453)) ) ),
    inference(resolution,[status(thm)],[c_26,c_3442])).

tff(c_6634,plain,(
    ! [A_451,B_454] :
      ( r2_hidden(A_451,'#skF_7')
      | v1_xboole_0(k2_zfmisc_1('#skF_7','#skF_6'))
      | ~ r2_hidden(k4_tarski(A_451,B_454),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_3453,c_6623])).

tff(c_6640,plain,(
    ! [A_455,B_456] :
      ( r2_hidden(A_455,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_455,B_456),'#skF_8') ) ),
    inference(negUnitSimplification,[status(thm)],[c_3729,c_6634])).

tff(c_6663,plain,(
    ! [C_459] :
      ( r2_hidden('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_459),'#skF_7')
      | ~ r2_hidden(C_459,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_2,c_6640])).

tff(c_6755,plain,(
    ! [C_463] :
      ( m1_subset_1('#skF_4'('#skF_8',k2_relat_1('#skF_8'),C_463),'#skF_7')
      | ~ r2_hidden(C_463,k2_relat_1('#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_6663,c_24])).

tff(c_3602,plain,(
    ! [A_328,C_329] :
      ( r2_hidden(k4_tarski('#skF_4'(A_328,k2_relat_1(A_328),C_329),C_329),A_328)
      | ~ r2_hidden(C_329,k2_relat_1(A_328)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_40,plain,(
    ! [E_79] :
      ( r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8')
      | ~ r2_hidden(k4_tarski(E_79,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_79,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3499,plain,(
    ! [E_79] :
      ( ~ r2_hidden(k4_tarski(E_79,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_79,'#skF_7') ) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_3608,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_8',k2_relat_1('#skF_8'),'#skF_11'),'#skF_7')
    | ~ r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_3602,c_3499])).

tff(c_3633,plain,(
    ~ m1_subset_1('#skF_4'('#skF_8',k2_relat_1('#skF_8'),'#skF_11'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3486,c_3608])).

tff(c_6758,plain,(
    ~ r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6755,c_3633])).

tff(c_6762,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3486,c_6758])).

tff(c_6763,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_4,plain,(
    ! [C_16,A_1,D_19] :
      ( r2_hidden(C_16,k2_relat_1(A_1))
      | ~ r2_hidden(k4_tarski(D_19,C_16),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6773,plain,(
    r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6763,c_4])).

tff(c_38,plain,(
    ! [E_79] :
      ( ~ r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8'))
      | ~ r2_hidden(k4_tarski(E_79,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_79,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_6786,plain,(
    ! [E_79] :
      ( ~ r2_hidden(k4_tarski(E_79,'#skF_11'),'#skF_8')
      | ~ m1_subset_1(E_79,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6773,c_3482,c_38])).

tff(c_6839,plain,
    ( ~ m1_subset_1('#skF_4'('#skF_8',k2_relat_1('#skF_8'),'#skF_11'),'#skF_7')
    | ~ r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_6835,c_6786])).

tff(c_6863,plain,(
    ~ m1_subset_1('#skF_4'('#skF_8',k2_relat_1('#skF_8'),'#skF_11'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3486,c_6839])).

tff(c_11438,plain,(
    ~ r2_hidden('#skF_11',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_11435,c_6863])).

tff(c_11442,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3486,c_11438])).

tff(c_11444,plain,(
    ~ r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_46,plain,
    ( r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8')
    | r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_11481,plain,(
    r2_hidden(k4_tarski('#skF_10','#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_11444,c_46])).

tff(c_11491,plain,(
    r2_hidden('#skF_9',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_11481,c_4])).

tff(c_11506,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_11491,c_30])).

tff(c_11549,plain,(
    ! [A_797,B_798,C_799] :
      ( k2_relset_1(A_797,B_798,C_799) = k2_relat_1(C_799)
      | ~ m1_subset_1(C_799,k1_zfmisc_1(k2_zfmisc_1(A_797,B_798))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_11557,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_32,c_11549])).

tff(c_11505,plain,(
    m1_subset_1('#skF_9',k2_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_11491,c_24])).

tff(c_11520,plain,(
    ! [A_791,B_792,C_793] :
      ( k2_relset_1(A_791,B_792,C_793) = k2_relat_1(C_793)
      | ~ m1_subset_1(C_793,k1_zfmisc_1(k2_zfmisc_1(A_791,B_792))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_11528,plain,(
    k2_relset_1('#skF_7','#skF_6','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_32,c_11520])).

tff(c_44,plain,
    ( ~ r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8'))
    | r2_hidden('#skF_11',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_11494,plain,(
    ~ r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_11444,c_44])).

tff(c_11498,plain,
    ( v1_xboole_0(k2_relset_1('#skF_7','#skF_6','#skF_8'))
    | ~ m1_subset_1('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(resolution,[status(thm)],[c_26,c_11494])).

tff(c_11508,plain,(
    ~ m1_subset_1('#skF_9',k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_11498])).

tff(c_11530,plain,(
    ~ m1_subset_1('#skF_9',k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11528,c_11508])).

tff(c_11535,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11505,c_11530])).

tff(c_11536,plain,(
    v1_xboole_0(k2_relset_1('#skF_7','#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_11498])).

tff(c_11560,plain,(
    v1_xboole_0(k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11557,c_11536])).

tff(c_11565,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11506,c_11560])).

%------------------------------------------------------------------------------
