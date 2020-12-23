%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:03 EST 2020

% Result     : Theorem 7.16s
% Output     : CNFRefutation 7.16s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 212 expanded)
%              Number of leaves         :   42 (  91 expanded)
%              Depth                    :    9
%              Number of atoms          :  184 ( 499 expanded)
%              Number of equality atoms :   15 (  32 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k1_relset_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_11 > #skF_6 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_5 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_65,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ! [D] :
                    ( m1_subset_1(D,A)
                   => ( r2_hidden(D,k1_relset_1(A,B,C))
                    <=> ? [E] :
                          ( m1_subset_1(E,B)
                          & r2_hidden(k4_tarski(D,E),C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relset_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(c_42,plain,(
    ! [A_35,B_36] : v1_relat_1(k2_zfmisc_1(A_35,B_36)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_62,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_82,plain,(
    ! [B_98,A_99] :
      ( v1_relat_1(B_98)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(A_99))
      | ~ v1_relat_1(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_85,plain,
    ( v1_relat_1('#skF_10')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_62,c_82])).

tff(c_88,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_85])).

tff(c_3821,plain,(
    ! [A_434,B_435,C_436] :
      ( k1_relset_1(A_434,B_435,C_436) = k1_relat_1(C_436)
      | ~ m1_subset_1(C_436,k1_zfmisc_1(k2_zfmisc_1(A_434,B_435))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3825,plain,(
    k1_relset_1('#skF_8','#skF_9','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_62,c_3821])).

tff(c_312,plain,(
    ! [A_152,B_153,C_154] :
      ( k1_relset_1(A_152,B_153,C_154) = k1_relat_1(C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_316,plain,(
    k1_relset_1('#skF_8','#skF_9','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_62,c_312])).

tff(c_78,plain,
    ( r2_hidden('#skF_11',k1_relset_1('#skF_8','#skF_9','#skF_10'))
    | m1_subset_1('#skF_12','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_89,plain,(
    m1_subset_1('#skF_12','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_74,plain,
    ( r2_hidden('#skF_11',k1_relset_1('#skF_8','#skF_9','#skF_10'))
    | r2_hidden(k4_tarski('#skF_11','#skF_12'),'#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_141,plain,(
    r2_hidden(k4_tarski('#skF_11','#skF_12'),'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_32,plain,(
    ! [C_31,A_16,D_34] :
      ( r2_hidden(C_31,k1_relat_1(A_16))
      | ~ r2_hidden(k4_tarski(C_31,D_34),A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_148,plain,(
    r2_hidden('#skF_11',k1_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_141,c_32])).

tff(c_150,plain,(
    ! [A_123,B_124,C_125] :
      ( k1_relset_1(A_123,B_124,C_125) = k1_relat_1(C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_154,plain,(
    k1_relset_1('#skF_8','#skF_9','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_62,c_150])).

tff(c_68,plain,(
    ! [E_91] :
      ( ~ r2_hidden(k4_tarski('#skF_11',E_91),'#skF_10')
      | ~ m1_subset_1(E_91,'#skF_9')
      | ~ r2_hidden('#skF_11',k1_relset_1('#skF_8','#skF_9','#skF_10')) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_269,plain,(
    ! [E_146] :
      ( ~ r2_hidden(k4_tarski('#skF_11',E_146),'#skF_10')
      | ~ m1_subset_1(E_146,'#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_154,c_68])).

tff(c_276,plain,(
    ~ m1_subset_1('#skF_12','#skF_9') ),
    inference(resolution,[status(thm)],[c_141,c_269])).

tff(c_283,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_276])).

tff(c_284,plain,(
    r2_hidden('#skF_11',k1_relset_1('#skF_8','#skF_9','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_318,plain,(
    r2_hidden('#skF_11',k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_284])).

tff(c_108,plain,(
    ! [C_115,B_116,A_117] :
      ( v5_relat_1(C_115,B_116)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_117,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_112,plain,(
    v5_relat_1('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_62,c_108])).

tff(c_52,plain,(
    ! [A_43] :
      ( k10_relat_1(A_43,k2_relat_1(A_43)) = k1_relat_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_420,plain,(
    ! [A_171,B_172,C_173] :
      ( r2_hidden('#skF_7'(A_171,B_172,C_173),k2_relat_1(C_173))
      | ~ r2_hidden(A_171,k10_relat_1(C_173,B_172))
      | ~ v1_relat_1(C_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_114,plain,(
    ! [B_118,A_119] :
      ( r1_tarski(k2_relat_1(B_118),A_119)
      | ~ v5_relat_1(B_118,A_119)
      | ~ v1_relat_1(B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_290,plain,(
    ! [B_147,A_148] :
      ( k3_xboole_0(k2_relat_1(B_147),A_148) = k2_relat_1(B_147)
      | ~ v5_relat_1(B_147,A_148)
      | ~ v1_relat_1(B_147) ) ),
    inference(resolution,[status(thm)],[c_114,c_20])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_302,plain,(
    ! [D_6,A_148,B_147] :
      ( r2_hidden(D_6,A_148)
      | ~ r2_hidden(D_6,k2_relat_1(B_147))
      | ~ v5_relat_1(B_147,A_148)
      | ~ v1_relat_1(B_147) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_290,c_4])).

tff(c_1555,plain,(
    ! [A_274,B_275,C_276,A_277] :
      ( r2_hidden('#skF_7'(A_274,B_275,C_276),A_277)
      | ~ v5_relat_1(C_276,A_277)
      | ~ r2_hidden(A_274,k10_relat_1(C_276,B_275))
      | ~ v1_relat_1(C_276) ) ),
    inference(resolution,[status(thm)],[c_420,c_302])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,B_10)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1587,plain,(
    ! [A_278,B_279,C_280,A_281] :
      ( m1_subset_1('#skF_7'(A_278,B_279,C_280),A_281)
      | ~ v5_relat_1(C_280,A_281)
      | ~ r2_hidden(A_278,k10_relat_1(C_280,B_279))
      | ~ v1_relat_1(C_280) ) ),
    inference(resolution,[status(thm)],[c_1555,c_22])).

tff(c_3716,plain,(
    ! [A_402,A_403,A_404] :
      ( m1_subset_1('#skF_7'(A_402,k2_relat_1(A_403),A_403),A_404)
      | ~ v5_relat_1(A_403,A_404)
      | ~ r2_hidden(A_402,k1_relat_1(A_403))
      | ~ v1_relat_1(A_403)
      | ~ v1_relat_1(A_403) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1587])).

tff(c_428,plain,(
    ! [A_174,B_175,C_176] :
      ( r2_hidden(k4_tarski(A_174,'#skF_7'(A_174,B_175,C_176)),C_176)
      | ~ r2_hidden(A_174,k10_relat_1(C_176,B_175))
      | ~ v1_relat_1(C_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_285,plain,(
    ~ r2_hidden(k4_tarski('#skF_11','#skF_12'),'#skF_10') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_72,plain,(
    ! [E_91] :
      ( ~ r2_hidden(k4_tarski('#skF_11',E_91),'#skF_10')
      | ~ m1_subset_1(E_91,'#skF_9')
      | r2_hidden(k4_tarski('#skF_11','#skF_12'),'#skF_10') ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_328,plain,(
    ! [E_91] :
      ( ~ r2_hidden(k4_tarski('#skF_11',E_91),'#skF_10')
      | ~ m1_subset_1(E_91,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_285,c_72])).

tff(c_438,plain,(
    ! [B_175] :
      ( ~ m1_subset_1('#skF_7'('#skF_11',B_175,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_11',k10_relat_1('#skF_10',B_175))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_428,c_328])).

tff(c_481,plain,(
    ! [B_180] :
      ( ~ m1_subset_1('#skF_7'('#skF_11',B_180,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_11',k10_relat_1('#skF_10',B_180)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_438])).

tff(c_485,plain,
    ( ~ m1_subset_1('#skF_7'('#skF_11',k2_relat_1('#skF_10'),'#skF_10'),'#skF_9')
    | ~ r2_hidden('#skF_11',k1_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_481])).

tff(c_487,plain,(
    ~ m1_subset_1('#skF_7'('#skF_11',k2_relat_1('#skF_10'),'#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_318,c_485])).

tff(c_3719,plain,
    ( ~ v5_relat_1('#skF_10','#skF_9')
    | ~ r2_hidden('#skF_11',k1_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_3716,c_487])).

tff(c_3739,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_318,c_112,c_3719])).

tff(c_3740,plain,(
    r2_hidden('#skF_11',k1_relset_1('#skF_8','#skF_9','#skF_10')) ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_3827,plain,(
    r2_hidden('#skF_11',k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3825,c_3740])).

tff(c_3758,plain,(
    ! [C_414,B_415,A_416] :
      ( v5_relat_1(C_414,B_415)
      | ~ m1_subset_1(C_414,k1_zfmisc_1(k2_zfmisc_1(A_416,B_415))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_3762,plain,(
    v5_relat_1('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_62,c_3758])).

tff(c_3927,plain,(
    ! [A_452,B_453,C_454] :
      ( r2_hidden('#skF_7'(A_452,B_453,C_454),k2_relat_1(C_454))
      | ~ r2_hidden(A_452,k10_relat_1(C_454,B_453))
      | ~ v1_relat_1(C_454) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3765,plain,(
    ! [B_420,A_421] :
      ( r1_tarski(k2_relat_1(B_420),A_421)
      | ~ v5_relat_1(B_420,A_421)
      | ~ v1_relat_1(B_420) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3799,plain,(
    ! [B_429,A_430] :
      ( k3_xboole_0(k2_relat_1(B_429),A_430) = k2_relat_1(B_429)
      | ~ v5_relat_1(B_429,A_430)
      | ~ v1_relat_1(B_429) ) ),
    inference(resolution,[status(thm)],[c_3765,c_20])).

tff(c_3808,plain,(
    ! [D_6,A_430,B_429] :
      ( r2_hidden(D_6,A_430)
      | ~ r2_hidden(D_6,k2_relat_1(B_429))
      | ~ v5_relat_1(B_429,A_430)
      | ~ v1_relat_1(B_429) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3799,c_4])).

tff(c_4834,plain,(
    ! [A_537,B_538,C_539,A_540] :
      ( r2_hidden('#skF_7'(A_537,B_538,C_539),A_540)
      | ~ v5_relat_1(C_539,A_540)
      | ~ r2_hidden(A_537,k10_relat_1(C_539,B_538))
      | ~ v1_relat_1(C_539) ) ),
    inference(resolution,[status(thm)],[c_3927,c_3808])).

tff(c_4865,plain,(
    ! [A_541,B_542,C_543,A_544] :
      ( m1_subset_1('#skF_7'(A_541,B_542,C_543),A_544)
      | ~ v5_relat_1(C_543,A_544)
      | ~ r2_hidden(A_541,k10_relat_1(C_543,B_542))
      | ~ v1_relat_1(C_543) ) ),
    inference(resolution,[status(thm)],[c_4834,c_22])).

tff(c_7168,plain,(
    ! [A_676,A_677,A_678] :
      ( m1_subset_1('#skF_7'(A_676,k2_relat_1(A_677),A_677),A_678)
      | ~ v5_relat_1(A_677,A_678)
      | ~ r2_hidden(A_676,k1_relat_1(A_677))
      | ~ v1_relat_1(A_677)
      | ~ v1_relat_1(A_677) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_4865])).

tff(c_3936,plain,(
    ! [A_458,B_459,C_460] :
      ( r2_hidden(k4_tarski(A_458,'#skF_7'(A_458,B_459,C_460)),C_460)
      | ~ r2_hidden(A_458,k10_relat_1(C_460,B_459))
      | ~ v1_relat_1(C_460) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_3741,plain,(
    ~ m1_subset_1('#skF_12','#skF_9') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_76,plain,(
    ! [E_91] :
      ( ~ r2_hidden(k4_tarski('#skF_11',E_91),'#skF_10')
      | ~ m1_subset_1(E_91,'#skF_9')
      | m1_subset_1('#skF_12','#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_3779,plain,(
    ! [E_91] :
      ( ~ r2_hidden(k4_tarski('#skF_11',E_91),'#skF_10')
      | ~ m1_subset_1(E_91,'#skF_9') ) ),
    inference(negUnitSimplification,[status(thm)],[c_3741,c_76])).

tff(c_3946,plain,(
    ! [B_459] :
      ( ~ m1_subset_1('#skF_7'('#skF_11',B_459,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_11',k10_relat_1('#skF_10',B_459))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_3936,c_3779])).

tff(c_3975,plain,(
    ! [B_464] :
      ( ~ m1_subset_1('#skF_7'('#skF_11',B_464,'#skF_10'),'#skF_9')
      | ~ r2_hidden('#skF_11',k10_relat_1('#skF_10',B_464)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_3946])).

tff(c_3979,plain,
    ( ~ m1_subset_1('#skF_7'('#skF_11',k2_relat_1('#skF_10'),'#skF_10'),'#skF_9')
    | ~ r2_hidden('#skF_11',k1_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_3975])).

tff(c_3981,plain,(
    ~ m1_subset_1('#skF_7'('#skF_11',k2_relat_1('#skF_10'),'#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_3827,c_3979])).

tff(c_7171,plain,
    ( ~ v5_relat_1('#skF_10','#skF_9')
    | ~ r2_hidden('#skF_11',k1_relat_1('#skF_10'))
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_7168,c_3981])).

tff(c_7191,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_3827,c_3762,c_7171])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n015.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 17:55:38 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.16/2.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.16/2.45  
% 7.16/2.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.16/2.45  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k1_relset_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_11 > #skF_6 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_7 > #skF_8 > #skF_5 > #skF_12 > #skF_4
% 7.16/2.45  
% 7.16/2.45  %Foreground sorts:
% 7.16/2.45  
% 7.16/2.45  
% 7.16/2.45  %Background operators:
% 7.16/2.45  
% 7.16/2.45  
% 7.16/2.45  %Foreground operators:
% 7.16/2.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.16/2.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.16/2.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.16/2.45  tff('#skF_11', type, '#skF_11': $i).
% 7.16/2.45  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 7.16/2.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.16/2.45  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.16/2.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.16/2.45  tff('#skF_10', type, '#skF_10': $i).
% 7.16/2.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.16/2.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.16/2.45  tff('#skF_9', type, '#skF_9': $i).
% 7.16/2.45  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.16/2.45  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.16/2.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.16/2.45  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 7.16/2.45  tff('#skF_8', type, '#skF_8': $i).
% 7.16/2.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.16/2.45  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.16/2.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.16/2.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.16/2.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.16/2.45  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.16/2.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.16/2.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.16/2.45  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.16/2.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.16/2.45  tff('#skF_12', type, '#skF_12': $i).
% 7.16/2.45  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.16/2.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.16/2.45  
% 7.16/2.47  tff(f_65, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.16/2.47  tff(f_111, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (![D]: (m1_subset_1(D, A) => (r2_hidden(D, k1_relset_1(A, B, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(D, E), C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relset_1)).
% 7.16/2.47  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.16/2.47  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.16/2.47  tff(f_63, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 7.16/2.47  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.16/2.47  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 7.16/2.47  tff(f_76, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 7.16/2.47  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 7.16/2.47  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.16/2.47  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 7.16/2.47  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 7.16/2.47  tff(c_42, plain, (![A_35, B_36]: (v1_relat_1(k2_zfmisc_1(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.16/2.47  tff(c_62, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.16/2.47  tff(c_82, plain, (![B_98, A_99]: (v1_relat_1(B_98) | ~m1_subset_1(B_98, k1_zfmisc_1(A_99)) | ~v1_relat_1(A_99))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.16/2.47  tff(c_85, plain, (v1_relat_1('#skF_10') | ~v1_relat_1(k2_zfmisc_1('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_62, c_82])).
% 7.16/2.47  tff(c_88, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_85])).
% 7.16/2.47  tff(c_3821, plain, (![A_434, B_435, C_436]: (k1_relset_1(A_434, B_435, C_436)=k1_relat_1(C_436) | ~m1_subset_1(C_436, k1_zfmisc_1(k2_zfmisc_1(A_434, B_435))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.16/2.47  tff(c_3825, plain, (k1_relset_1('#skF_8', '#skF_9', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_62, c_3821])).
% 7.16/2.47  tff(c_312, plain, (![A_152, B_153, C_154]: (k1_relset_1(A_152, B_153, C_154)=k1_relat_1(C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.16/2.47  tff(c_316, plain, (k1_relset_1('#skF_8', '#skF_9', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_62, c_312])).
% 7.16/2.47  tff(c_78, plain, (r2_hidden('#skF_11', k1_relset_1('#skF_8', '#skF_9', '#skF_10')) | m1_subset_1('#skF_12', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.16/2.47  tff(c_89, plain, (m1_subset_1('#skF_12', '#skF_9')), inference(splitLeft, [status(thm)], [c_78])).
% 7.16/2.47  tff(c_74, plain, (r2_hidden('#skF_11', k1_relset_1('#skF_8', '#skF_9', '#skF_10')) | r2_hidden(k4_tarski('#skF_11', '#skF_12'), '#skF_10')), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.16/2.47  tff(c_141, plain, (r2_hidden(k4_tarski('#skF_11', '#skF_12'), '#skF_10')), inference(splitLeft, [status(thm)], [c_74])).
% 7.16/2.47  tff(c_32, plain, (![C_31, A_16, D_34]: (r2_hidden(C_31, k1_relat_1(A_16)) | ~r2_hidden(k4_tarski(C_31, D_34), A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.16/2.47  tff(c_148, plain, (r2_hidden('#skF_11', k1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_141, c_32])).
% 7.16/2.47  tff(c_150, plain, (![A_123, B_124, C_125]: (k1_relset_1(A_123, B_124, C_125)=k1_relat_1(C_125) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.16/2.47  tff(c_154, plain, (k1_relset_1('#skF_8', '#skF_9', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_62, c_150])).
% 7.16/2.47  tff(c_68, plain, (![E_91]: (~r2_hidden(k4_tarski('#skF_11', E_91), '#skF_10') | ~m1_subset_1(E_91, '#skF_9') | ~r2_hidden('#skF_11', k1_relset_1('#skF_8', '#skF_9', '#skF_10')))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.16/2.47  tff(c_269, plain, (![E_146]: (~r2_hidden(k4_tarski('#skF_11', E_146), '#skF_10') | ~m1_subset_1(E_146, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_154, c_68])).
% 7.16/2.47  tff(c_276, plain, (~m1_subset_1('#skF_12', '#skF_9')), inference(resolution, [status(thm)], [c_141, c_269])).
% 7.16/2.47  tff(c_283, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_276])).
% 7.16/2.47  tff(c_284, plain, (r2_hidden('#skF_11', k1_relset_1('#skF_8', '#skF_9', '#skF_10'))), inference(splitRight, [status(thm)], [c_74])).
% 7.16/2.47  tff(c_318, plain, (r2_hidden('#skF_11', k1_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_316, c_284])).
% 7.16/2.47  tff(c_108, plain, (![C_115, B_116, A_117]: (v5_relat_1(C_115, B_116) | ~m1_subset_1(C_115, k1_zfmisc_1(k2_zfmisc_1(A_117, B_116))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.16/2.47  tff(c_112, plain, (v5_relat_1('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_62, c_108])).
% 7.16/2.47  tff(c_52, plain, (![A_43]: (k10_relat_1(A_43, k2_relat_1(A_43))=k1_relat_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.16/2.47  tff(c_420, plain, (![A_171, B_172, C_173]: (r2_hidden('#skF_7'(A_171, B_172, C_173), k2_relat_1(C_173)) | ~r2_hidden(A_171, k10_relat_1(C_173, B_172)) | ~v1_relat_1(C_173))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.16/2.47  tff(c_114, plain, (![B_118, A_119]: (r1_tarski(k2_relat_1(B_118), A_119) | ~v5_relat_1(B_118, A_119) | ~v1_relat_1(B_118))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.16/2.47  tff(c_20, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.16/2.47  tff(c_290, plain, (![B_147, A_148]: (k3_xboole_0(k2_relat_1(B_147), A_148)=k2_relat_1(B_147) | ~v5_relat_1(B_147, A_148) | ~v1_relat_1(B_147))), inference(resolution, [status(thm)], [c_114, c_20])).
% 7.16/2.47  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.16/2.47  tff(c_302, plain, (![D_6, A_148, B_147]: (r2_hidden(D_6, A_148) | ~r2_hidden(D_6, k2_relat_1(B_147)) | ~v5_relat_1(B_147, A_148) | ~v1_relat_1(B_147))), inference(superposition, [status(thm), theory('equality')], [c_290, c_4])).
% 7.16/2.47  tff(c_1555, plain, (![A_274, B_275, C_276, A_277]: (r2_hidden('#skF_7'(A_274, B_275, C_276), A_277) | ~v5_relat_1(C_276, A_277) | ~r2_hidden(A_274, k10_relat_1(C_276, B_275)) | ~v1_relat_1(C_276))), inference(resolution, [status(thm)], [c_420, c_302])).
% 7.16/2.47  tff(c_22, plain, (![A_9, B_10]: (m1_subset_1(A_9, B_10) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.16/2.47  tff(c_1587, plain, (![A_278, B_279, C_280, A_281]: (m1_subset_1('#skF_7'(A_278, B_279, C_280), A_281) | ~v5_relat_1(C_280, A_281) | ~r2_hidden(A_278, k10_relat_1(C_280, B_279)) | ~v1_relat_1(C_280))), inference(resolution, [status(thm)], [c_1555, c_22])).
% 7.16/2.47  tff(c_3716, plain, (![A_402, A_403, A_404]: (m1_subset_1('#skF_7'(A_402, k2_relat_1(A_403), A_403), A_404) | ~v5_relat_1(A_403, A_404) | ~r2_hidden(A_402, k1_relat_1(A_403)) | ~v1_relat_1(A_403) | ~v1_relat_1(A_403))), inference(superposition, [status(thm), theory('equality')], [c_52, c_1587])).
% 7.16/2.47  tff(c_428, plain, (![A_174, B_175, C_176]: (r2_hidden(k4_tarski(A_174, '#skF_7'(A_174, B_175, C_176)), C_176) | ~r2_hidden(A_174, k10_relat_1(C_176, B_175)) | ~v1_relat_1(C_176))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.16/2.47  tff(c_285, plain, (~r2_hidden(k4_tarski('#skF_11', '#skF_12'), '#skF_10')), inference(splitRight, [status(thm)], [c_74])).
% 7.16/2.47  tff(c_72, plain, (![E_91]: (~r2_hidden(k4_tarski('#skF_11', E_91), '#skF_10') | ~m1_subset_1(E_91, '#skF_9') | r2_hidden(k4_tarski('#skF_11', '#skF_12'), '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.16/2.47  tff(c_328, plain, (![E_91]: (~r2_hidden(k4_tarski('#skF_11', E_91), '#skF_10') | ~m1_subset_1(E_91, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_285, c_72])).
% 7.16/2.47  tff(c_438, plain, (![B_175]: (~m1_subset_1('#skF_7'('#skF_11', B_175, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k10_relat_1('#skF_10', B_175)) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_428, c_328])).
% 7.16/2.47  tff(c_481, plain, (![B_180]: (~m1_subset_1('#skF_7'('#skF_11', B_180, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k10_relat_1('#skF_10', B_180)))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_438])).
% 7.16/2.47  tff(c_485, plain, (~m1_subset_1('#skF_7'('#skF_11', k2_relat_1('#skF_10'), '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k1_relat_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_52, c_481])).
% 7.16/2.47  tff(c_487, plain, (~m1_subset_1('#skF_7'('#skF_11', k2_relat_1('#skF_10'), '#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_318, c_485])).
% 7.16/2.47  tff(c_3719, plain, (~v5_relat_1('#skF_10', '#skF_9') | ~r2_hidden('#skF_11', k1_relat_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_3716, c_487])).
% 7.16/2.47  tff(c_3739, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_318, c_112, c_3719])).
% 7.16/2.47  tff(c_3740, plain, (r2_hidden('#skF_11', k1_relset_1('#skF_8', '#skF_9', '#skF_10'))), inference(splitRight, [status(thm)], [c_78])).
% 7.16/2.47  tff(c_3827, plain, (r2_hidden('#skF_11', k1_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_3825, c_3740])).
% 7.16/2.47  tff(c_3758, plain, (![C_414, B_415, A_416]: (v5_relat_1(C_414, B_415) | ~m1_subset_1(C_414, k1_zfmisc_1(k2_zfmisc_1(A_416, B_415))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.16/2.47  tff(c_3762, plain, (v5_relat_1('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_62, c_3758])).
% 7.16/2.47  tff(c_3927, plain, (![A_452, B_453, C_454]: (r2_hidden('#skF_7'(A_452, B_453, C_454), k2_relat_1(C_454)) | ~r2_hidden(A_452, k10_relat_1(C_454, B_453)) | ~v1_relat_1(C_454))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.16/2.47  tff(c_3765, plain, (![B_420, A_421]: (r1_tarski(k2_relat_1(B_420), A_421) | ~v5_relat_1(B_420, A_421) | ~v1_relat_1(B_420))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.16/2.47  tff(c_3799, plain, (![B_429, A_430]: (k3_xboole_0(k2_relat_1(B_429), A_430)=k2_relat_1(B_429) | ~v5_relat_1(B_429, A_430) | ~v1_relat_1(B_429))), inference(resolution, [status(thm)], [c_3765, c_20])).
% 7.16/2.47  tff(c_3808, plain, (![D_6, A_430, B_429]: (r2_hidden(D_6, A_430) | ~r2_hidden(D_6, k2_relat_1(B_429)) | ~v5_relat_1(B_429, A_430) | ~v1_relat_1(B_429))), inference(superposition, [status(thm), theory('equality')], [c_3799, c_4])).
% 7.16/2.47  tff(c_4834, plain, (![A_537, B_538, C_539, A_540]: (r2_hidden('#skF_7'(A_537, B_538, C_539), A_540) | ~v5_relat_1(C_539, A_540) | ~r2_hidden(A_537, k10_relat_1(C_539, B_538)) | ~v1_relat_1(C_539))), inference(resolution, [status(thm)], [c_3927, c_3808])).
% 7.16/2.47  tff(c_4865, plain, (![A_541, B_542, C_543, A_544]: (m1_subset_1('#skF_7'(A_541, B_542, C_543), A_544) | ~v5_relat_1(C_543, A_544) | ~r2_hidden(A_541, k10_relat_1(C_543, B_542)) | ~v1_relat_1(C_543))), inference(resolution, [status(thm)], [c_4834, c_22])).
% 7.16/2.47  tff(c_7168, plain, (![A_676, A_677, A_678]: (m1_subset_1('#skF_7'(A_676, k2_relat_1(A_677), A_677), A_678) | ~v5_relat_1(A_677, A_678) | ~r2_hidden(A_676, k1_relat_1(A_677)) | ~v1_relat_1(A_677) | ~v1_relat_1(A_677))), inference(superposition, [status(thm), theory('equality')], [c_52, c_4865])).
% 7.16/2.47  tff(c_3936, plain, (![A_458, B_459, C_460]: (r2_hidden(k4_tarski(A_458, '#skF_7'(A_458, B_459, C_460)), C_460) | ~r2_hidden(A_458, k10_relat_1(C_460, B_459)) | ~v1_relat_1(C_460))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.16/2.47  tff(c_3741, plain, (~m1_subset_1('#skF_12', '#skF_9')), inference(splitRight, [status(thm)], [c_78])).
% 7.16/2.47  tff(c_76, plain, (![E_91]: (~r2_hidden(k4_tarski('#skF_11', E_91), '#skF_10') | ~m1_subset_1(E_91, '#skF_9') | m1_subset_1('#skF_12', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_111])).
% 7.16/2.47  tff(c_3779, plain, (![E_91]: (~r2_hidden(k4_tarski('#skF_11', E_91), '#skF_10') | ~m1_subset_1(E_91, '#skF_9'))), inference(negUnitSimplification, [status(thm)], [c_3741, c_76])).
% 7.16/2.47  tff(c_3946, plain, (![B_459]: (~m1_subset_1('#skF_7'('#skF_11', B_459, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k10_relat_1('#skF_10', B_459)) | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_3936, c_3779])).
% 7.16/2.47  tff(c_3975, plain, (![B_464]: (~m1_subset_1('#skF_7'('#skF_11', B_464, '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k10_relat_1('#skF_10', B_464)))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_3946])).
% 7.16/2.47  tff(c_3979, plain, (~m1_subset_1('#skF_7'('#skF_11', k2_relat_1('#skF_10'), '#skF_10'), '#skF_9') | ~r2_hidden('#skF_11', k1_relat_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_52, c_3975])).
% 7.16/2.47  tff(c_3981, plain, (~m1_subset_1('#skF_7'('#skF_11', k2_relat_1('#skF_10'), '#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_3827, c_3979])).
% 7.16/2.47  tff(c_7171, plain, (~v5_relat_1('#skF_10', '#skF_9') | ~r2_hidden('#skF_11', k1_relat_1('#skF_10')) | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_7168, c_3981])).
% 7.16/2.47  tff(c_7191, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_3827, c_3762, c_7171])).
% 7.16/2.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.16/2.47  
% 7.16/2.47  Inference rules
% 7.16/2.47  ----------------------
% 7.16/2.47  #Ref     : 0
% 7.16/2.47  #Sup     : 1581
% 7.16/2.47  #Fact    : 0
% 7.16/2.47  #Define  : 0
% 7.16/2.47  #Split   : 4
% 7.16/2.47  #Chain   : 0
% 7.16/2.47  #Close   : 0
% 7.16/2.47  
% 7.16/2.47  Ordering : KBO
% 7.16/2.47  
% 7.16/2.47  Simplification rules
% 7.16/2.47  ----------------------
% 7.16/2.47  #Subsume      : 120
% 7.16/2.47  #Demod        : 244
% 7.16/2.47  #Tautology    : 109
% 7.16/2.47  #SimpNegUnit  : 2
% 7.16/2.47  #BackRed      : 4
% 7.16/2.47  
% 7.16/2.47  #Partial instantiations: 0
% 7.16/2.47  #Strategies tried      : 1
% 7.16/2.47  
% 7.16/2.47  Timing (in seconds)
% 7.16/2.47  ----------------------
% 7.16/2.47  Preprocessing        : 0.33
% 7.16/2.47  Parsing              : 0.17
% 7.16/2.47  CNF conversion       : 0.03
% 7.16/2.47  Main loop            : 1.37
% 7.16/2.47  Inferencing          : 0.50
% 7.16/2.47  Reduction            : 0.34
% 7.16/2.47  Demodulation         : 0.23
% 7.16/2.47  BG Simplification    : 0.07
% 7.16/2.47  Subsumption          : 0.32
% 7.16/2.47  Abstraction          : 0.09
% 7.16/2.47  MUC search           : 0.00
% 7.16/2.47  Cooper               : 0.00
% 7.16/2.47  Total                : 1.74
% 7.16/2.47  Index Insertion      : 0.00
% 7.16/2.47  Index Deletion       : 0.00
% 7.16/2.47  Index Matching       : 0.00
% 7.16/2.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
