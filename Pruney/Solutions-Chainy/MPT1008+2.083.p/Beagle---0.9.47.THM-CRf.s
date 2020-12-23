%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:37 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 393 expanded)
%              Number of leaves         :   40 ( 146 expanded)
%              Depth                    :   16
%              Number of atoms          :  188 ( 841 expanded)
%              Number of equality atoms :   90 ( 373 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_124,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_63,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_112,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_84,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_129,plain,(
    ! [C_57,A_58,B_59] :
      ( v1_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_138,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_129])).

tff(c_32,plain,(
    ! [A_15] :
      ( k1_relat_1(A_15) != k1_xboole_0
      | k1_xboole_0 = A_15
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_146,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_138,c_32])).

tff(c_157,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_315,plain,(
    ! [B_88,A_89] :
      ( k1_tarski(k1_funct_1(B_88,A_89)) = k2_relat_1(B_88)
      | k1_tarski(A_89) != k1_relat_1(B_88)
      | ~ v1_funct_1(B_88)
      | ~ v1_relat_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_158,plain,(
    ! [A_63,B_64,C_65] :
      ( k2_relset_1(A_63,B_64,C_65) = k2_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_167,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_158])).

tff(c_48,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') != k1_tarski(k1_funct_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_193,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_48])).

tff(c_321,plain,
    ( k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_193])).

tff(c_340,plain,(
    k1_tarski('#skF_2') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_56,c_321])).

tff(c_210,plain,(
    ! [A_72,B_73,C_74] :
      ( k1_relset_1(A_72,B_73,C_74) = k1_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_219,plain,(
    k1_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_210])).

tff(c_243,plain,(
    ! [A_80,B_81,C_82] :
      ( m1_subset_1(k1_relset_1(A_80,B_81,C_82),k1_zfmisc_1(A_80))
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_261,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(k1_tarski('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_243])).

tff(c_267,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(k1_tarski('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_261])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_281,plain,(
    r1_tarski(k1_relat_1('#skF_4'),k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_267,c_22])).

tff(c_6,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_386,plain,(
    ! [B_96,C_97,A_98] :
      ( k2_tarski(B_96,C_97) = A_98
      | k1_tarski(C_97) = A_98
      | k1_tarski(B_96) = A_98
      | k1_xboole_0 = A_98
      | ~ r1_tarski(A_98,k2_tarski(B_96,C_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_402,plain,(
    ! [A_4,A_98] :
      ( k2_tarski(A_4,A_4) = A_98
      | k1_tarski(A_4) = A_98
      | k1_tarski(A_4) = A_98
      | k1_xboole_0 = A_98
      | ~ r1_tarski(A_98,k1_tarski(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_386])).

tff(c_446,plain,(
    ! [A_107,A_108] :
      ( k1_tarski(A_107) = A_108
      | k1_tarski(A_107) = A_108
      | k1_tarski(A_107) = A_108
      | k1_xboole_0 = A_108
      | ~ r1_tarski(A_108,k1_tarski(A_107)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_402])).

tff(c_456,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_281,c_446])).

tff(c_468,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_157,c_340,c_340,c_340,c_456])).

tff(c_469,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_478,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_469,c_26])).

tff(c_30,plain,(
    ! [A_15] :
      ( k2_relat_1(A_15) != k1_xboole_0
      | k1_xboole_0 = A_15
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_145,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_138,c_30])).

tff(c_147,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_471,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_469,c_147])).

tff(c_512,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_471])).

tff(c_513,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_4,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_519,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_4])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_520,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_513,c_28])).

tff(c_514,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_527,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_514])).

tff(c_708,plain,(
    ! [B_146,A_147] :
      ( k1_tarski(k1_funct_1(B_146,A_147)) = k2_relat_1(B_146)
      | k1_tarski(A_147) != k1_relat_1(B_146)
      | ~ v1_funct_1(B_146)
      | ~ v1_relat_1(B_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_577,plain,(
    ! [A_123,B_124,C_125] :
      ( k2_relset_1(A_123,B_124,C_125) = k2_relat_1(C_125)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_584,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_577])).

tff(c_587,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_527,c_584])).

tff(c_588,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_587,c_48])).

tff(c_714,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_708,c_588])).

tff(c_732,plain,(
    k1_tarski('#skF_2') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_56,c_520,c_527,c_714])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_522,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_50])).

tff(c_54,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_518,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | A_1 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_2])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_601,plain,(
    ! [A_127,B_128,C_129] :
      ( k1_relset_1(A_127,B_128,C_129) = k1_relat_1(C_129)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_616,plain,(
    ! [A_130,B_131,A_132] :
      ( k1_relset_1(A_130,B_131,A_132) = k1_relat_1(A_132)
      | ~ r1_tarski(A_132,k2_zfmisc_1(A_130,B_131)) ) ),
    inference(resolution,[status(thm)],[c_24,c_601])).

tff(c_620,plain,(
    ! [A_130,B_131] : k1_relset_1(A_130,B_131,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_519,c_616])).

tff(c_622,plain,(
    ! [A_130,B_131] : k1_relset_1(A_130,B_131,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_520,c_620])).

tff(c_646,plain,(
    ! [A_140,B_141,C_142] :
      ( m1_subset_1(k1_relset_1(A_140,B_141,C_142),k1_zfmisc_1(A_140))
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_669,plain,(
    ! [A_143,B_144] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(A_143))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_143,B_144))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_622,c_646])).

tff(c_672,plain,(
    ! [A_143,B_144] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(A_143))
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(A_143,B_144)) ) ),
    inference(resolution,[status(thm)],[c_24,c_669])).

tff(c_678,plain,(
    ! [A_143] : m1_subset_1('#skF_4',k1_zfmisc_1(A_143)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_672])).

tff(c_631,plain,(
    ! [A_135,B_136,A_137] :
      ( k2_relset_1(A_135,B_136,A_137) = k2_relat_1(A_137)
      | ~ r1_tarski(A_137,k2_zfmisc_1(A_135,B_136)) ) ),
    inference(resolution,[status(thm)],[c_24,c_577])).

tff(c_635,plain,(
    ! [A_135,B_136] : k2_relset_1(A_135,B_136,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_519,c_631])).

tff(c_637,plain,(
    ! [A_135,B_136] : k2_relset_1(A_135,B_136,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_527,c_635])).

tff(c_46,plain,(
    ! [D_35,C_34,A_32,B_33] :
      ( r2_hidden(k1_funct_1(D_35,C_34),k2_relset_1(A_32,B_33,D_35))
      | k1_xboole_0 = B_33
      | ~ r2_hidden(C_34,A_32)
      | ~ m1_subset_1(D_35,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | ~ v1_funct_2(D_35,A_32,B_33)
      | ~ v1_funct_1(D_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_856,plain,(
    ! [D_170,C_171,A_172,B_173] :
      ( r2_hidden(k1_funct_1(D_170,C_171),k2_relset_1(A_172,B_173,D_170))
      | B_173 = '#skF_4'
      | ~ r2_hidden(C_171,A_172)
      | ~ m1_subset_1(D_170,k1_zfmisc_1(k2_zfmisc_1(A_172,B_173)))
      | ~ v1_funct_2(D_170,A_172,B_173)
      | ~ v1_funct_1(D_170) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_513,c_46])).

tff(c_862,plain,(
    ! [C_171,B_136,A_135] :
      ( r2_hidden(k1_funct_1('#skF_4',C_171),'#skF_4')
      | B_136 = '#skF_4'
      | ~ r2_hidden(C_171,A_135)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_135,B_136)))
      | ~ v1_funct_2('#skF_4',A_135,B_136)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_637,c_856])).

tff(c_866,plain,(
    ! [C_174,B_175,A_176] :
      ( r2_hidden(k1_funct_1('#skF_4',C_174),'#skF_4')
      | B_175 = '#skF_4'
      | ~ r2_hidden(C_174,A_176)
      | ~ v1_funct_2('#skF_4',A_176,B_175) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_678,c_862])).

tff(c_873,plain,(
    ! [A_177,B_178] :
      ( r2_hidden(k1_funct_1('#skF_4','#skF_1'(A_177)),'#skF_4')
      | B_178 = '#skF_4'
      | ~ v1_funct_2('#skF_4',A_177,B_178)
      | A_177 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_518,c_866])).

tff(c_875,plain,
    ( r2_hidden(k1_funct_1('#skF_4','#skF_1'(k1_tarski('#skF_2'))),'#skF_4')
    | '#skF_3' = '#skF_4'
    | k1_tarski('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_54,c_873])).

tff(c_878,plain,(
    r2_hidden(k1_funct_1('#skF_4','#skF_1'(k1_tarski('#skF_2'))),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_732,c_522,c_875])).

tff(c_36,plain,(
    ! [B_19,A_18] :
      ( ~ r1_tarski(B_19,A_18)
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_883,plain,(
    ~ r1_tarski('#skF_4',k1_funct_1('#skF_4','#skF_1'(k1_tarski('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_878,c_36])).

tff(c_888,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_519,c_883])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:12:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.55  
% 3.16/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.55  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.16/1.55  
% 3.16/1.55  %Foreground sorts:
% 3.16/1.55  
% 3.16/1.55  
% 3.16/1.55  %Background operators:
% 3.16/1.55  
% 3.16/1.55  
% 3.16/1.55  %Foreground operators:
% 3.16/1.55  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.16/1.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.16/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.16/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.16/1.55  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.16/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.16/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.16/1.55  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.16/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.16/1.55  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.16/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.16/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.16/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.16/1.55  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.16/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.16/1.55  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.16/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.16/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.16/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.16/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.16/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.16/1.55  
% 3.16/1.58  tff(f_124, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t62_funct_2)).
% 3.16/1.58  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.16/1.58  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.16/1.58  tff(f_79, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.16/1.58  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.16/1.58  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.16/1.58  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.16/1.58  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.16/1.58  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.16/1.58  tff(f_56, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.16/1.58  tff(f_63, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.16/1.58  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.16/1.58  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.16/1.58  tff(f_112, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 3.16/1.58  tff(f_84, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.16/1.58  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.16/1.58  tff(c_129, plain, (![C_57, A_58, B_59]: (v1_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.16/1.58  tff(c_138, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_129])).
% 3.16/1.58  tff(c_32, plain, (![A_15]: (k1_relat_1(A_15)!=k1_xboole_0 | k1_xboole_0=A_15 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.16/1.58  tff(c_146, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_138, c_32])).
% 3.16/1.58  tff(c_157, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_146])).
% 3.16/1.58  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.16/1.58  tff(c_315, plain, (![B_88, A_89]: (k1_tarski(k1_funct_1(B_88, A_89))=k2_relat_1(B_88) | k1_tarski(A_89)!=k1_relat_1(B_88) | ~v1_funct_1(B_88) | ~v1_relat_1(B_88))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.16/1.58  tff(c_158, plain, (![A_63, B_64, C_65]: (k2_relset_1(A_63, B_64, C_65)=k2_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.16/1.58  tff(c_167, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_158])).
% 3.16/1.58  tff(c_48, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')!=k1_tarski(k1_funct_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.16/1.58  tff(c_193, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_167, c_48])).
% 3.16/1.58  tff(c_321, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_315, c_193])).
% 3.16/1.58  tff(c_340, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_56, c_321])).
% 3.16/1.58  tff(c_210, plain, (![A_72, B_73, C_74]: (k1_relset_1(A_72, B_73, C_74)=k1_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.16/1.58  tff(c_219, plain, (k1_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_210])).
% 3.16/1.58  tff(c_243, plain, (![A_80, B_81, C_82]: (m1_subset_1(k1_relset_1(A_80, B_81, C_82), k1_zfmisc_1(A_80)) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.16/1.58  tff(c_261, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(k1_tarski('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_219, c_243])).
% 3.16/1.58  tff(c_267, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_261])).
% 3.16/1.58  tff(c_22, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.16/1.58  tff(c_281, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_267, c_22])).
% 3.16/1.58  tff(c_6, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.16/1.58  tff(c_386, plain, (![B_96, C_97, A_98]: (k2_tarski(B_96, C_97)=A_98 | k1_tarski(C_97)=A_98 | k1_tarski(B_96)=A_98 | k1_xboole_0=A_98 | ~r1_tarski(A_98, k2_tarski(B_96, C_97)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.16/1.58  tff(c_402, plain, (![A_4, A_98]: (k2_tarski(A_4, A_4)=A_98 | k1_tarski(A_4)=A_98 | k1_tarski(A_4)=A_98 | k1_xboole_0=A_98 | ~r1_tarski(A_98, k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_386])).
% 3.16/1.58  tff(c_446, plain, (![A_107, A_108]: (k1_tarski(A_107)=A_108 | k1_tarski(A_107)=A_108 | k1_tarski(A_107)=A_108 | k1_xboole_0=A_108 | ~r1_tarski(A_108, k1_tarski(A_107)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_402])).
% 3.16/1.58  tff(c_456, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_281, c_446])).
% 3.16/1.58  tff(c_468, plain, $false, inference(negUnitSimplification, [status(thm)], [c_157, c_340, c_340, c_340, c_456])).
% 3.16/1.58  tff(c_469, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_146])).
% 3.16/1.58  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.16/1.58  tff(c_478, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_469, c_469, c_26])).
% 3.16/1.58  tff(c_30, plain, (![A_15]: (k2_relat_1(A_15)!=k1_xboole_0 | k1_xboole_0=A_15 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.16/1.58  tff(c_145, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_138, c_30])).
% 3.16/1.58  tff(c_147, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_145])).
% 3.16/1.58  tff(c_471, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_469, c_147])).
% 3.16/1.58  tff(c_512, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_478, c_471])).
% 3.16/1.58  tff(c_513, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_145])).
% 3.16/1.58  tff(c_4, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.16/1.58  tff(c_519, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_513, c_4])).
% 3.16/1.58  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.16/1.58  tff(c_520, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_513, c_513, c_28])).
% 3.16/1.58  tff(c_514, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_145])).
% 3.16/1.58  tff(c_527, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_513, c_514])).
% 3.16/1.58  tff(c_708, plain, (![B_146, A_147]: (k1_tarski(k1_funct_1(B_146, A_147))=k2_relat_1(B_146) | k1_tarski(A_147)!=k1_relat_1(B_146) | ~v1_funct_1(B_146) | ~v1_relat_1(B_146))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.16/1.58  tff(c_577, plain, (![A_123, B_124, C_125]: (k2_relset_1(A_123, B_124, C_125)=k2_relat_1(C_125) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.16/1.58  tff(c_584, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_577])).
% 3.16/1.58  tff(c_587, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_527, c_584])).
% 3.16/1.58  tff(c_588, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_587, c_48])).
% 3.16/1.58  tff(c_714, plain, (k2_relat_1('#skF_4')!='#skF_4' | k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_708, c_588])).
% 3.16/1.58  tff(c_732, plain, (k1_tarski('#skF_2')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_138, c_56, c_520, c_527, c_714])).
% 3.16/1.58  tff(c_50, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.16/1.58  tff(c_522, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_513, c_50])).
% 3.16/1.58  tff(c_54, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.16/1.58  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.16/1.58  tff(c_518, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | A_1='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_513, c_2])).
% 3.16/1.58  tff(c_24, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.16/1.58  tff(c_601, plain, (![A_127, B_128, C_129]: (k1_relset_1(A_127, B_128, C_129)=k1_relat_1(C_129) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.16/1.58  tff(c_616, plain, (![A_130, B_131, A_132]: (k1_relset_1(A_130, B_131, A_132)=k1_relat_1(A_132) | ~r1_tarski(A_132, k2_zfmisc_1(A_130, B_131)))), inference(resolution, [status(thm)], [c_24, c_601])).
% 3.16/1.58  tff(c_620, plain, (![A_130, B_131]: (k1_relset_1(A_130, B_131, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_519, c_616])).
% 3.16/1.58  tff(c_622, plain, (![A_130, B_131]: (k1_relset_1(A_130, B_131, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_520, c_620])).
% 3.16/1.58  tff(c_646, plain, (![A_140, B_141, C_142]: (m1_subset_1(k1_relset_1(A_140, B_141, C_142), k1_zfmisc_1(A_140)) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.16/1.58  tff(c_669, plain, (![A_143, B_144]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_143)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))))), inference(superposition, [status(thm), theory('equality')], [c_622, c_646])).
% 3.16/1.58  tff(c_672, plain, (![A_143, B_144]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_143)) | ~r1_tarski('#skF_4', k2_zfmisc_1(A_143, B_144)))), inference(resolution, [status(thm)], [c_24, c_669])).
% 3.16/1.58  tff(c_678, plain, (![A_143]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_143)))), inference(demodulation, [status(thm), theory('equality')], [c_519, c_672])).
% 3.16/1.58  tff(c_631, plain, (![A_135, B_136, A_137]: (k2_relset_1(A_135, B_136, A_137)=k2_relat_1(A_137) | ~r1_tarski(A_137, k2_zfmisc_1(A_135, B_136)))), inference(resolution, [status(thm)], [c_24, c_577])).
% 3.16/1.58  tff(c_635, plain, (![A_135, B_136]: (k2_relset_1(A_135, B_136, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_519, c_631])).
% 3.16/1.58  tff(c_637, plain, (![A_135, B_136]: (k2_relset_1(A_135, B_136, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_527, c_635])).
% 3.16/1.58  tff(c_46, plain, (![D_35, C_34, A_32, B_33]: (r2_hidden(k1_funct_1(D_35, C_34), k2_relset_1(A_32, B_33, D_35)) | k1_xboole_0=B_33 | ~r2_hidden(C_34, A_32) | ~m1_subset_1(D_35, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | ~v1_funct_2(D_35, A_32, B_33) | ~v1_funct_1(D_35))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.16/1.58  tff(c_856, plain, (![D_170, C_171, A_172, B_173]: (r2_hidden(k1_funct_1(D_170, C_171), k2_relset_1(A_172, B_173, D_170)) | B_173='#skF_4' | ~r2_hidden(C_171, A_172) | ~m1_subset_1(D_170, k1_zfmisc_1(k2_zfmisc_1(A_172, B_173))) | ~v1_funct_2(D_170, A_172, B_173) | ~v1_funct_1(D_170))), inference(demodulation, [status(thm), theory('equality')], [c_513, c_46])).
% 3.16/1.58  tff(c_862, plain, (![C_171, B_136, A_135]: (r2_hidden(k1_funct_1('#skF_4', C_171), '#skF_4') | B_136='#skF_4' | ~r2_hidden(C_171, A_135) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_135, B_136))) | ~v1_funct_2('#skF_4', A_135, B_136) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_637, c_856])).
% 3.16/1.58  tff(c_866, plain, (![C_174, B_175, A_176]: (r2_hidden(k1_funct_1('#skF_4', C_174), '#skF_4') | B_175='#skF_4' | ~r2_hidden(C_174, A_176) | ~v1_funct_2('#skF_4', A_176, B_175))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_678, c_862])).
% 3.16/1.58  tff(c_873, plain, (![A_177, B_178]: (r2_hidden(k1_funct_1('#skF_4', '#skF_1'(A_177)), '#skF_4') | B_178='#skF_4' | ~v1_funct_2('#skF_4', A_177, B_178) | A_177='#skF_4')), inference(resolution, [status(thm)], [c_518, c_866])).
% 3.16/1.58  tff(c_875, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_1'(k1_tarski('#skF_2'))), '#skF_4') | '#skF_3'='#skF_4' | k1_tarski('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_54, c_873])).
% 3.16/1.58  tff(c_878, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_1'(k1_tarski('#skF_2'))), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_732, c_522, c_875])).
% 3.16/1.58  tff(c_36, plain, (![B_19, A_18]: (~r1_tarski(B_19, A_18) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.16/1.58  tff(c_883, plain, (~r1_tarski('#skF_4', k1_funct_1('#skF_4', '#skF_1'(k1_tarski('#skF_2'))))), inference(resolution, [status(thm)], [c_878, c_36])).
% 3.16/1.58  tff(c_888, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_519, c_883])).
% 3.16/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.58  
% 3.16/1.58  Inference rules
% 3.16/1.58  ----------------------
% 3.16/1.58  #Ref     : 0
% 3.16/1.58  #Sup     : 171
% 3.16/1.58  #Fact    : 0
% 3.16/1.58  #Define  : 0
% 3.16/1.58  #Split   : 2
% 3.16/1.58  #Chain   : 0
% 3.16/1.58  #Close   : 0
% 3.16/1.58  
% 3.16/1.58  Ordering : KBO
% 3.16/1.58  
% 3.16/1.58  Simplification rules
% 3.16/1.58  ----------------------
% 3.16/1.58  #Subsume      : 3
% 3.16/1.58  #Demod        : 126
% 3.16/1.58  #Tautology    : 100
% 3.16/1.58  #SimpNegUnit  : 2
% 3.16/1.58  #BackRed      : 19
% 3.16/1.58  
% 3.16/1.58  #Partial instantiations: 0
% 3.16/1.58  #Strategies tried      : 1
% 3.16/1.58  
% 3.16/1.58  Timing (in seconds)
% 3.16/1.58  ----------------------
% 3.16/1.58  Preprocessing        : 0.33
% 3.16/1.58  Parsing              : 0.17
% 3.16/1.58  CNF conversion       : 0.02
% 3.16/1.58  Main loop            : 0.45
% 3.16/1.58  Inferencing          : 0.18
% 3.16/1.58  Reduction            : 0.14
% 3.16/1.58  Demodulation         : 0.10
% 3.16/1.58  BG Simplification    : 0.02
% 3.16/1.58  Subsumption          : 0.07
% 3.16/1.58  Abstraction          : 0.02
% 3.16/1.58  MUC search           : 0.00
% 3.16/1.58  Cooper               : 0.00
% 3.16/1.58  Total                : 0.83
% 3.16/1.58  Index Insertion      : 0.00
% 3.16/1.58  Index Deletion       : 0.00
% 3.16/1.58  Index Matching       : 0.00
% 3.16/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
