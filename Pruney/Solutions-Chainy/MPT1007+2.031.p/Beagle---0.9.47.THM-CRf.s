%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:15 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 199 expanded)
%              Number of leaves         :   46 (  86 expanded)
%              Depth                    :   14
%              Number of atoms          :  146 ( 390 expanded)
%              Number of equality atoms :   41 ( 114 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_134,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_42,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_122,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_96,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_97,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_105,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_97])).

tff(c_30,plain,(
    ! [A_26] :
      ( k2_relat_1(A_26) != k1_xboole_0
      | k1_xboole_0 = A_26
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_114,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_105,c_30])).

tff(c_126,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_136,plain,(
    ! [C_66,A_67,B_68] :
      ( v4_relat_1(C_66,A_67)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_144,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_136])).

tff(c_158,plain,(
    ! [B_74,A_75] :
      ( k7_relat_1(B_74,A_75) = B_74
      | ~ v4_relat_1(B_74,A_75)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_161,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_144,c_158])).

tff(c_167,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_161])).

tff(c_182,plain,(
    ! [B_77,A_78] :
      ( k2_relat_1(k7_relat_1(B_77,A_78)) = k9_relat_1(B_77,A_78)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_191,plain,
    ( k9_relat_1('#skF_4',k1_tarski('#skF_2')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_182])).

tff(c_198,plain,(
    k9_relat_1('#skF_4',k1_tarski('#skF_2')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_191])).

tff(c_20,plain,(
    ! [A_17,B_19] :
      ( k9_relat_1(A_17,k1_tarski(B_19)) = k11_relat_1(A_17,B_19)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_240,plain,
    ( k11_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_20])).

tff(c_247,plain,(
    k11_relat_1('#skF_4','#skF_2') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_240])).

tff(c_24,plain,(
    ! [A_22,B_23] :
      ( r2_hidden(A_22,k1_relat_1(B_23))
      | k11_relat_1(B_23,A_22) = k1_xboole_0
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_147,plain,(
    ! [C_70,B_71,A_72] :
      ( v5_relat_1(C_70,B_71)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_72,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_155,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_147])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_320,plain,(
    ! [B_103,C_104,A_105] :
      ( r2_hidden(k1_funct_1(B_103,C_104),A_105)
      | ~ r2_hidden(C_104,k1_relat_1(B_103))
      | ~ v1_funct_1(B_103)
      | ~ v5_relat_1(B_103,A_105)
      | ~ v1_relat_1(B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_48,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_333,plain,
    ( ~ r2_hidden('#skF_2',k1_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_320,c_48])).

tff(c_342,plain,(
    ~ r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_155,c_56,c_333])).

tff(c_346,plain,
    ( k11_relat_1('#skF_4','#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_342])).

tff(c_349,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_247,c_346])).

tff(c_351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_349])).

tff(c_352,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_360,plain,(
    ! [A_5] : r1_tarski('#skF_4',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_6])).

tff(c_14,plain,(
    ! [A_12] : ~ v1_xboole_0(k1_tarski(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_361,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_50])).

tff(c_54,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_359,plain,(
    ! [A_13] : m1_subset_1('#skF_4',k1_zfmisc_1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_16])).

tff(c_353,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_367,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_353])).

tff(c_528,plain,(
    ! [A_144,B_145,C_146] :
      ( k2_relset_1(A_144,B_145,C_146) = k2_relat_1(C_146)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_532,plain,(
    ! [A_144,B_145] : k2_relset_1(A_144,B_145,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_359,c_528])).

tff(c_534,plain,(
    ! [A_144,B_145] : k2_relset_1(A_144,B_145,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_532])).

tff(c_46,plain,(
    ! [D_45,C_44,A_42,B_43] :
      ( r2_hidden(k1_funct_1(D_45,C_44),k2_relset_1(A_42,B_43,D_45))
      | k1_xboole_0 = B_43
      | ~ r2_hidden(C_44,A_42)
      | ~ m1_subset_1(D_45,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43)))
      | ~ v1_funct_2(D_45,A_42,B_43)
      | ~ v1_funct_1(D_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_622,plain,(
    ! [D_165,C_166,A_167,B_168] :
      ( r2_hidden(k1_funct_1(D_165,C_166),k2_relset_1(A_167,B_168,D_165))
      | B_168 = '#skF_4'
      | ~ r2_hidden(C_166,A_167)
      | ~ m1_subset_1(D_165,k1_zfmisc_1(k2_zfmisc_1(A_167,B_168)))
      | ~ v1_funct_2(D_165,A_167,B_168)
      | ~ v1_funct_1(D_165) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_46])).

tff(c_631,plain,(
    ! [C_166,B_145,A_144] :
      ( r2_hidden(k1_funct_1('#skF_4',C_166),'#skF_4')
      | B_145 = '#skF_4'
      | ~ r2_hidden(C_166,A_144)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_144,B_145)))
      | ~ v1_funct_2('#skF_4',A_144,B_145)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_534,c_622])).

tff(c_647,plain,(
    ! [C_172,B_173,A_174] :
      ( r2_hidden(k1_funct_1('#skF_4',C_172),'#skF_4')
      | B_173 = '#skF_4'
      | ~ r2_hidden(C_172,A_174)
      | ~ v1_funct_2('#skF_4',A_174,B_173) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_359,c_631])).

tff(c_660,plain,(
    ! [A_175,B_176] :
      ( r2_hidden(k1_funct_1('#skF_4','#skF_1'(A_175)),'#skF_4')
      | B_176 = '#skF_4'
      | ~ v1_funct_2('#skF_4',A_175,B_176)
      | v1_xboole_0(A_175) ) ),
    inference(resolution,[status(thm)],[c_4,c_647])).

tff(c_662,plain,
    ( r2_hidden(k1_funct_1('#skF_4','#skF_1'(k1_tarski('#skF_2'))),'#skF_4')
    | '#skF_3' = '#skF_4'
    | v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_54,c_660])).

tff(c_665,plain,(
    r2_hidden(k1_funct_1('#skF_4','#skF_1'(k1_tarski('#skF_2'))),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_361,c_662])).

tff(c_36,plain,(
    ! [B_32,A_31] :
      ( ~ r1_tarski(B_32,A_31)
      | ~ r2_hidden(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_672,plain,(
    ~ r1_tarski('#skF_4',k1_funct_1('#skF_4','#skF_1'(k1_tarski('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_665,c_36])).

tff(c_681,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_672])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n024.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:42:36 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.38  
% 2.79/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.38  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.79/1.38  
% 2.79/1.38  %Foreground sorts:
% 2.79/1.38  
% 2.79/1.38  
% 2.79/1.38  %Background operators:
% 2.79/1.38  
% 2.79/1.38  
% 2.79/1.38  %Foreground operators:
% 2.79/1.38  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.79/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.79/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.79/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.79/1.38  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.79/1.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.79/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.79/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.79/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.79/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.79/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.79/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.79/1.38  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.79/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.79/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.79/1.38  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.79/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.79/1.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.79/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.79/1.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.79/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.79/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.79/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.79/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.79/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.79/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.79/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.79/1.38  
% 2.79/1.40  tff(f_134, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 2.79/1.40  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.79/1.40  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.79/1.40  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.79/1.40  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.79/1.40  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.79/1.40  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 2.79/1.40  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 2.79/1.40  tff(f_91, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_funct_1)).
% 2.79/1.40  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.79/1.40  tff(f_42, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_xboole_0)).
% 2.79/1.40  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.79/1.40  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.79/1.40  tff(f_110, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.79/1.40  tff(f_122, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_funct_2)).
% 2.79/1.40  tff(f_96, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.79/1.40  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.79/1.40  tff(c_97, plain, (![C_60, A_61, B_62]: (v1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.79/1.40  tff(c_105, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_97])).
% 2.79/1.40  tff(c_30, plain, (![A_26]: (k2_relat_1(A_26)!=k1_xboole_0 | k1_xboole_0=A_26 | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.79/1.40  tff(c_114, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_105, c_30])).
% 2.79/1.40  tff(c_126, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_114])).
% 2.79/1.40  tff(c_136, plain, (![C_66, A_67, B_68]: (v4_relat_1(C_66, A_67) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.79/1.40  tff(c_144, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_52, c_136])).
% 2.79/1.40  tff(c_158, plain, (![B_74, A_75]: (k7_relat_1(B_74, A_75)=B_74 | ~v4_relat_1(B_74, A_75) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.79/1.40  tff(c_161, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_144, c_158])).
% 2.79/1.40  tff(c_167, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_105, c_161])).
% 2.79/1.40  tff(c_182, plain, (![B_77, A_78]: (k2_relat_1(k7_relat_1(B_77, A_78))=k9_relat_1(B_77, A_78) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.79/1.40  tff(c_191, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_2'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_167, c_182])).
% 2.79/1.40  tff(c_198, plain, (k9_relat_1('#skF_4', k1_tarski('#skF_2'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_191])).
% 2.79/1.40  tff(c_20, plain, (![A_17, B_19]: (k9_relat_1(A_17, k1_tarski(B_19))=k11_relat_1(A_17, B_19) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.79/1.40  tff(c_240, plain, (k11_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_198, c_20])).
% 2.79/1.40  tff(c_247, plain, (k11_relat_1('#skF_4', '#skF_2')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_240])).
% 2.79/1.40  tff(c_24, plain, (![A_22, B_23]: (r2_hidden(A_22, k1_relat_1(B_23)) | k11_relat_1(B_23, A_22)=k1_xboole_0 | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.79/1.40  tff(c_147, plain, (![C_70, B_71, A_72]: (v5_relat_1(C_70, B_71) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_72, B_71))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.79/1.40  tff(c_155, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_147])).
% 2.79/1.40  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.79/1.40  tff(c_320, plain, (![B_103, C_104, A_105]: (r2_hidden(k1_funct_1(B_103, C_104), A_105) | ~r2_hidden(C_104, k1_relat_1(B_103)) | ~v1_funct_1(B_103) | ~v5_relat_1(B_103, A_105) | ~v1_relat_1(B_103))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.79/1.40  tff(c_48, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.79/1.40  tff(c_333, plain, (~r2_hidden('#skF_2', k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_320, c_48])).
% 2.79/1.40  tff(c_342, plain, (~r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_155, c_56, c_333])).
% 2.79/1.40  tff(c_346, plain, (k11_relat_1('#skF_4', '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_342])).
% 2.79/1.40  tff(c_349, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_105, c_247, c_346])).
% 2.79/1.40  tff(c_351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126, c_349])).
% 2.79/1.40  tff(c_352, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_114])).
% 2.79/1.40  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.79/1.40  tff(c_360, plain, (![A_5]: (r1_tarski('#skF_4', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_352, c_6])).
% 2.79/1.40  tff(c_14, plain, (![A_12]: (~v1_xboole_0(k1_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.79/1.40  tff(c_50, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.79/1.40  tff(c_361, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_352, c_50])).
% 2.79/1.40  tff(c_54, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_134])).
% 2.79/1.40  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.79/1.40  tff(c_16, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.79/1.40  tff(c_359, plain, (![A_13]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_352, c_16])).
% 2.79/1.40  tff(c_353, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_114])).
% 2.79/1.40  tff(c_367, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_352, c_353])).
% 2.79/1.40  tff(c_528, plain, (![A_144, B_145, C_146]: (k2_relset_1(A_144, B_145, C_146)=k2_relat_1(C_146) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.79/1.40  tff(c_532, plain, (![A_144, B_145]: (k2_relset_1(A_144, B_145, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_359, c_528])).
% 2.79/1.40  tff(c_534, plain, (![A_144, B_145]: (k2_relset_1(A_144, B_145, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_367, c_532])).
% 2.79/1.40  tff(c_46, plain, (![D_45, C_44, A_42, B_43]: (r2_hidden(k1_funct_1(D_45, C_44), k2_relset_1(A_42, B_43, D_45)) | k1_xboole_0=B_43 | ~r2_hidden(C_44, A_42) | ~m1_subset_1(D_45, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))) | ~v1_funct_2(D_45, A_42, B_43) | ~v1_funct_1(D_45))), inference(cnfTransformation, [status(thm)], [f_122])).
% 2.79/1.40  tff(c_622, plain, (![D_165, C_166, A_167, B_168]: (r2_hidden(k1_funct_1(D_165, C_166), k2_relset_1(A_167, B_168, D_165)) | B_168='#skF_4' | ~r2_hidden(C_166, A_167) | ~m1_subset_1(D_165, k1_zfmisc_1(k2_zfmisc_1(A_167, B_168))) | ~v1_funct_2(D_165, A_167, B_168) | ~v1_funct_1(D_165))), inference(demodulation, [status(thm), theory('equality')], [c_352, c_46])).
% 2.79/1.40  tff(c_631, plain, (![C_166, B_145, A_144]: (r2_hidden(k1_funct_1('#skF_4', C_166), '#skF_4') | B_145='#skF_4' | ~r2_hidden(C_166, A_144) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))) | ~v1_funct_2('#skF_4', A_144, B_145) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_534, c_622])).
% 2.79/1.40  tff(c_647, plain, (![C_172, B_173, A_174]: (r2_hidden(k1_funct_1('#skF_4', C_172), '#skF_4') | B_173='#skF_4' | ~r2_hidden(C_172, A_174) | ~v1_funct_2('#skF_4', A_174, B_173))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_359, c_631])).
% 2.79/1.40  tff(c_660, plain, (![A_175, B_176]: (r2_hidden(k1_funct_1('#skF_4', '#skF_1'(A_175)), '#skF_4') | B_176='#skF_4' | ~v1_funct_2('#skF_4', A_175, B_176) | v1_xboole_0(A_175))), inference(resolution, [status(thm)], [c_4, c_647])).
% 2.79/1.40  tff(c_662, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_1'(k1_tarski('#skF_2'))), '#skF_4') | '#skF_3'='#skF_4' | v1_xboole_0(k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_660])).
% 2.79/1.40  tff(c_665, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_1'(k1_tarski('#skF_2'))), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_14, c_361, c_662])).
% 2.79/1.40  tff(c_36, plain, (![B_32, A_31]: (~r1_tarski(B_32, A_31) | ~r2_hidden(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.79/1.40  tff(c_672, plain, (~r1_tarski('#skF_4', k1_funct_1('#skF_4', '#skF_1'(k1_tarski('#skF_2'))))), inference(resolution, [status(thm)], [c_665, c_36])).
% 2.79/1.40  tff(c_681, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_360, c_672])).
% 2.79/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.40  
% 2.79/1.40  Inference rules
% 2.79/1.40  ----------------------
% 2.79/1.40  #Ref     : 0
% 2.79/1.40  #Sup     : 129
% 2.79/1.40  #Fact    : 0
% 2.79/1.40  #Define  : 0
% 2.79/1.40  #Split   : 3
% 2.79/1.40  #Chain   : 0
% 2.79/1.40  #Close   : 0
% 2.79/1.40  
% 2.79/1.40  Ordering : KBO
% 2.79/1.40  
% 2.79/1.40  Simplification rules
% 2.79/1.40  ----------------------
% 2.79/1.40  #Subsume      : 3
% 2.79/1.40  #Demod        : 64
% 2.79/1.40  #Tautology    : 64
% 2.79/1.40  #SimpNegUnit  : 2
% 2.79/1.40  #BackRed      : 8
% 2.79/1.40  
% 2.79/1.40  #Partial instantiations: 0
% 2.79/1.40  #Strategies tried      : 1
% 2.79/1.40  
% 2.79/1.40  Timing (in seconds)
% 2.79/1.40  ----------------------
% 2.79/1.40  Preprocessing        : 0.32
% 2.79/1.40  Parsing              : 0.18
% 2.79/1.40  CNF conversion       : 0.02
% 2.79/1.40  Main loop            : 0.31
% 2.79/1.40  Inferencing          : 0.12
% 2.79/1.40  Reduction            : 0.09
% 2.79/1.40  Demodulation         : 0.06
% 2.79/1.40  BG Simplification    : 0.02
% 2.79/1.40  Subsumption          : 0.05
% 2.79/1.40  Abstraction          : 0.01
% 2.79/1.40  MUC search           : 0.00
% 2.79/1.40  Cooper               : 0.00
% 2.79/1.40  Total                : 0.67
% 2.79/1.40  Index Insertion      : 0.00
% 2.79/1.40  Index Deletion       : 0.00
% 2.79/1.40  Index Matching       : 0.00
% 2.79/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
