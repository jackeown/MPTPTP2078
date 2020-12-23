%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:20 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 252 expanded)
%              Number of leaves         :   41 ( 108 expanded)
%              Depth                    :    9
%              Number of atoms          :  210 ( 771 expanded)
%              Number of equality atoms :   25 (  62 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_157,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
             => ( v2_funct_1(C)
                & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_98,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_49,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_96,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_76,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_137,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
           => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_60,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_76,plain,(
    ! [A_49] :
      ( v2_funct_1(A_49)
      | ~ v1_funct_1(A_49)
      | ~ v1_relat_1(A_49)
      | ~ v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_46,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_74,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_79,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_74])).

tff(c_82,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_79])).

tff(c_83,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_56,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_132,plain,(
    ! [C_61,A_62,B_63] :
      ( v1_xboole_0(C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63)))
      | ~ v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_138,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_132])).

tff(c_145,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_138])).

tff(c_58,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_54,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_52,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_38,plain,(
    ! [A_31] : k6_relat_1(A_31) = k6_partfun1(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_14,plain,(
    ! [A_7] : v2_funct_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_62,plain,(
    ! [A_7] : v2_funct_1(k6_partfun1(A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_14])).

tff(c_269,plain,(
    ! [C_92,E_95,B_94,A_91,F_93,D_90] :
      ( m1_subset_1(k1_partfun1(A_91,B_94,C_92,D_90,E_95,F_93),k1_zfmisc_1(k2_zfmisc_1(A_91,D_90)))
      | ~ m1_subset_1(F_93,k1_zfmisc_1(k2_zfmisc_1(C_92,D_90)))
      | ~ v1_funct_1(F_93)
      | ~ m1_subset_1(E_95,k1_zfmisc_1(k2_zfmisc_1(A_91,B_94)))
      | ~ v1_funct_1(E_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_28,plain,(
    ! [A_22] : m1_subset_1(k6_relat_1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_61,plain,(
    ! [A_22] : m1_subset_1(k6_partfun1(A_22),k1_zfmisc_1(k2_zfmisc_1(A_22,A_22))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_28])).

tff(c_48,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_213,plain,(
    ! [D_77,C_78,A_79,B_80] :
      ( D_77 = C_78
      | ~ r2_relset_1(A_79,B_80,C_78,D_77)
      | ~ m1_subset_1(D_77,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80)))
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_221,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_48,c_213])).

tff(c_236,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_221])).

tff(c_237,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_236])).

tff(c_277,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_269,c_237])).

tff(c_300,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_54,c_50,c_277])).

tff(c_301,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_236])).

tff(c_508,plain,(
    ! [C_154,A_150,D_152,E_153,B_151] :
      ( k1_xboole_0 = C_154
      | v2_funct_1(D_152)
      | ~ v2_funct_1(k1_partfun1(A_150,B_151,B_151,C_154,D_152,E_153))
      | ~ m1_subset_1(E_153,k1_zfmisc_1(k2_zfmisc_1(B_151,C_154)))
      | ~ v1_funct_2(E_153,B_151,C_154)
      | ~ v1_funct_1(E_153)
      | ~ m1_subset_1(D_152,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151)))
      | ~ v1_funct_2(D_152,A_150,B_151)
      | ~ v1_funct_1(D_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_510,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_301,c_508])).

tff(c_515,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_54,c_52,c_50,c_62,c_510])).

tff(c_516,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_515])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_520,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_516,c_2])).

tff(c_522,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_520])).

tff(c_523,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_6,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_525,plain,(
    ! [B_155,A_156] :
      ( v1_relat_1(B_155)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(A_156))
      | ~ v1_relat_1(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_531,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_56,c_525])).

tff(c_540,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_531])).

tff(c_542,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_523,c_540])).

tff(c_543,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_546,plain,(
    ! [B_158,A_159] :
      ( v1_relat_1(B_158)
      | ~ m1_subset_1(B_158,k1_zfmisc_1(A_159))
      | ~ v1_relat_1(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_555,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_50,c_546])).

tff(c_564,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_555])).

tff(c_580,plain,(
    ! [C_165,B_166,A_167] :
      ( v5_relat_1(C_165,B_166)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_167,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_592,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_580])).

tff(c_633,plain,(
    ! [A_178,B_179,D_180] :
      ( r2_relset_1(A_178,B_179,D_180,D_180)
      | ~ m1_subset_1(D_180,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_640,plain,(
    ! [A_22] : r2_relset_1(A_22,A_22,k6_partfun1(A_22),k6_partfun1(A_22)) ),
    inference(resolution,[status(thm)],[c_61,c_633])).

tff(c_644,plain,(
    ! [A_182,B_183,C_184] :
      ( k2_relset_1(A_182,B_183,C_184) = k2_relat_1(C_184)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_182,B_183))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_656,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_644])).

tff(c_730,plain,(
    ! [A_200,D_199,F_202,B_203,C_201,E_204] :
      ( m1_subset_1(k1_partfun1(A_200,B_203,C_201,D_199,E_204,F_202),k1_zfmisc_1(k2_zfmisc_1(A_200,D_199)))
      | ~ m1_subset_1(F_202,k1_zfmisc_1(k2_zfmisc_1(C_201,D_199)))
      | ~ v1_funct_1(F_202)
      | ~ m1_subset_1(E_204,k1_zfmisc_1(k2_zfmisc_1(A_200,B_203)))
      | ~ v1_funct_1(E_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_674,plain,(
    ! [D_186,C_187,A_188,B_189] :
      ( D_186 = C_187
      | ~ r2_relset_1(A_188,B_189,C_187,D_186)
      | ~ m1_subset_1(D_186,k1_zfmisc_1(k2_zfmisc_1(A_188,B_189)))
      | ~ m1_subset_1(C_187,k1_zfmisc_1(k2_zfmisc_1(A_188,B_189))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_682,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_48,c_674])).

tff(c_697,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_682])).

tff(c_698,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_697])).

tff(c_738,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_730,c_698])).

tff(c_761,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56,c_54,c_50,c_738])).

tff(c_762,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_697])).

tff(c_1066,plain,(
    ! [A_278,B_279,C_280,D_281] :
      ( k2_relset_1(A_278,B_279,C_280) = B_279
      | ~ r2_relset_1(B_279,B_279,k1_partfun1(B_279,A_278,A_278,B_279,D_281,C_280),k6_partfun1(B_279))
      | ~ m1_subset_1(D_281,k1_zfmisc_1(k2_zfmisc_1(B_279,A_278)))
      | ~ v1_funct_2(D_281,B_279,A_278)
      | ~ v1_funct_1(D_281)
      | ~ m1_subset_1(C_280,k1_zfmisc_1(k2_zfmisc_1(A_278,B_279)))
      | ~ v1_funct_2(C_280,A_278,B_279)
      | ~ v1_funct_1(C_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1069,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_762,c_1066])).

tff(c_1071,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_60,c_58,c_56,c_640,c_656,c_1069])).

tff(c_30,plain,(
    ! [B_24] :
      ( v2_funct_2(B_24,k2_relat_1(B_24))
      | ~ v5_relat_1(B_24,k2_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1076,plain,
    ( v2_funct_2('#skF_4',k2_relat_1('#skF_4'))
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1071,c_30])).

tff(c_1080,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_564,c_592,c_1071,c_1076])).

tff(c_1082,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_543,c_1080])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:19:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.64/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.62  
% 3.64/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.63  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.64/1.63  
% 3.64/1.63  %Foreground sorts:
% 3.64/1.63  
% 3.64/1.63  
% 3.64/1.63  %Background operators:
% 3.64/1.63  
% 3.64/1.63  
% 3.64/1.63  %Foreground operators:
% 3.64/1.63  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.64/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.64/1.63  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.64/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.64/1.63  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.64/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.64/1.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.64/1.63  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.64/1.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.64/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.64/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.64/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.64/1.63  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 3.64/1.63  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.64/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.64/1.63  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 3.64/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.64/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.64/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.64/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.64/1.63  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.64/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.64/1.63  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.64/1.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.64/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.64/1.63  
% 3.64/1.65  tff(f_157, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_funct_2)).
% 3.64/1.65  tff(f_47, axiom, (![A]: (((v1_xboole_0(A) & v1_relat_1(A)) & v1_funct_1(A)) => ((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_1)).
% 3.64/1.65  tff(f_62, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 3.64/1.65  tff(f_98, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.64/1.65  tff(f_49, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 3.64/1.65  tff(f_96, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.64/1.65  tff(f_76, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 3.64/1.65  tff(f_74, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.64/1.65  tff(f_137, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 3.64/1.65  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.64/1.65  tff(f_35, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.64/1.65  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.64/1.65  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.64/1.65  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.64/1.65  tff(f_115, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 3.64/1.65  tff(f_84, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 3.64/1.65  tff(c_60, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.64/1.65  tff(c_76, plain, (![A_49]: (v2_funct_1(A_49) | ~v1_funct_1(A_49) | ~v1_relat_1(A_49) | ~v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.64/1.65  tff(c_46, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.64/1.65  tff(c_74, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_46])).
% 3.64/1.65  tff(c_79, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_76, c_74])).
% 3.64/1.65  tff(c_82, plain, (~v1_relat_1('#skF_3') | ~v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_79])).
% 3.64/1.65  tff(c_83, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_82])).
% 3.64/1.65  tff(c_56, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.64/1.65  tff(c_132, plain, (![C_61, A_62, B_63]: (v1_xboole_0(C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))) | ~v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.64/1.65  tff(c_138, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_56, c_132])).
% 3.64/1.65  tff(c_145, plain, (~v1_xboole_0('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_83, c_138])).
% 3.64/1.65  tff(c_58, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.64/1.65  tff(c_54, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.64/1.65  tff(c_52, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.64/1.65  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.64/1.65  tff(c_38, plain, (![A_31]: (k6_relat_1(A_31)=k6_partfun1(A_31))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.64/1.65  tff(c_14, plain, (![A_7]: (v2_funct_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.64/1.65  tff(c_62, plain, (![A_7]: (v2_funct_1(k6_partfun1(A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_14])).
% 3.64/1.65  tff(c_269, plain, (![C_92, E_95, B_94, A_91, F_93, D_90]: (m1_subset_1(k1_partfun1(A_91, B_94, C_92, D_90, E_95, F_93), k1_zfmisc_1(k2_zfmisc_1(A_91, D_90))) | ~m1_subset_1(F_93, k1_zfmisc_1(k2_zfmisc_1(C_92, D_90))) | ~v1_funct_1(F_93) | ~m1_subset_1(E_95, k1_zfmisc_1(k2_zfmisc_1(A_91, B_94))) | ~v1_funct_1(E_95))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.64/1.65  tff(c_28, plain, (![A_22]: (m1_subset_1(k6_relat_1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.64/1.65  tff(c_61, plain, (![A_22]: (m1_subset_1(k6_partfun1(A_22), k1_zfmisc_1(k2_zfmisc_1(A_22, A_22))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_28])).
% 3.64/1.65  tff(c_48, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_157])).
% 3.64/1.65  tff(c_213, plain, (![D_77, C_78, A_79, B_80]: (D_77=C_78 | ~r2_relset_1(A_79, B_80, C_78, D_77) | ~m1_subset_1(D_77, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.64/1.65  tff(c_221, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_48, c_213])).
% 3.64/1.65  tff(c_236, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_221])).
% 3.64/1.65  tff(c_237, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_236])).
% 3.64/1.65  tff(c_277, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_269, c_237])).
% 3.64/1.65  tff(c_300, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_54, c_50, c_277])).
% 3.64/1.65  tff(c_301, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_236])).
% 3.64/1.65  tff(c_508, plain, (![C_154, A_150, D_152, E_153, B_151]: (k1_xboole_0=C_154 | v2_funct_1(D_152) | ~v2_funct_1(k1_partfun1(A_150, B_151, B_151, C_154, D_152, E_153)) | ~m1_subset_1(E_153, k1_zfmisc_1(k2_zfmisc_1(B_151, C_154))) | ~v1_funct_2(E_153, B_151, C_154) | ~v1_funct_1(E_153) | ~m1_subset_1(D_152, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))) | ~v1_funct_2(D_152, A_150, B_151) | ~v1_funct_1(D_152))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.64/1.65  tff(c_510, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_301, c_508])).
% 3.64/1.65  tff(c_515, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_54, c_52, c_50, c_62, c_510])).
% 3.64/1.65  tff(c_516, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_74, c_515])).
% 3.64/1.65  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.64/1.65  tff(c_520, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_516, c_2])).
% 3.64/1.65  tff(c_522, plain, $false, inference(negUnitSimplification, [status(thm)], [c_145, c_520])).
% 3.64/1.65  tff(c_523, plain, (~v1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_82])).
% 3.64/1.65  tff(c_6, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.64/1.65  tff(c_525, plain, (![B_155, A_156]: (v1_relat_1(B_155) | ~m1_subset_1(B_155, k1_zfmisc_1(A_156)) | ~v1_relat_1(A_156))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.64/1.65  tff(c_531, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_56, c_525])).
% 3.64/1.65  tff(c_540, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_531])).
% 3.64/1.65  tff(c_542, plain, $false, inference(negUnitSimplification, [status(thm)], [c_523, c_540])).
% 3.64/1.65  tff(c_543, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 3.64/1.65  tff(c_546, plain, (![B_158, A_159]: (v1_relat_1(B_158) | ~m1_subset_1(B_158, k1_zfmisc_1(A_159)) | ~v1_relat_1(A_159))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.64/1.65  tff(c_555, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_50, c_546])).
% 3.64/1.65  tff(c_564, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_555])).
% 3.64/1.65  tff(c_580, plain, (![C_165, B_166, A_167]: (v5_relat_1(C_165, B_166) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_167, B_166))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.64/1.65  tff(c_592, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_50, c_580])).
% 3.64/1.65  tff(c_633, plain, (![A_178, B_179, D_180]: (r2_relset_1(A_178, B_179, D_180, D_180) | ~m1_subset_1(D_180, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.64/1.65  tff(c_640, plain, (![A_22]: (r2_relset_1(A_22, A_22, k6_partfun1(A_22), k6_partfun1(A_22)))), inference(resolution, [status(thm)], [c_61, c_633])).
% 3.64/1.65  tff(c_644, plain, (![A_182, B_183, C_184]: (k2_relset_1(A_182, B_183, C_184)=k2_relat_1(C_184) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_182, B_183))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.64/1.65  tff(c_656, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_644])).
% 3.64/1.65  tff(c_730, plain, (![A_200, D_199, F_202, B_203, C_201, E_204]: (m1_subset_1(k1_partfun1(A_200, B_203, C_201, D_199, E_204, F_202), k1_zfmisc_1(k2_zfmisc_1(A_200, D_199))) | ~m1_subset_1(F_202, k1_zfmisc_1(k2_zfmisc_1(C_201, D_199))) | ~v1_funct_1(F_202) | ~m1_subset_1(E_204, k1_zfmisc_1(k2_zfmisc_1(A_200, B_203))) | ~v1_funct_1(E_204))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.64/1.65  tff(c_674, plain, (![D_186, C_187, A_188, B_189]: (D_186=C_187 | ~r2_relset_1(A_188, B_189, C_187, D_186) | ~m1_subset_1(D_186, k1_zfmisc_1(k2_zfmisc_1(A_188, B_189))) | ~m1_subset_1(C_187, k1_zfmisc_1(k2_zfmisc_1(A_188, B_189))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.64/1.65  tff(c_682, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_48, c_674])).
% 3.64/1.65  tff(c_697, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_61, c_682])).
% 3.64/1.65  tff(c_698, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_697])).
% 3.64/1.65  tff(c_738, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_730, c_698])).
% 3.64/1.65  tff(c_761, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_56, c_54, c_50, c_738])).
% 3.64/1.65  tff(c_762, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_697])).
% 3.64/1.65  tff(c_1066, plain, (![A_278, B_279, C_280, D_281]: (k2_relset_1(A_278, B_279, C_280)=B_279 | ~r2_relset_1(B_279, B_279, k1_partfun1(B_279, A_278, A_278, B_279, D_281, C_280), k6_partfun1(B_279)) | ~m1_subset_1(D_281, k1_zfmisc_1(k2_zfmisc_1(B_279, A_278))) | ~v1_funct_2(D_281, B_279, A_278) | ~v1_funct_1(D_281) | ~m1_subset_1(C_280, k1_zfmisc_1(k2_zfmisc_1(A_278, B_279))) | ~v1_funct_2(C_280, A_278, B_279) | ~v1_funct_1(C_280))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.64/1.65  tff(c_1069, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_762, c_1066])).
% 3.64/1.65  tff(c_1071, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_60, c_58, c_56, c_640, c_656, c_1069])).
% 3.64/1.65  tff(c_30, plain, (![B_24]: (v2_funct_2(B_24, k2_relat_1(B_24)) | ~v5_relat_1(B_24, k2_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.64/1.65  tff(c_1076, plain, (v2_funct_2('#skF_4', k2_relat_1('#skF_4')) | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1071, c_30])).
% 3.64/1.65  tff(c_1080, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_564, c_592, c_1071, c_1076])).
% 3.64/1.65  tff(c_1082, plain, $false, inference(negUnitSimplification, [status(thm)], [c_543, c_1080])).
% 3.64/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.64/1.65  
% 3.64/1.65  Inference rules
% 3.64/1.65  ----------------------
% 3.64/1.65  #Ref     : 0
% 3.64/1.65  #Sup     : 207
% 3.64/1.65  #Fact    : 0
% 3.64/1.65  #Define  : 0
% 3.64/1.65  #Split   : 11
% 3.64/1.65  #Chain   : 0
% 3.64/1.65  #Close   : 0
% 3.64/1.65  
% 3.64/1.65  Ordering : KBO
% 3.64/1.65  
% 3.64/1.65  Simplification rules
% 3.64/1.65  ----------------------
% 3.64/1.65  #Subsume      : 1
% 3.64/1.65  #Demod        : 145
% 3.64/1.65  #Tautology    : 37
% 3.64/1.65  #SimpNegUnit  : 5
% 3.64/1.65  #BackRed      : 6
% 3.64/1.65  
% 3.64/1.65  #Partial instantiations: 0
% 3.64/1.65  #Strategies tried      : 1
% 3.64/1.65  
% 3.64/1.65  Timing (in seconds)
% 3.64/1.65  ----------------------
% 3.64/1.65  Preprocessing        : 0.34
% 3.64/1.65  Parsing              : 0.18
% 3.64/1.65  CNF conversion       : 0.02
% 3.64/1.65  Main loop            : 0.53
% 3.64/1.65  Inferencing          : 0.21
% 3.64/1.65  Reduction            : 0.16
% 3.64/1.65  Demodulation         : 0.12
% 3.64/1.65  BG Simplification    : 0.02
% 3.64/1.65  Subsumption          : 0.08
% 3.64/1.65  Abstraction          : 0.02
% 3.64/1.65  MUC search           : 0.00
% 3.64/1.65  Cooper               : 0.00
% 3.64/1.65  Total                : 0.90
% 3.64/1.65  Index Insertion      : 0.00
% 3.64/1.65  Index Deletion       : 0.00
% 3.64/1.65  Index Matching       : 0.00
% 3.64/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
