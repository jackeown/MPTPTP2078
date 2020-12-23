%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:58 EST 2020

% Result     : Theorem 4.19s
% Output     : CNFRefutation 4.63s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 622 expanded)
%              Number of leaves         :   38 ( 217 expanded)
%              Depth                    :   14
%              Number of atoms          :  201 (1558 expanded)
%              Number of equality atoms :   91 ( 791 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_142,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => k8_relset_1(A,B,C,k7_relset_1(A,B,C,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_2)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_129,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_43,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_132,plain,(
    ! [C_54,A_55,B_56] :
      ( v1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_149,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_132])).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_64,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_79,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_68,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_242,plain,(
    ! [A_77,B_78,C_79] :
      ( k1_relset_1(A_77,B_78,C_79) = k1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_261,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_242])).

tff(c_896,plain,(
    ! [B_167,A_168,C_169] :
      ( k1_xboole_0 = B_167
      | k1_relset_1(A_168,B_167,C_169) = A_168
      | ~ v1_funct_2(C_169,A_168,B_167)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_168,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_910,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_896])).

tff(c_926,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_261,c_910])).

tff(c_927,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_926])).

tff(c_56,plain,(
    ! [B_42,A_41] :
      ( m1_subset_1(B_42,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_42),A_41)))
      | ~ r1_tarski(k2_relat_1(B_42),A_41)
      | ~ v1_funct_1(B_42)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_936,plain,(
    ! [A_41] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_41)))
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_41)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_927,c_56])).

tff(c_999,plain,(
    ! [A_175] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_175)))
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_175) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_70,c_936])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1048,plain,(
    ! [A_177] :
      ( r1_tarski('#skF_3',k2_zfmisc_1('#skF_1',A_177))
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_177) ) ),
    inference(resolution,[status(thm)],[c_999,c_18])).

tff(c_1053,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1',k2_relat_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_6,c_1048])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_440,plain,(
    ! [A_110,B_111,C_112,D_113] :
      ( k8_relset_1(A_110,B_111,C_112,D_113) = k10_relat_1(C_112,D_113)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1352,plain,(
    ! [A_213,B_214,A_215,D_216] :
      ( k8_relset_1(A_213,B_214,A_215,D_216) = k10_relat_1(A_215,D_216)
      | ~ r1_tarski(A_215,k2_zfmisc_1(A_213,B_214)) ) ),
    inference(resolution,[status(thm)],[c_20,c_440])).

tff(c_1367,plain,(
    ! [D_216] : k8_relset_1('#skF_1',k2_relat_1('#skF_3'),'#skF_3',D_216) = k10_relat_1('#skF_3',D_216) ),
    inference(resolution,[status(thm)],[c_1053,c_1352])).

tff(c_30,plain,(
    ! [A_21,B_22,C_23] :
      ( k1_relset_1(A_21,B_22,C_23) = k1_relat_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1013,plain,(
    ! [A_175] :
      ( k1_relset_1('#skF_1',A_175,'#skF_3') = k1_relat_1('#skF_3')
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_175) ) ),
    inference(resolution,[status(thm)],[c_999,c_30])).

tff(c_1038,plain,(
    ! [A_176] :
      ( k1_relset_1('#skF_1',A_176,'#skF_3') = '#skF_1'
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_927,c_1013])).

tff(c_1043,plain,(
    k1_relset_1('#skF_1',k2_relat_1('#skF_3'),'#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_1038])).

tff(c_36,plain,(
    ! [A_32,B_33,C_34] :
      ( k8_relset_1(A_32,B_33,C_34,B_33) = k1_relset_1(A_32,B_33,C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2128,plain,(
    ! [A_280] :
      ( k8_relset_1('#skF_1',A_280,'#skF_3',A_280) = k1_relset_1('#skF_1',A_280,'#skF_3')
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_280) ) ),
    inference(resolution,[status(thm)],[c_999,c_36])).

tff(c_2133,plain,(
    k8_relset_1('#skF_1',k2_relat_1('#skF_3'),'#skF_3',k2_relat_1('#skF_3')) = k1_relset_1('#skF_1',k2_relat_1('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_2128])).

tff(c_2137,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1367,c_1043,c_2133])).

tff(c_481,plain,(
    ! [B_123,A_124] :
      ( k9_relat_1(B_123,k10_relat_1(B_123,A_124)) = A_124
      | ~ r1_tarski(A_124,k2_relat_1(B_123))
      | ~ v1_funct_1(B_123)
      | ~ v1_relat_1(B_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_489,plain,(
    ! [B_123] :
      ( k9_relat_1(B_123,k10_relat_1(B_123,k2_relat_1(B_123))) = k2_relat_1(B_123)
      | ~ v1_funct_1(B_123)
      | ~ v1_relat_1(B_123) ) ),
    inference(resolution,[status(thm)],[c_6,c_481])).

tff(c_2142,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2137,c_489])).

tff(c_2146,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_70,c_2142])).

tff(c_522,plain,(
    ! [A_131,B_132,C_133,D_134] :
      ( k7_relset_1(A_131,B_132,C_133,D_134) = k9_relat_1(C_133,D_134)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_540,plain,(
    ! [D_134] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_134) = k9_relat_1('#skF_3',D_134) ),
    inference(resolution,[status(thm)],[c_66,c_522])).

tff(c_458,plain,(
    ! [D_113] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_113) = k10_relat_1('#skF_3',D_113) ),
    inference(resolution,[status(thm)],[c_66,c_440])).

tff(c_62,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3',k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_461,plain,(
    k10_relat_1('#skF_3',k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_62])).

tff(c_542,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_461])).

tff(c_2150,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2146,c_542])).

tff(c_2153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2137,c_2150])).

tff(c_2154,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_16,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2174,plain,(
    ! [A_6] : m1_subset_1('#skF_1',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2154,c_16])).

tff(c_2618,plain,(
    ! [A_364,B_365,C_366,D_367] :
      ( k8_relset_1(A_364,B_365,C_366,D_367) = k10_relat_1(C_366,D_367)
      | ~ m1_subset_1(C_366,k1_zfmisc_1(k2_zfmisc_1(A_364,B_365))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2634,plain,(
    ! [A_364,B_365,D_367] : k8_relset_1(A_364,B_365,'#skF_1',D_367) = k10_relat_1('#skF_1',D_367) ),
    inference(resolution,[status(thm)],[c_2174,c_2618])).

tff(c_2325,plain,(
    ! [A_308,B_309,C_310] :
      ( k1_relset_1(A_308,B_309,C_310) = k1_relat_1(C_310)
      | ~ m1_subset_1(C_310,k1_zfmisc_1(k2_zfmisc_1(A_308,B_309))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2341,plain,(
    ! [A_308,B_309] : k1_relset_1(A_308,B_309,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2174,c_2325])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_44,plain,(
    ! [C_37,B_36] :
      ( v1_funct_2(C_37,k1_xboole_0,B_36)
      | k1_relset_1(k1_xboole_0,B_36,C_37) != k1_xboole_0
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_75,plain,(
    ! [C_37,B_36] :
      ( v1_funct_2(C_37,k1_xboole_0,B_36)
      | k1_relset_1(k1_xboole_0,B_36,C_37) != k1_xboole_0
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_44])).

tff(c_2454,plain,(
    ! [C_335,B_336] :
      ( v1_funct_2(C_335,'#skF_1',B_336)
      | k1_relset_1('#skF_1',B_336,C_335) != '#skF_1'
      | ~ m1_subset_1(C_335,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2154,c_2154,c_2154,c_2154,c_75])).

tff(c_2460,plain,(
    ! [B_336] :
      ( v1_funct_2('#skF_1','#skF_1',B_336)
      | k1_relset_1('#skF_1',B_336,'#skF_1') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_2174,c_2454])).

tff(c_2463,plain,(
    ! [B_336] :
      ( v1_funct_2('#skF_1','#skF_1',B_336)
      | k1_relat_1('#skF_1') != '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2341,c_2460])).

tff(c_2464,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2463])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2166,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2154,c_2154,c_12])).

tff(c_2155,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_2160,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2154,c_2155])).

tff(c_2200,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2166,c_2160,c_66])).

tff(c_2204,plain,(
    ! [A_288,B_289] :
      ( r1_tarski(A_288,B_289)
      | ~ m1_subset_1(A_288,k1_zfmisc_1(B_289)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2215,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_2200,c_2204])).

tff(c_8,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2192,plain,(
    ! [A_3] :
      ( A_3 = '#skF_1'
      | ~ r1_tarski(A_3,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2154,c_2154,c_8])).

tff(c_2220,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2215,c_2192])).

tff(c_2161,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2160,c_68])).

tff(c_2223,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2220,c_2161])).

tff(c_48,plain,(
    ! [B_36,C_37] :
      ( k1_relset_1(k1_xboole_0,B_36,C_37) = k1_xboole_0
      | ~ v1_funct_2(C_37,k1_xboole_0,B_36)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_74,plain,(
    ! [B_36,C_37] :
      ( k1_relset_1(k1_xboole_0,B_36,C_37) = k1_xboole_0
      | ~ v1_funct_2(C_37,k1_xboole_0,B_36)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_48])).

tff(c_2471,plain,(
    ! [B_339,C_340] :
      ( k1_relset_1('#skF_1',B_339,C_340) = '#skF_1'
      | ~ v1_funct_2(C_340,'#skF_1',B_339)
      | ~ m1_subset_1(C_340,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2154,c_2154,c_2154,c_2154,c_74])).

tff(c_2475,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_1') = '#skF_1'
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_2223,c_2471])).

tff(c_2482,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2174,c_2341,c_2475])).

tff(c_2484,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2464,c_2482])).

tff(c_2486,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2463])).

tff(c_2487,plain,(
    ! [A_308,B_309] : k1_relset_1(A_308,B_309,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2486,c_2341])).

tff(c_2918,plain,(
    ! [A_393,B_394,C_395] :
      ( k8_relset_1(A_393,B_394,C_395,B_394) = k1_relset_1(A_393,B_394,C_395)
      | ~ m1_subset_1(C_395,k1_zfmisc_1(k2_zfmisc_1(A_393,B_394))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2929,plain,(
    ! [A_393,B_394] : k8_relset_1(A_393,B_394,'#skF_1',B_394) = k1_relset_1(A_393,B_394,'#skF_1') ),
    inference(resolution,[status(thm)],[c_2174,c_2918])).

tff(c_2935,plain,(
    ! [B_394] : k10_relat_1('#skF_1',B_394) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2634,c_2487,c_2929])).

tff(c_2686,plain,(
    ! [A_380,B_381,C_382,D_383] :
      ( k7_relset_1(A_380,B_381,C_382,D_383) = k9_relat_1(C_382,D_383)
      | ~ m1_subset_1(C_382,k1_zfmisc_1(k2_zfmisc_1(A_380,B_381))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2705,plain,(
    ! [A_384,B_385,D_386] : k7_relset_1(A_384,B_385,'#skF_1',D_386) = k9_relat_1('#skF_1',D_386) ),
    inference(resolution,[status(thm)],[c_2174,c_2686])).

tff(c_28,plain,(
    ! [A_17,B_18,C_19,D_20] :
      ( m1_subset_1(k7_relset_1(A_17,B_18,C_19,D_20),k1_zfmisc_1(B_18))
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2715,plain,(
    ! [D_386,B_385,A_384] :
      ( m1_subset_1(k9_relat_1('#skF_1',D_386),k1_zfmisc_1(B_385))
      | ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(A_384,B_385))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2705,c_28])).

tff(c_2739,plain,(
    ! [D_388,B_389] : m1_subset_1(k9_relat_1('#skF_1',D_388),k1_zfmisc_1(B_389)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2174,c_2715])).

tff(c_2808,plain,(
    ! [D_390,B_391] : r1_tarski(k9_relat_1('#skF_1',D_390),B_391) ),
    inference(resolution,[status(thm)],[c_2739,c_18])).

tff(c_2857,plain,(
    ! [D_390] : k9_relat_1('#skF_1',D_390) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_2808,c_2192])).

tff(c_2702,plain,(
    ! [A_380,B_381,D_383] : k7_relset_1(A_380,B_381,'#skF_1',D_383) = k9_relat_1('#skF_1',D_383) ),
    inference(resolution,[status(thm)],[c_2174,c_2686])).

tff(c_2248,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_1',k7_relset_1('#skF_1','#skF_1','#skF_1','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2220,c_2220,c_2160,c_2160,c_62])).

tff(c_2635,plain,(
    k10_relat_1('#skF_1',k7_relset_1('#skF_1','#skF_1','#skF_1','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2634,c_2248])).

tff(c_2703,plain,(
    k10_relat_1('#skF_1',k9_relat_1('#skF_1','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2702,c_2635])).

tff(c_2864,plain,(
    k10_relat_1('#skF_1','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2857,c_2703])).

tff(c_2959,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2935,c_2864])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:54:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.19/1.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.55/1.79  
% 4.55/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.55/1.79  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.55/1.79  
% 4.55/1.79  %Foreground sorts:
% 4.55/1.79  
% 4.55/1.79  
% 4.55/1.79  %Background operators:
% 4.55/1.79  
% 4.55/1.79  
% 4.55/1.79  %Foreground operators:
% 4.55/1.79  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.55/1.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.55/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.55/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.55/1.79  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.55/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.55/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.55/1.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.55/1.79  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.55/1.79  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.55/1.79  tff('#skF_2', type, '#skF_2': $i).
% 4.55/1.79  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.55/1.79  tff('#skF_3', type, '#skF_3': $i).
% 4.55/1.79  tff('#skF_1', type, '#skF_1': $i).
% 4.55/1.79  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.55/1.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.55/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.55/1.79  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.55/1.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.55/1.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.55/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.55/1.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.55/1.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.55/1.79  
% 4.63/1.81  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.63/1.81  tff(f_142, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, k7_relset_1(A, B, C, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_funct_2)).
% 4.63/1.81  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.63/1.81  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.63/1.81  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.63/1.81  tff(f_129, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 4.63/1.81  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.63/1.81  tff(f_81, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.63/1.81  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 4.63/1.81  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 4.63/1.81  tff(f_77, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.63/1.81  tff(f_43, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 4.63/1.81  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.63/1.81  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 4.63/1.81  tff(f_69, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 4.63/1.81  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.63/1.81  tff(c_66, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.63/1.81  tff(c_132, plain, (![C_54, A_55, B_56]: (v1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.63/1.81  tff(c_149, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_132])).
% 4.63/1.81  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.63/1.81  tff(c_64, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.63/1.81  tff(c_79, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_64])).
% 4.63/1.81  tff(c_68, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.63/1.81  tff(c_242, plain, (![A_77, B_78, C_79]: (k1_relset_1(A_77, B_78, C_79)=k1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.63/1.81  tff(c_261, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_242])).
% 4.63/1.81  tff(c_896, plain, (![B_167, A_168, C_169]: (k1_xboole_0=B_167 | k1_relset_1(A_168, B_167, C_169)=A_168 | ~v1_funct_2(C_169, A_168, B_167) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_168, B_167))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.63/1.81  tff(c_910, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_896])).
% 4.63/1.81  tff(c_926, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_261, c_910])).
% 4.63/1.81  tff(c_927, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_79, c_926])).
% 4.63/1.81  tff(c_56, plain, (![B_42, A_41]: (m1_subset_1(B_42, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_42), A_41))) | ~r1_tarski(k2_relat_1(B_42), A_41) | ~v1_funct_1(B_42) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.63/1.81  tff(c_936, plain, (![A_41]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_41))) | ~r1_tarski(k2_relat_1('#skF_3'), A_41) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_927, c_56])).
% 4.63/1.81  tff(c_999, plain, (![A_175]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_175))) | ~r1_tarski(k2_relat_1('#skF_3'), A_175))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_70, c_936])).
% 4.63/1.81  tff(c_18, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.63/1.81  tff(c_1048, plain, (![A_177]: (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', A_177)) | ~r1_tarski(k2_relat_1('#skF_3'), A_177))), inference(resolution, [status(thm)], [c_999, c_18])).
% 4.63/1.81  tff(c_1053, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', k2_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_6, c_1048])).
% 4.63/1.81  tff(c_20, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.63/1.81  tff(c_440, plain, (![A_110, B_111, C_112, D_113]: (k8_relset_1(A_110, B_111, C_112, D_113)=k10_relat_1(C_112, D_113) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.63/1.81  tff(c_1352, plain, (![A_213, B_214, A_215, D_216]: (k8_relset_1(A_213, B_214, A_215, D_216)=k10_relat_1(A_215, D_216) | ~r1_tarski(A_215, k2_zfmisc_1(A_213, B_214)))), inference(resolution, [status(thm)], [c_20, c_440])).
% 4.63/1.81  tff(c_1367, plain, (![D_216]: (k8_relset_1('#skF_1', k2_relat_1('#skF_3'), '#skF_3', D_216)=k10_relat_1('#skF_3', D_216))), inference(resolution, [status(thm)], [c_1053, c_1352])).
% 4.63/1.81  tff(c_30, plain, (![A_21, B_22, C_23]: (k1_relset_1(A_21, B_22, C_23)=k1_relat_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.63/1.81  tff(c_1013, plain, (![A_175]: (k1_relset_1('#skF_1', A_175, '#skF_3')=k1_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), A_175))), inference(resolution, [status(thm)], [c_999, c_30])).
% 4.63/1.81  tff(c_1038, plain, (![A_176]: (k1_relset_1('#skF_1', A_176, '#skF_3')='#skF_1' | ~r1_tarski(k2_relat_1('#skF_3'), A_176))), inference(demodulation, [status(thm), theory('equality')], [c_927, c_1013])).
% 4.63/1.81  tff(c_1043, plain, (k1_relset_1('#skF_1', k2_relat_1('#skF_3'), '#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_6, c_1038])).
% 4.63/1.81  tff(c_36, plain, (![A_32, B_33, C_34]: (k8_relset_1(A_32, B_33, C_34, B_33)=k1_relset_1(A_32, B_33, C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.63/1.81  tff(c_2128, plain, (![A_280]: (k8_relset_1('#skF_1', A_280, '#skF_3', A_280)=k1_relset_1('#skF_1', A_280, '#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), A_280))), inference(resolution, [status(thm)], [c_999, c_36])).
% 4.63/1.81  tff(c_2133, plain, (k8_relset_1('#skF_1', k2_relat_1('#skF_3'), '#skF_3', k2_relat_1('#skF_3'))=k1_relset_1('#skF_1', k2_relat_1('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_6, c_2128])).
% 4.63/1.81  tff(c_2137, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1367, c_1043, c_2133])).
% 4.63/1.81  tff(c_481, plain, (![B_123, A_124]: (k9_relat_1(B_123, k10_relat_1(B_123, A_124))=A_124 | ~r1_tarski(A_124, k2_relat_1(B_123)) | ~v1_funct_1(B_123) | ~v1_relat_1(B_123))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.63/1.81  tff(c_489, plain, (![B_123]: (k9_relat_1(B_123, k10_relat_1(B_123, k2_relat_1(B_123)))=k2_relat_1(B_123) | ~v1_funct_1(B_123) | ~v1_relat_1(B_123))), inference(resolution, [status(thm)], [c_6, c_481])).
% 4.63/1.81  tff(c_2142, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2137, c_489])).
% 4.63/1.81  tff(c_2146, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_70, c_2142])).
% 4.63/1.81  tff(c_522, plain, (![A_131, B_132, C_133, D_134]: (k7_relset_1(A_131, B_132, C_133, D_134)=k9_relat_1(C_133, D_134) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.63/1.81  tff(c_540, plain, (![D_134]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_134)=k9_relat_1('#skF_3', D_134))), inference(resolution, [status(thm)], [c_66, c_522])).
% 4.63/1.81  tff(c_458, plain, (![D_113]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_113)=k10_relat_1('#skF_3', D_113))), inference(resolution, [status(thm)], [c_66, c_440])).
% 4.63/1.81  tff(c_62, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.63/1.81  tff(c_461, plain, (k10_relat_1('#skF_3', k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_458, c_62])).
% 4.63/1.81  tff(c_542, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_540, c_461])).
% 4.63/1.81  tff(c_2150, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2146, c_542])).
% 4.63/1.81  tff(c_2153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2137, c_2150])).
% 4.63/1.81  tff(c_2154, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_64])).
% 4.63/1.81  tff(c_16, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.63/1.81  tff(c_2174, plain, (![A_6]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_2154, c_16])).
% 4.63/1.81  tff(c_2618, plain, (![A_364, B_365, C_366, D_367]: (k8_relset_1(A_364, B_365, C_366, D_367)=k10_relat_1(C_366, D_367) | ~m1_subset_1(C_366, k1_zfmisc_1(k2_zfmisc_1(A_364, B_365))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.63/1.81  tff(c_2634, plain, (![A_364, B_365, D_367]: (k8_relset_1(A_364, B_365, '#skF_1', D_367)=k10_relat_1('#skF_1', D_367))), inference(resolution, [status(thm)], [c_2174, c_2618])).
% 4.63/1.81  tff(c_2325, plain, (![A_308, B_309, C_310]: (k1_relset_1(A_308, B_309, C_310)=k1_relat_1(C_310) | ~m1_subset_1(C_310, k1_zfmisc_1(k2_zfmisc_1(A_308, B_309))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.63/1.81  tff(c_2341, plain, (![A_308, B_309]: (k1_relset_1(A_308, B_309, '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_2174, c_2325])).
% 4.63/1.81  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.63/1.81  tff(c_44, plain, (![C_37, B_36]: (v1_funct_2(C_37, k1_xboole_0, B_36) | k1_relset_1(k1_xboole_0, B_36, C_37)!=k1_xboole_0 | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_36))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.63/1.81  tff(c_75, plain, (![C_37, B_36]: (v1_funct_2(C_37, k1_xboole_0, B_36) | k1_relset_1(k1_xboole_0, B_36, C_37)!=k1_xboole_0 | ~m1_subset_1(C_37, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_44])).
% 4.63/1.81  tff(c_2454, plain, (![C_335, B_336]: (v1_funct_2(C_335, '#skF_1', B_336) | k1_relset_1('#skF_1', B_336, C_335)!='#skF_1' | ~m1_subset_1(C_335, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2154, c_2154, c_2154, c_2154, c_75])).
% 4.63/1.81  tff(c_2460, plain, (![B_336]: (v1_funct_2('#skF_1', '#skF_1', B_336) | k1_relset_1('#skF_1', B_336, '#skF_1')!='#skF_1')), inference(resolution, [status(thm)], [c_2174, c_2454])).
% 4.63/1.81  tff(c_2463, plain, (![B_336]: (v1_funct_2('#skF_1', '#skF_1', B_336) | k1_relat_1('#skF_1')!='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2341, c_2460])).
% 4.63/1.81  tff(c_2464, plain, (k1_relat_1('#skF_1')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2463])).
% 4.63/1.81  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.63/1.81  tff(c_2166, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2154, c_2154, c_12])).
% 4.63/1.81  tff(c_2155, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_64])).
% 4.63/1.81  tff(c_2160, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2154, c_2155])).
% 4.63/1.81  tff(c_2200, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2166, c_2160, c_66])).
% 4.63/1.81  tff(c_2204, plain, (![A_288, B_289]: (r1_tarski(A_288, B_289) | ~m1_subset_1(A_288, k1_zfmisc_1(B_289)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.63/1.81  tff(c_2215, plain, (r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_2200, c_2204])).
% 4.63/1.81  tff(c_8, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.63/1.81  tff(c_2192, plain, (![A_3]: (A_3='#skF_1' | ~r1_tarski(A_3, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2154, c_2154, c_8])).
% 4.63/1.81  tff(c_2220, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_2215, c_2192])).
% 4.63/1.81  tff(c_2161, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2160, c_68])).
% 4.63/1.81  tff(c_2223, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2220, c_2161])).
% 4.63/1.81  tff(c_48, plain, (![B_36, C_37]: (k1_relset_1(k1_xboole_0, B_36, C_37)=k1_xboole_0 | ~v1_funct_2(C_37, k1_xboole_0, B_36) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_36))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.63/1.81  tff(c_74, plain, (![B_36, C_37]: (k1_relset_1(k1_xboole_0, B_36, C_37)=k1_xboole_0 | ~v1_funct_2(C_37, k1_xboole_0, B_36) | ~m1_subset_1(C_37, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_48])).
% 4.63/1.81  tff(c_2471, plain, (![B_339, C_340]: (k1_relset_1('#skF_1', B_339, C_340)='#skF_1' | ~v1_funct_2(C_340, '#skF_1', B_339) | ~m1_subset_1(C_340, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2154, c_2154, c_2154, c_2154, c_74])).
% 4.63/1.81  tff(c_2475, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_1')='#skF_1' | ~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_2223, c_2471])).
% 4.63/1.81  tff(c_2482, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2174, c_2341, c_2475])).
% 4.63/1.81  tff(c_2484, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2464, c_2482])).
% 4.63/1.81  tff(c_2486, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(splitRight, [status(thm)], [c_2463])).
% 4.63/1.81  tff(c_2487, plain, (![A_308, B_309]: (k1_relset_1(A_308, B_309, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2486, c_2341])).
% 4.63/1.81  tff(c_2918, plain, (![A_393, B_394, C_395]: (k8_relset_1(A_393, B_394, C_395, B_394)=k1_relset_1(A_393, B_394, C_395) | ~m1_subset_1(C_395, k1_zfmisc_1(k2_zfmisc_1(A_393, B_394))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.63/1.81  tff(c_2929, plain, (![A_393, B_394]: (k8_relset_1(A_393, B_394, '#skF_1', B_394)=k1_relset_1(A_393, B_394, '#skF_1'))), inference(resolution, [status(thm)], [c_2174, c_2918])).
% 4.63/1.81  tff(c_2935, plain, (![B_394]: (k10_relat_1('#skF_1', B_394)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2634, c_2487, c_2929])).
% 4.63/1.81  tff(c_2686, plain, (![A_380, B_381, C_382, D_383]: (k7_relset_1(A_380, B_381, C_382, D_383)=k9_relat_1(C_382, D_383) | ~m1_subset_1(C_382, k1_zfmisc_1(k2_zfmisc_1(A_380, B_381))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.63/1.81  tff(c_2705, plain, (![A_384, B_385, D_386]: (k7_relset_1(A_384, B_385, '#skF_1', D_386)=k9_relat_1('#skF_1', D_386))), inference(resolution, [status(thm)], [c_2174, c_2686])).
% 4.63/1.81  tff(c_28, plain, (![A_17, B_18, C_19, D_20]: (m1_subset_1(k7_relset_1(A_17, B_18, C_19, D_20), k1_zfmisc_1(B_18)) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.63/1.81  tff(c_2715, plain, (![D_386, B_385, A_384]: (m1_subset_1(k9_relat_1('#skF_1', D_386), k1_zfmisc_1(B_385)) | ~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(A_384, B_385))))), inference(superposition, [status(thm), theory('equality')], [c_2705, c_28])).
% 4.63/1.81  tff(c_2739, plain, (![D_388, B_389]: (m1_subset_1(k9_relat_1('#skF_1', D_388), k1_zfmisc_1(B_389)))), inference(demodulation, [status(thm), theory('equality')], [c_2174, c_2715])).
% 4.63/1.81  tff(c_2808, plain, (![D_390, B_391]: (r1_tarski(k9_relat_1('#skF_1', D_390), B_391))), inference(resolution, [status(thm)], [c_2739, c_18])).
% 4.63/1.81  tff(c_2857, plain, (![D_390]: (k9_relat_1('#skF_1', D_390)='#skF_1')), inference(resolution, [status(thm)], [c_2808, c_2192])).
% 4.63/1.81  tff(c_2702, plain, (![A_380, B_381, D_383]: (k7_relset_1(A_380, B_381, '#skF_1', D_383)=k9_relat_1('#skF_1', D_383))), inference(resolution, [status(thm)], [c_2174, c_2686])).
% 4.63/1.81  tff(c_2248, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_1', k7_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2220, c_2220, c_2160, c_2160, c_62])).
% 4.63/1.81  tff(c_2635, plain, (k10_relat_1('#skF_1', k7_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2634, c_2248])).
% 4.63/1.81  tff(c_2703, plain, (k10_relat_1('#skF_1', k9_relat_1('#skF_1', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2702, c_2635])).
% 4.63/1.81  tff(c_2864, plain, (k10_relat_1('#skF_1', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2857, c_2703])).
% 4.63/1.81  tff(c_2959, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2935, c_2864])).
% 4.63/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.81  
% 4.63/1.81  Inference rules
% 4.63/1.81  ----------------------
% 4.63/1.81  #Ref     : 0
% 4.63/1.81  #Sup     : 624
% 4.63/1.81  #Fact    : 0
% 4.63/1.81  #Define  : 0
% 4.63/1.81  #Split   : 9
% 4.63/1.81  #Chain   : 0
% 4.63/1.81  #Close   : 0
% 4.63/1.81  
% 4.63/1.81  Ordering : KBO
% 4.63/1.81  
% 4.63/1.81  Simplification rules
% 4.63/1.81  ----------------------
% 4.63/1.81  #Subsume      : 67
% 4.63/1.81  #Demod        : 483
% 4.63/1.81  #Tautology    : 288
% 4.63/1.81  #SimpNegUnit  : 7
% 4.63/1.81  #BackRed      : 30
% 4.63/1.81  
% 4.63/1.81  #Partial instantiations: 0
% 4.63/1.81  #Strategies tried      : 1
% 4.63/1.81  
% 4.63/1.81  Timing (in seconds)
% 4.63/1.81  ----------------------
% 4.72/1.81  Preprocessing        : 0.34
% 4.72/1.82  Parsing              : 0.18
% 4.72/1.82  CNF conversion       : 0.02
% 4.72/1.82  Main loop            : 0.69
% 4.72/1.82  Inferencing          : 0.24
% 4.72/1.82  Reduction            : 0.24
% 4.72/1.82  Demodulation         : 0.16
% 4.72/1.82  BG Simplification    : 0.03
% 4.72/1.82  Subsumption          : 0.12
% 4.72/1.82  Abstraction          : 0.05
% 4.72/1.82  MUC search           : 0.00
% 4.72/1.82  Cooper               : 0.00
% 4.72/1.82  Total                : 1.07
% 4.72/1.82  Index Insertion      : 0.00
% 4.72/1.82  Index Deletion       : 0.00
% 4.72/1.82  Index Matching       : 0.00
% 4.72/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
