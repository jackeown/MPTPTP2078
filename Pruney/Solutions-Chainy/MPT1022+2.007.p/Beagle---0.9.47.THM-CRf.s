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
% DateTime   : Thu Dec  3 10:16:14 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 443 expanded)
%              Number of leaves         :   36 ( 170 expanded)
%              Depth                    :   13
%              Number of atoms          :  180 (1221 expanded)
%              Number of equality atoms :   57 ( 346 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_112,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,A)
          & v3_funct_2(C,A,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r1_tarski(B,A)
         => ( k7_relset_1(A,A,C,k8_relset_1(A,A,C,B)) = B
            & k8_relset_1(A,A,C,k7_relset_1(A,A,C,B)) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_funct_2)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(c_34,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_43,plain,(
    ! [C_28,A_29,B_30] :
      ( v1_relat_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_47,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_43])).

tff(c_42,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_38,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_294,plain,(
    ! [C_96,A_97,B_98] :
      ( v2_funct_1(C_96)
      | ~ v3_funct_2(C_96,A_97,B_98)
      | ~ v1_funct_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_297,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_294])).

tff(c_300,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_297])).

tff(c_40,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_57,plain,(
    ! [C_32,B_33,A_34] :
      ( v5_relat_1(C_32,B_33)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_34,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_61,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_57])).

tff(c_210,plain,(
    ! [B_76,A_77] :
      ( k2_relat_1(B_76) = A_77
      | ~ v2_funct_2(B_76,A_77)
      | ~ v5_relat_1(B_76,A_77)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_213,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_61,c_210])).

tff(c_216,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_213])).

tff(c_217,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_216])).

tff(c_283,plain,(
    ! [C_93,B_94,A_95] :
      ( v2_funct_2(C_93,B_94)
      | ~ v3_funct_2(C_93,A_95,B_94)
      | ~ v1_funct_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_95,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_286,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_283])).

tff(c_289,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_286])).

tff(c_291,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_217,c_289])).

tff(c_292,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_2,plain,(
    ! [A_1] :
      ( k10_relat_1(A_1,k2_relat_1(A_1)) = k1_relat_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_307,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_2])).

tff(c_313,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_307])).

tff(c_320,plain,(
    ! [A_99,B_100,C_101,D_102] :
      ( k8_relset_1(A_99,B_100,C_101,D_102) = k10_relat_1(C_101,D_102)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_323,plain,(
    ! [D_102] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_102) = k10_relat_1('#skF_3',D_102) ),
    inference(resolution,[status(thm)],[c_36,c_320])).

tff(c_409,plain,(
    ! [B_119,A_120,C_121] :
      ( k1_xboole_0 = B_119
      | k8_relset_1(A_120,B_119,C_121,B_119) = A_120
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_120,B_119)))
      | ~ v1_funct_2(C_121,A_120,B_119)
      | ~ v1_funct_1(C_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_411,plain,
    ( k1_xboole_0 = '#skF_1'
    | k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_1') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_409])).

tff(c_414,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_313,c_323,c_411])).

tff(c_415,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_414])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( k10_relat_1(B_5,k9_relat_1(B_5,A_4)) = A_4
      | ~ v2_funct_1(B_5)
      | ~ r1_tarski(A_4,k1_relat_1(B_5))
      | ~ v1_funct_1(B_5)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_419,plain,(
    ! [A_4] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_4)) = A_4
      | ~ v2_funct_1('#skF_3')
      | ~ r1_tarski(A_4,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_415,c_6])).

tff(c_432,plain,(
    ! [A_122] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_122)) = A_122
      | ~ r1_tarski(A_122,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_42,c_300,c_419])).

tff(c_363,plain,(
    ! [A_107,B_108,C_109,D_110] :
      ( k7_relset_1(A_107,B_108,C_109,D_110) = k9_relat_1(C_109,D_110)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_366,plain,(
    ! [D_110] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_110) = k9_relat_1('#skF_3',D_110) ),
    inference(resolution,[status(thm)],[c_36,c_363])).

tff(c_69,plain,(
    ! [B_39,A_40] :
      ( k2_relat_1(B_39) = A_40
      | ~ v2_funct_2(B_39,A_40)
      | ~ v5_relat_1(B_39,A_40)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_72,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_61,c_69])).

tff(c_75,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_72])).

tff(c_76,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_75])).

tff(c_113,plain,(
    ! [C_56,B_57,A_58] :
      ( v2_funct_2(C_56,B_57)
      | ~ v3_funct_2(C_56,A_58,B_57)
      | ~ v1_funct_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_58,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_116,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_113])).

tff(c_119,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38,c_116])).

tff(c_121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_119])).

tff(c_122,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_75])).

tff(c_171,plain,(
    ! [B_69,A_70] :
      ( k9_relat_1(B_69,k10_relat_1(B_69,A_70)) = A_70
      | ~ r1_tarski(A_70,k2_relat_1(B_69))
      | ~ v1_funct_1(B_69)
      | ~ v1_relat_1(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_173,plain,(
    ! [A_70] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_70)) = A_70
      | ~ r1_tarski(A_70,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_171])).

tff(c_176,plain,(
    ! [A_71] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_71)) = A_71
      | ~ r1_tarski(A_71,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_42,c_173])).

tff(c_157,plain,(
    ! [A_64,B_65,C_66,D_67] :
      ( k7_relset_1(A_64,B_65,C_66,D_67) = k9_relat_1(C_66,D_67)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_160,plain,(
    ! [D_67] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_67) = k9_relat_1('#skF_3',D_67) ),
    inference(resolution,[status(thm)],[c_36,c_157])).

tff(c_143,plain,(
    ! [A_59,B_60,C_61,D_62] :
      ( k8_relset_1(A_59,B_60,C_61,D_62) = k10_relat_1(C_61,D_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_146,plain,(
    ! [D_62] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_62) = k10_relat_1('#skF_3',D_62) ),
    inference(resolution,[status(thm)],[c_36,c_143])).

tff(c_32,plain,
    ( k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2'
    | k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_62,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_147,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3',k10_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_62])).

tff(c_161,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_147])).

tff(c_182,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_161])).

tff(c_197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_182])).

tff(c_198,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_325,plain,(
    k10_relat_1('#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_198])).

tff(c_367,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_325])).

tff(c_438,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_432,c_367])).

tff(c_455,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_438])).

tff(c_457,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_414])).

tff(c_456,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_414])).

tff(c_28,plain,(
    ! [B_26,C_27] :
      ( k8_relset_1(k1_xboole_0,B_26,C_27,B_26) = k1_xboole_0
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_26)))
      | ~ v1_funct_2(C_27,k1_xboole_0,B_26)
      | ~ v1_funct_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_464,plain,(
    ! [B_123,C_124] :
      ( k8_relset_1('#skF_1',B_123,C_124,B_123) = '#skF_1'
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_123)))
      | ~ v1_funct_2(C_124,'#skF_1',B_123)
      | ~ v1_funct_1(C_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_456,c_456,c_456,c_28])).

tff(c_466,plain,
    ( k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_1') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_464])).

tff(c_469,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_313,c_323,c_466])).

tff(c_471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_457,c_469])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:53:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.39  
% 2.55/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.40  %$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.55/1.40  
% 2.55/1.40  %Foreground sorts:
% 2.55/1.40  
% 2.55/1.40  
% 2.55/1.40  %Background operators:
% 2.55/1.40  
% 2.55/1.40  
% 2.55/1.40  %Foreground operators:
% 2.55/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.55/1.40  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.55/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.40  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.55/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.55/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.55/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.55/1.40  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.55/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.55/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.55/1.40  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.55/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.55/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.55/1.40  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 2.55/1.40  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.55/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.55/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.40  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.55/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.55/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.55/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.40  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.55/1.40  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 2.55/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.55/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.55/1.40  
% 2.55/1.41  tff(f_112, negated_conjecture, ~(![A, B, C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_tarski(B, A) => ((k7_relset_1(A, A, C, k8_relset_1(A, A, C, B)) = B) & (k8_relset_1(A, A, C, k7_relset_1(A, A, C, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_funct_2)).
% 2.55/1.41  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.55/1.41  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 2.55/1.41  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.55/1.41  tff(f_85, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 2.55/1.41  tff(f_29, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.55/1.41  tff(f_65, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.55/1.41  tff(f_97, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_2)).
% 2.55/1.41  tff(f_47, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 2.55/1.41  tff(f_61, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.55/1.41  tff(f_37, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 2.55/1.41  tff(c_34, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.55/1.41  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.55/1.41  tff(c_43, plain, (![C_28, A_29, B_30]: (v1_relat_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.55/1.41  tff(c_47, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_43])).
% 2.55/1.41  tff(c_42, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.55/1.42  tff(c_38, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.55/1.42  tff(c_294, plain, (![C_96, A_97, B_98]: (v2_funct_1(C_96) | ~v3_funct_2(C_96, A_97, B_98) | ~v1_funct_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.55/1.42  tff(c_297, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_294])).
% 2.55/1.42  tff(c_300, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_297])).
% 2.55/1.42  tff(c_40, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.55/1.42  tff(c_57, plain, (![C_32, B_33, A_34]: (v5_relat_1(C_32, B_33) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_34, B_33))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.55/1.42  tff(c_61, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_36, c_57])).
% 2.55/1.42  tff(c_210, plain, (![B_76, A_77]: (k2_relat_1(B_76)=A_77 | ~v2_funct_2(B_76, A_77) | ~v5_relat_1(B_76, A_77) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.55/1.42  tff(c_213, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_61, c_210])).
% 2.55/1.42  tff(c_216, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_213])).
% 2.55/1.42  tff(c_217, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_216])).
% 2.55/1.42  tff(c_283, plain, (![C_93, B_94, A_95]: (v2_funct_2(C_93, B_94) | ~v3_funct_2(C_93, A_95, B_94) | ~v1_funct_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_95, B_94))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.55/1.42  tff(c_286, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_283])).
% 2.55/1.42  tff(c_289, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_286])).
% 2.55/1.42  tff(c_291, plain, $false, inference(negUnitSimplification, [status(thm)], [c_217, c_289])).
% 2.55/1.42  tff(c_292, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_216])).
% 2.55/1.42  tff(c_2, plain, (![A_1]: (k10_relat_1(A_1, k2_relat_1(A_1))=k1_relat_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.55/1.42  tff(c_307, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_292, c_2])).
% 2.55/1.42  tff(c_313, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_307])).
% 2.55/1.42  tff(c_320, plain, (![A_99, B_100, C_101, D_102]: (k8_relset_1(A_99, B_100, C_101, D_102)=k10_relat_1(C_101, D_102) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.55/1.42  tff(c_323, plain, (![D_102]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_102)=k10_relat_1('#skF_3', D_102))), inference(resolution, [status(thm)], [c_36, c_320])).
% 2.55/1.42  tff(c_409, plain, (![B_119, A_120, C_121]: (k1_xboole_0=B_119 | k8_relset_1(A_120, B_119, C_121, B_119)=A_120 | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_120, B_119))) | ~v1_funct_2(C_121, A_120, B_119) | ~v1_funct_1(C_121))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.55/1.42  tff(c_411, plain, (k1_xboole_0='#skF_1' | k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_409])).
% 2.55/1.42  tff(c_414, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_313, c_323, c_411])).
% 2.55/1.42  tff(c_415, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_414])).
% 2.55/1.42  tff(c_6, plain, (![B_5, A_4]: (k10_relat_1(B_5, k9_relat_1(B_5, A_4))=A_4 | ~v2_funct_1(B_5) | ~r1_tarski(A_4, k1_relat_1(B_5)) | ~v1_funct_1(B_5) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.55/1.42  tff(c_419, plain, (![A_4]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_4))=A_4 | ~v2_funct_1('#skF_3') | ~r1_tarski(A_4, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_415, c_6])).
% 2.55/1.42  tff(c_432, plain, (![A_122]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_122))=A_122 | ~r1_tarski(A_122, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_42, c_300, c_419])).
% 2.55/1.42  tff(c_363, plain, (![A_107, B_108, C_109, D_110]: (k7_relset_1(A_107, B_108, C_109, D_110)=k9_relat_1(C_109, D_110) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.55/1.42  tff(c_366, plain, (![D_110]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_110)=k9_relat_1('#skF_3', D_110))), inference(resolution, [status(thm)], [c_36, c_363])).
% 2.55/1.42  tff(c_69, plain, (![B_39, A_40]: (k2_relat_1(B_39)=A_40 | ~v2_funct_2(B_39, A_40) | ~v5_relat_1(B_39, A_40) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.55/1.42  tff(c_72, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_61, c_69])).
% 2.55/1.42  tff(c_75, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_47, c_72])).
% 2.55/1.42  tff(c_76, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_75])).
% 2.55/1.42  tff(c_113, plain, (![C_56, B_57, A_58]: (v2_funct_2(C_56, B_57) | ~v3_funct_2(C_56, A_58, B_57) | ~v1_funct_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_58, B_57))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.55/1.42  tff(c_116, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_113])).
% 2.55/1.42  tff(c_119, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38, c_116])).
% 2.55/1.42  tff(c_121, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_119])).
% 2.55/1.42  tff(c_122, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_75])).
% 2.55/1.42  tff(c_171, plain, (![B_69, A_70]: (k9_relat_1(B_69, k10_relat_1(B_69, A_70))=A_70 | ~r1_tarski(A_70, k2_relat_1(B_69)) | ~v1_funct_1(B_69) | ~v1_relat_1(B_69))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.55/1.42  tff(c_173, plain, (![A_70]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_70))=A_70 | ~r1_tarski(A_70, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_122, c_171])).
% 2.55/1.42  tff(c_176, plain, (![A_71]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_71))=A_71 | ~r1_tarski(A_71, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_42, c_173])).
% 2.55/1.42  tff(c_157, plain, (![A_64, B_65, C_66, D_67]: (k7_relset_1(A_64, B_65, C_66, D_67)=k9_relat_1(C_66, D_67) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.55/1.42  tff(c_160, plain, (![D_67]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_67)=k9_relat_1('#skF_3', D_67))), inference(resolution, [status(thm)], [c_36, c_157])).
% 2.55/1.42  tff(c_143, plain, (![A_59, B_60, C_61, D_62]: (k8_relset_1(A_59, B_60, C_61, D_62)=k10_relat_1(C_61, D_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.55/1.42  tff(c_146, plain, (![D_62]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_62)=k10_relat_1('#skF_3', D_62))), inference(resolution, [status(thm)], [c_36, c_143])).
% 2.55/1.42  tff(c_32, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2' | k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.55/1.42  tff(c_62, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_32])).
% 2.55/1.42  tff(c_147, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', k10_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_146, c_62])).
% 2.55/1.42  tff(c_161, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_160, c_147])).
% 2.55/1.42  tff(c_182, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_176, c_161])).
% 2.55/1.42  tff(c_197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_182])).
% 2.55/1.42  tff(c_198, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitRight, [status(thm)], [c_32])).
% 2.55/1.42  tff(c_325, plain, (k10_relat_1('#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_323, c_198])).
% 2.55/1.42  tff(c_367, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_366, c_325])).
% 2.55/1.42  tff(c_438, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_432, c_367])).
% 2.55/1.42  tff(c_455, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_438])).
% 2.55/1.42  tff(c_457, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitRight, [status(thm)], [c_414])).
% 2.55/1.42  tff(c_456, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_414])).
% 2.55/1.42  tff(c_28, plain, (![B_26, C_27]: (k8_relset_1(k1_xboole_0, B_26, C_27, B_26)=k1_xboole_0 | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_26))) | ~v1_funct_2(C_27, k1_xboole_0, B_26) | ~v1_funct_1(C_27))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.55/1.42  tff(c_464, plain, (![B_123, C_124]: (k8_relset_1('#skF_1', B_123, C_124, B_123)='#skF_1' | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_123))) | ~v1_funct_2(C_124, '#skF_1', B_123) | ~v1_funct_1(C_124))), inference(demodulation, [status(thm), theory('equality')], [c_456, c_456, c_456, c_456, c_28])).
% 2.55/1.42  tff(c_466, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_464])).
% 2.55/1.42  tff(c_469, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_313, c_323, c_466])).
% 2.55/1.42  tff(c_471, plain, $false, inference(negUnitSimplification, [status(thm)], [c_457, c_469])).
% 2.55/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.42  
% 2.55/1.42  Inference rules
% 2.55/1.42  ----------------------
% 2.55/1.42  #Ref     : 0
% 2.55/1.42  #Sup     : 97
% 2.55/1.42  #Fact    : 0
% 2.55/1.42  #Define  : 0
% 2.55/1.42  #Split   : 5
% 2.55/1.42  #Chain   : 0
% 2.55/1.42  #Close   : 0
% 2.55/1.42  
% 2.55/1.42  Ordering : KBO
% 2.55/1.42  
% 2.55/1.42  Simplification rules
% 2.55/1.42  ----------------------
% 2.55/1.42  #Subsume      : 2
% 2.55/1.42  #Demod        : 68
% 2.55/1.42  #Tautology    : 58
% 2.55/1.42  #SimpNegUnit  : 3
% 2.55/1.42  #BackRed      : 14
% 2.55/1.42  
% 2.55/1.42  #Partial instantiations: 0
% 2.55/1.42  #Strategies tried      : 1
% 2.55/1.42  
% 2.55/1.42  Timing (in seconds)
% 2.55/1.42  ----------------------
% 2.55/1.42  Preprocessing        : 0.33
% 2.55/1.42  Parsing              : 0.18
% 2.55/1.42  CNF conversion       : 0.02
% 2.55/1.42  Main loop            : 0.24
% 2.55/1.42  Inferencing          : 0.10
% 2.55/1.42  Reduction            : 0.07
% 2.55/1.42  Demodulation         : 0.05
% 2.55/1.42  BG Simplification    : 0.02
% 2.55/1.42  Subsumption          : 0.03
% 2.55/1.42  Abstraction          : 0.01
% 2.55/1.42  MUC search           : 0.00
% 2.55/1.42  Cooper               : 0.00
% 2.55/1.42  Total                : 0.61
% 2.55/1.42  Index Insertion      : 0.00
% 2.55/1.42  Index Deletion       : 0.00
% 2.55/1.42  Index Matching       : 0.00
% 2.55/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
