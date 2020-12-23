%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:13 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 151 expanded)
%              Number of leaves         :   36 (  69 expanded)
%              Depth                    :    9
%              Number of atoms          :  137 ( 377 expanded)
%              Number of equality atoms :   40 (  98 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,A)
          & v3_funct_2(C,A,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r1_tarski(B,A)
         => ( k7_relset_1(A,A,C,k8_relset_1(A,A,C,B)) = B
            & k8_relset_1(A,A,C,k7_relset_1(A,A,C,B)) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_funct_2)).

tff(f_47,axiom,(
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
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_53,axiom,(
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

tff(f_33,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(c_32,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_41,plain,(
    ! [C_29,A_30,B_31] :
      ( v1_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_45,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_41])).

tff(c_40,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_36,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_377,plain,(
    ! [C_121,A_122,B_123] :
      ( v2_funct_1(C_121)
      | ~ v3_funct_2(C_121,A_122,B_123)
      | ~ v1_funct_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_380,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_377])).

tff(c_383,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_380])).

tff(c_38,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_280,plain,(
    ! [A_105,B_106,C_107] :
      ( k1_relset_1(A_105,B_106,C_107) = k1_relat_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_284,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_280])).

tff(c_392,plain,(
    ! [A_129,B_130] :
      ( k1_relset_1(A_129,A_129,B_130) = A_129
      | ~ m1_subset_1(B_130,k1_zfmisc_1(k2_zfmisc_1(A_129,A_129)))
      | ~ v1_funct_2(B_130,A_129,A_129)
      | ~ v1_funct_1(B_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_395,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_392])).

tff(c_398,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_284,c_395])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( k10_relat_1(B_4,k9_relat_1(B_4,A_3)) = A_3
      | ~ v2_funct_1(B_4)
      | ~ r1_tarski(A_3,k1_relat_1(B_4))
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_402,plain,(
    ! [A_3] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_3)) = A_3
      | ~ v2_funct_1('#skF_3')
      | ~ r1_tarski(A_3,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_4])).

tff(c_412,plain,(
    ! [A_131] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_131)) = A_131
      | ~ r1_tarski(A_131,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_40,c_383,c_402])).

tff(c_333,plain,(
    ! [A_116,B_117,C_118,D_119] :
      ( k8_relset_1(A_116,B_117,C_118,D_119) = k10_relat_1(C_118,D_119)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_336,plain,(
    ! [D_119] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_119) = k10_relat_1('#skF_3',D_119) ),
    inference(resolution,[status(thm)],[c_34,c_333])).

tff(c_313,plain,(
    ! [A_111,B_112,C_113,D_114] :
      ( k7_relset_1(A_111,B_112,C_113,D_114) = k9_relat_1(C_113,D_114)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_316,plain,(
    ! [D_114] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_114) = k9_relat_1('#skF_3',D_114) ),
    inference(resolution,[status(thm)],[c_34,c_313])).

tff(c_52,plain,(
    ! [C_35,B_36,A_37] :
      ( v5_relat_1(C_35,B_36)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_37,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_56,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_52])).

tff(c_58,plain,(
    ! [B_39,A_40] :
      ( k2_relat_1(B_39) = A_40
      | ~ v2_funct_2(B_39,A_40)
      | ~ v5_relat_1(B_39,A_40)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_61,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_58])).

tff(c_64,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_61])).

tff(c_74,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_111,plain,(
    ! [C_59,B_60,A_61] :
      ( v2_funct_2(C_59,B_60)
      | ~ v3_funct_2(C_59,A_61,B_60)
      | ~ v1_funct_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_61,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_114,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_111])).

tff(c_117,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_114])).

tff(c_119,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_117])).

tff(c_120,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_132,plain,(
    ! [B_62,A_63] :
      ( k9_relat_1(B_62,k10_relat_1(B_62,A_63)) = A_63
      | ~ r1_tarski(A_63,k2_relat_1(B_62))
      | ~ v1_funct_1(B_62)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_134,plain,(
    ! [A_63] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_63)) = A_63
      | ~ r1_tarski(A_63,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_132])).

tff(c_136,plain,(
    ! [A_63] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_63)) = A_63
      | ~ r1_tarski(A_63,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_40,c_134])).

tff(c_167,plain,(
    ! [A_73,B_74,C_75,D_76] :
      ( k8_relset_1(A_73,B_74,C_75,D_76) = k10_relat_1(C_75,D_76)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_170,plain,(
    ! [D_76] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_76) = k10_relat_1('#skF_3',D_76) ),
    inference(resolution,[status(thm)],[c_34,c_167])).

tff(c_146,plain,(
    ! [A_65,B_66,C_67,D_68] :
      ( k7_relset_1(A_65,B_66,C_67,D_68) = k9_relat_1(C_67,D_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_149,plain,(
    ! [D_68] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_68) = k9_relat_1('#skF_3',D_68) ),
    inference(resolution,[status(thm)],[c_34,c_146])).

tff(c_30,plain,
    ( k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2'
    | k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_51,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_157,plain,(
    k9_relat_1('#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_51])).

tff(c_171,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_157])).

tff(c_183,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_171])).

tff(c_187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_183])).

tff(c_188,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_317,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_316,c_188])).

tff(c_337,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_317])).

tff(c_418,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_337])).

tff(c_435,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_418])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n012.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 17:13:52 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.30  
% 2.23/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.30  %$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.46/1.30  
% 2.46/1.30  %Foreground sorts:
% 2.46/1.30  
% 2.46/1.30  
% 2.46/1.30  %Background operators:
% 2.46/1.30  
% 2.46/1.30  
% 2.46/1.30  %Foreground operators:
% 2.46/1.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.46/1.30  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.46/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.46/1.30  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.46/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.46/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.46/1.30  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.46/1.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.46/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.46/1.30  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.46/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.46/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.46/1.30  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 2.46/1.30  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.46/1.30  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.46/1.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.46/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.46/1.30  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.46/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.46/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.46/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.46/1.30  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.46/1.30  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 2.46/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.46/1.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.46/1.30  
% 2.46/1.32  tff(f_108, negated_conjecture, ~(![A, B, C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_tarski(B, A) => ((k7_relset_1(A, A, C, k8_relset_1(A, A, C, B)) = B) & (k8_relset_1(A, A, C, k7_relset_1(A, A, C, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_funct_2)).
% 2.46/1.32  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.46/1.32  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 2.46/1.32  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.46/1.32  tff(f_93, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 2.46/1.32  tff(f_43, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 2.46/1.32  tff(f_65, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.46/1.32  tff(f_61, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.46/1.32  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.46/1.32  tff(f_85, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 2.46/1.32  tff(f_33, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 2.46/1.32  tff(c_32, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.46/1.32  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.46/1.32  tff(c_41, plain, (![C_29, A_30, B_31]: (v1_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.46/1.32  tff(c_45, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_41])).
% 2.46/1.32  tff(c_40, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.46/1.32  tff(c_36, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.46/1.32  tff(c_377, plain, (![C_121, A_122, B_123]: (v2_funct_1(C_121) | ~v3_funct_2(C_121, A_122, B_123) | ~v1_funct_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.46/1.32  tff(c_380, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_377])).
% 2.46/1.32  tff(c_383, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_380])).
% 2.46/1.32  tff(c_38, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.46/1.32  tff(c_280, plain, (![A_105, B_106, C_107]: (k1_relset_1(A_105, B_106, C_107)=k1_relat_1(C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.46/1.32  tff(c_284, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_280])).
% 2.46/1.32  tff(c_392, plain, (![A_129, B_130]: (k1_relset_1(A_129, A_129, B_130)=A_129 | ~m1_subset_1(B_130, k1_zfmisc_1(k2_zfmisc_1(A_129, A_129))) | ~v1_funct_2(B_130, A_129, A_129) | ~v1_funct_1(B_130))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.46/1.32  tff(c_395, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_392])).
% 2.46/1.32  tff(c_398, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_284, c_395])).
% 2.46/1.32  tff(c_4, plain, (![B_4, A_3]: (k10_relat_1(B_4, k9_relat_1(B_4, A_3))=A_3 | ~v2_funct_1(B_4) | ~r1_tarski(A_3, k1_relat_1(B_4)) | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.46/1.32  tff(c_402, plain, (![A_3]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_3))=A_3 | ~v2_funct_1('#skF_3') | ~r1_tarski(A_3, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_398, c_4])).
% 2.46/1.32  tff(c_412, plain, (![A_131]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_131))=A_131 | ~r1_tarski(A_131, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_40, c_383, c_402])).
% 2.46/1.32  tff(c_333, plain, (![A_116, B_117, C_118, D_119]: (k8_relset_1(A_116, B_117, C_118, D_119)=k10_relat_1(C_118, D_119) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.46/1.32  tff(c_336, plain, (![D_119]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_119)=k10_relat_1('#skF_3', D_119))), inference(resolution, [status(thm)], [c_34, c_333])).
% 2.46/1.32  tff(c_313, plain, (![A_111, B_112, C_113, D_114]: (k7_relset_1(A_111, B_112, C_113, D_114)=k9_relat_1(C_113, D_114) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.46/1.32  tff(c_316, plain, (![D_114]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_114)=k9_relat_1('#skF_3', D_114))), inference(resolution, [status(thm)], [c_34, c_313])).
% 2.46/1.32  tff(c_52, plain, (![C_35, B_36, A_37]: (v5_relat_1(C_35, B_36) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_37, B_36))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.46/1.32  tff(c_56, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_52])).
% 2.46/1.32  tff(c_58, plain, (![B_39, A_40]: (k2_relat_1(B_39)=A_40 | ~v2_funct_2(B_39, A_40) | ~v5_relat_1(B_39, A_40) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.46/1.32  tff(c_61, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56, c_58])).
% 2.46/1.32  tff(c_64, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_45, c_61])).
% 2.46/1.32  tff(c_74, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_64])).
% 2.46/1.32  tff(c_111, plain, (![C_59, B_60, A_61]: (v2_funct_2(C_59, B_60) | ~v3_funct_2(C_59, A_61, B_60) | ~v1_funct_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_61, B_60))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.46/1.32  tff(c_114, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_111])).
% 2.46/1.32  tff(c_117, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_114])).
% 2.46/1.32  tff(c_119, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_117])).
% 2.46/1.32  tff(c_120, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_64])).
% 2.46/1.32  tff(c_132, plain, (![B_62, A_63]: (k9_relat_1(B_62, k10_relat_1(B_62, A_63))=A_63 | ~r1_tarski(A_63, k2_relat_1(B_62)) | ~v1_funct_1(B_62) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.46/1.32  tff(c_134, plain, (![A_63]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_63))=A_63 | ~r1_tarski(A_63, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_120, c_132])).
% 2.46/1.32  tff(c_136, plain, (![A_63]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_63))=A_63 | ~r1_tarski(A_63, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_40, c_134])).
% 2.46/1.32  tff(c_167, plain, (![A_73, B_74, C_75, D_76]: (k8_relset_1(A_73, B_74, C_75, D_76)=k10_relat_1(C_75, D_76) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.46/1.32  tff(c_170, plain, (![D_76]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_76)=k10_relat_1('#skF_3', D_76))), inference(resolution, [status(thm)], [c_34, c_167])).
% 2.46/1.32  tff(c_146, plain, (![A_65, B_66, C_67, D_68]: (k7_relset_1(A_65, B_66, C_67, D_68)=k9_relat_1(C_67, D_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.46/1.32  tff(c_149, plain, (![D_68]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_68)=k9_relat_1('#skF_3', D_68))), inference(resolution, [status(thm)], [c_34, c_146])).
% 2.46/1.32  tff(c_30, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2' | k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.46/1.32  tff(c_51, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_30])).
% 2.46/1.32  tff(c_157, plain, (k9_relat_1('#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_149, c_51])).
% 2.46/1.32  tff(c_171, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_170, c_157])).
% 2.46/1.32  tff(c_183, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_136, c_171])).
% 2.46/1.32  tff(c_187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_183])).
% 2.46/1.32  tff(c_188, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitRight, [status(thm)], [c_30])).
% 2.46/1.32  tff(c_317, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_316, c_188])).
% 2.46/1.32  tff(c_337, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_336, c_317])).
% 2.46/1.32  tff(c_418, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_412, c_337])).
% 2.46/1.32  tff(c_435, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_418])).
% 2.46/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.32  
% 2.46/1.32  Inference rules
% 2.46/1.32  ----------------------
% 2.46/1.32  #Ref     : 0
% 2.46/1.32  #Sup     : 89
% 2.46/1.32  #Fact    : 0
% 2.46/1.32  #Define  : 0
% 2.46/1.32  #Split   : 3
% 2.46/1.32  #Chain   : 0
% 2.46/1.32  #Close   : 0
% 2.46/1.32  
% 2.46/1.32  Ordering : KBO
% 2.46/1.32  
% 2.46/1.32  Simplification rules
% 2.46/1.32  ----------------------
% 2.46/1.32  #Subsume      : 0
% 2.46/1.32  #Demod        : 56
% 2.46/1.32  #Tautology    : 55
% 2.46/1.32  #SimpNegUnit  : 2
% 2.46/1.32  #BackRed      : 11
% 2.46/1.32  
% 2.46/1.32  #Partial instantiations: 0
% 2.46/1.32  #Strategies tried      : 1
% 2.46/1.32  
% 2.46/1.32  Timing (in seconds)
% 2.46/1.32  ----------------------
% 2.46/1.32  Preprocessing        : 0.32
% 2.46/1.32  Parsing              : 0.17
% 2.46/1.32  CNF conversion       : 0.02
% 2.46/1.32  Main loop            : 0.23
% 2.46/1.32  Inferencing          : 0.10
% 2.46/1.32  Reduction            : 0.07
% 2.46/1.32  Demodulation         : 0.05
% 2.46/1.32  BG Simplification    : 0.02
% 2.46/1.32  Subsumption          : 0.02
% 2.46/1.32  Abstraction          : 0.01
% 2.46/1.32  MUC search           : 0.00
% 2.46/1.32  Cooper               : 0.00
% 2.46/1.32  Total                : 0.59
% 2.46/1.32  Index Insertion      : 0.00
% 2.46/1.32  Index Deletion       : 0.00
% 2.46/1.32  Index Matching       : 0.00
% 2.46/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
