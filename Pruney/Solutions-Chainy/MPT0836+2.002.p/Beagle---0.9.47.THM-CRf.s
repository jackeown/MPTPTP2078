%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:03 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 255 expanded)
%              Number of leaves         :   41 ( 103 expanded)
%              Depth                    :   10
%              Number of atoms          :  184 ( 601 expanded)
%              Number of equality atoms :   29 (  68 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k1_relset_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_108,negated_conjecture,(
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

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_45,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(c_48,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_282,plain,(
    ! [A_134,B_135,C_136] :
      ( k1_relset_1(A_134,B_135,C_136) = k1_relat_1(C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_286,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_282])).

tff(c_64,plain,
    ( r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8'))
    | m1_subset_1('#skF_10','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_90,plain,(
    m1_subset_1('#skF_10','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_60,plain,
    ( r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8'))
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_166,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_10,plain,(
    ! [C_20,A_5,D_23] :
      ( r2_hidden(C_20,k1_relat_1(A_5))
      | ~ r2_hidden(k4_tarski(C_20,D_23),A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_173,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_166,c_10])).

tff(c_180,plain,(
    ! [A_119,B_120,C_121] :
      ( k1_relset_1(A_119,B_120,C_121) = k1_relat_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_184,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_180])).

tff(c_54,plain,(
    ! [E_87] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_87),'#skF_8')
      | ~ m1_subset_1(E_87,'#skF_7')
      | ~ r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8')) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_268,plain,(
    ! [E_133] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_133),'#skF_8')
      | ~ m1_subset_1(E_133,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_184,c_54])).

tff(c_271,plain,(
    ~ m1_subset_1('#skF_10','#skF_7') ),
    inference(resolution,[status(thm)],[c_166,c_268])).

tff(c_275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_271])).

tff(c_276,plain,(
    r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_288,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_276])).

tff(c_85,plain,(
    ! [C_93,A_94,B_95] :
      ( v1_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_89,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_85])).

tff(c_91,plain,(
    ! [C_96,B_97,A_98] :
      ( v5_relat_1(C_96,B_97)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_98,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_95,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_48,c_91])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k2_relat_1(B_4),A_3)
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_125,plain,(
    ! [B_113,A_114] :
      ( k5_relat_1(B_113,k6_relat_1(A_114)) = B_113
      | ~ r1_tarski(k2_relat_1(B_113),A_114)
      | ~ v1_relat_1(B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_132,plain,(
    ! [B_4,A_3] :
      ( k5_relat_1(B_4,k6_relat_1(A_3)) = B_4
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(resolution,[status(thm)],[c_6,c_125])).

tff(c_20,plain,(
    ! [A_24] : v1_relat_1(k6_relat_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_32,plain,(
    ! [A_34] : k1_relat_1(k6_relat_1(A_34)) = A_34 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_293,plain,(
    ! [A_137,B_138] :
      ( k10_relat_1(A_137,k1_relat_1(B_138)) = k1_relat_1(k5_relat_1(A_137,B_138))
      | ~ v1_relat_1(B_138)
      | ~ v1_relat_1(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_302,plain,(
    ! [A_137,A_34] :
      ( k1_relat_1(k5_relat_1(A_137,k6_relat_1(A_34))) = k10_relat_1(A_137,A_34)
      | ~ v1_relat_1(k6_relat_1(A_34))
      | ~ v1_relat_1(A_137) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_293])).

tff(c_312,plain,(
    ! [A_139,A_140] :
      ( k1_relat_1(k5_relat_1(A_139,k6_relat_1(A_140))) = k10_relat_1(A_139,A_140)
      | ~ v1_relat_1(A_139) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_302])).

tff(c_355,plain,(
    ! [B_144,A_145] :
      ( k10_relat_1(B_144,A_145) = k1_relat_1(B_144)
      | ~ v1_relat_1(B_144)
      | ~ v5_relat_1(B_144,A_145)
      | ~ v1_relat_1(B_144) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_312])).

tff(c_361,plain,
    ( k10_relat_1('#skF_8','#skF_7') = k1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_95,c_355])).

tff(c_367,plain,(
    k10_relat_1('#skF_8','#skF_7') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_361])).

tff(c_438,plain,(
    ! [A_152,B_153,C_154] :
      ( r2_hidden('#skF_5'(A_152,B_153,C_154),B_153)
      | ~ r2_hidden(A_152,k10_relat_1(C_154,B_153))
      | ~ v1_relat_1(C_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_446,plain,(
    ! [A_157,B_158,C_159] :
      ( m1_subset_1('#skF_5'(A_157,B_158,C_159),B_158)
      | ~ r2_hidden(A_157,k10_relat_1(C_159,B_158))
      | ~ v1_relat_1(C_159) ) ),
    inference(resolution,[status(thm)],[c_438,c_2])).

tff(c_457,plain,(
    ! [A_157] :
      ( m1_subset_1('#skF_5'(A_157,'#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_157,k1_relat_1('#skF_8'))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_446])).

tff(c_469,plain,(
    ! [A_160] :
      ( m1_subset_1('#skF_5'(A_160,'#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_160,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_457])).

tff(c_488,plain,(
    m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_288,c_469])).

tff(c_628,plain,(
    ! [A_187,B_188,C_189] :
      ( r2_hidden(k4_tarski(A_187,'#skF_5'(A_187,B_188,C_189)),C_189)
      | ~ r2_hidden(A_187,k10_relat_1(C_189,B_188))
      | ~ v1_relat_1(C_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_277,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_58,plain,(
    ! [E_87] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_87),'#skF_8')
      | ~ m1_subset_1(E_87,'#skF_7')
      | r2_hidden(k4_tarski('#skF_9','#skF_10'),'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_332,plain,(
    ! [E_87] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_87),'#skF_8')
      | ~ m1_subset_1(E_87,'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_277,c_58])).

tff(c_642,plain,(
    ! [B_188] :
      ( ~ m1_subset_1('#skF_5'('#skF_9',B_188,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_188))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_628,c_332])).

tff(c_696,plain,(
    ! [B_193] :
      ( ~ m1_subset_1('#skF_5'('#skF_9',B_193,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_193)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_642])).

tff(c_699,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_367,c_696])).

tff(c_706,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_488,c_699])).

tff(c_708,plain,(
    ~ m1_subset_1('#skF_10','#skF_7') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_845,plain,(
    ! [A_224,B_225,C_226] :
      ( k1_relset_1(A_224,B_225,C_226) = k1_relat_1(C_226)
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k2_zfmisc_1(A_224,B_225))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_849,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_845])).

tff(c_707,plain,(
    r2_hidden('#skF_9',k1_relset_1('#skF_6','#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_851,plain,(
    r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_849,c_707])).

tff(c_729,plain,(
    ! [C_205,B_206,A_207] :
      ( v5_relat_1(C_205,B_206)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_207,B_206))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_733,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_48,c_729])).

tff(c_749,plain,(
    ! [B_212,A_213] :
      ( k5_relat_1(B_212,k6_relat_1(A_213)) = B_212
      | ~ r1_tarski(k2_relat_1(B_212),A_213)
      | ~ v1_relat_1(B_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_756,plain,(
    ! [B_4,A_3] :
      ( k5_relat_1(B_4,k6_relat_1(A_3)) = B_4
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(resolution,[status(thm)],[c_6,c_749])).

tff(c_759,plain,(
    ! [A_214,B_215] :
      ( k10_relat_1(A_214,k1_relat_1(B_215)) = k1_relat_1(k5_relat_1(A_214,B_215))
      | ~ v1_relat_1(B_215)
      | ~ v1_relat_1(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_768,plain,(
    ! [A_214,A_34] :
      ( k1_relat_1(k5_relat_1(A_214,k6_relat_1(A_34))) = k10_relat_1(A_214,A_34)
      | ~ v1_relat_1(k6_relat_1(A_34))
      | ~ v1_relat_1(A_214) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_759])).

tff(c_804,plain,(
    ! [A_220,A_221] :
      ( k1_relat_1(k5_relat_1(A_220,k6_relat_1(A_221))) = k10_relat_1(A_220,A_221)
      | ~ v1_relat_1(A_220) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_768])).

tff(c_866,plain,(
    ! [B_229,A_230] :
      ( k10_relat_1(B_229,A_230) = k1_relat_1(B_229)
      | ~ v1_relat_1(B_229)
      | ~ v5_relat_1(B_229,A_230)
      | ~ v1_relat_1(B_229) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_756,c_804])).

tff(c_872,plain,
    ( k10_relat_1('#skF_8','#skF_7') = k1_relat_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_733,c_866])).

tff(c_878,plain,(
    k10_relat_1('#skF_8','#skF_7') = k1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_872])).

tff(c_920,plain,(
    ! [A_233,B_234,C_235] :
      ( r2_hidden('#skF_5'(A_233,B_234,C_235),B_234)
      | ~ r2_hidden(A_233,k10_relat_1(C_235,B_234))
      | ~ v1_relat_1(C_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_962,plain,(
    ! [A_243,B_244,C_245] :
      ( m1_subset_1('#skF_5'(A_243,B_244,C_245),B_244)
      | ~ r2_hidden(A_243,k10_relat_1(C_245,B_244))
      | ~ v1_relat_1(C_245) ) ),
    inference(resolution,[status(thm)],[c_920,c_2])).

tff(c_970,plain,(
    ! [A_243] :
      ( m1_subset_1('#skF_5'(A_243,'#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_243,k1_relat_1('#skF_8'))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_878,c_962])).

tff(c_985,plain,(
    ! [A_246] :
      ( m1_subset_1('#skF_5'(A_246,'#skF_7','#skF_8'),'#skF_7')
      | ~ r2_hidden(A_246,k1_relat_1('#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_970])).

tff(c_1004,plain,(
    m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_851,c_985])).

tff(c_1136,plain,(
    ! [A_275,B_276,C_277] :
      ( r2_hidden(k4_tarski(A_275,'#skF_5'(A_275,B_276,C_277)),C_277)
      | ~ r2_hidden(A_275,k10_relat_1(C_277,B_276))
      | ~ v1_relat_1(C_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_62,plain,(
    ! [E_87] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_87),'#skF_8')
      | ~ m1_subset_1(E_87,'#skF_7')
      | m1_subset_1('#skF_10','#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_709,plain,(
    ! [E_87] :
      ( ~ r2_hidden(k4_tarski('#skF_9',E_87),'#skF_8')
      | ~ m1_subset_1(E_87,'#skF_7') ) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_1153,plain,(
    ! [B_276] :
      ( ~ m1_subset_1('#skF_5'('#skF_9',B_276,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_276))
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1136,c_709])).

tff(c_1204,plain,(
    ! [B_281] :
      ( ~ m1_subset_1('#skF_5'('#skF_9',B_281,'#skF_8'),'#skF_7')
      | ~ r2_hidden('#skF_9',k10_relat_1('#skF_8',B_281)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_1153])).

tff(c_1207,plain,
    ( ~ m1_subset_1('#skF_5'('#skF_9','#skF_7','#skF_8'),'#skF_7')
    | ~ r2_hidden('#skF_9',k1_relat_1('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_878,c_1204])).

tff(c_1214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_851,c_1004,c_1207])).

tff(c_1215,plain,(
    m1_subset_1('#skF_10','#skF_7') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_1216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_708,c_1215])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:11:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.58  
% 3.32/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.58  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k1_relset_1 > k5_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_4 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1
% 3.32/1.58  
% 3.32/1.58  %Foreground sorts:
% 3.32/1.58  
% 3.32/1.58  
% 3.32/1.58  %Background operators:
% 3.32/1.58  
% 3.32/1.58  
% 3.32/1.58  %Foreground operators:
% 3.32/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.32/1.58  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.32/1.58  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.32/1.58  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.32/1.58  tff('#skF_7', type, '#skF_7': $i).
% 3.32/1.58  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.32/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.32/1.58  tff('#skF_10', type, '#skF_10': $i).
% 3.32/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.32/1.58  tff('#skF_6', type, '#skF_6': $i).
% 3.32/1.58  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.32/1.58  tff('#skF_9', type, '#skF_9': $i).
% 3.32/1.58  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.32/1.58  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.32/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.32/1.58  tff('#skF_8', type, '#skF_8': $i).
% 3.32/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.58  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.32/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.32/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.32/1.58  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.32/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.58  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.32/1.58  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.32/1.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.32/1.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.32/1.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.32/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.32/1.58  
% 3.32/1.60  tff(f_108, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (![D]: (m1_subset_1(D, A) => (r2_hidden(D, k1_relset_1(A, B, C)) <=> (?[E]: (m1_subset_1(E, B) & r2_hidden(k4_tarski(D, E), C)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relset_1)).
% 3.32/1.60  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.32/1.60  tff(f_43, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 3.32/1.60  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.32/1.60  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.32/1.60  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.32/1.60  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 3.32/1.60  tff(f_45, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.32/1.60  tff(f_67, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.32/1.60  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 3.32/1.60  tff(f_56, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 3.32/1.60  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.32/1.60  tff(c_48, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.32/1.60  tff(c_282, plain, (![A_134, B_135, C_136]: (k1_relset_1(A_134, B_135, C_136)=k1_relat_1(C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.32/1.60  tff(c_286, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_48, c_282])).
% 3.32/1.60  tff(c_64, plain, (r2_hidden('#skF_9', k1_relset_1('#skF_6', '#skF_7', '#skF_8')) | m1_subset_1('#skF_10', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.32/1.60  tff(c_90, plain, (m1_subset_1('#skF_10', '#skF_7')), inference(splitLeft, [status(thm)], [c_64])).
% 3.32/1.60  tff(c_60, plain, (r2_hidden('#skF_9', k1_relset_1('#skF_6', '#skF_7', '#skF_8')) | r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.32/1.60  tff(c_166, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8')), inference(splitLeft, [status(thm)], [c_60])).
% 3.32/1.60  tff(c_10, plain, (![C_20, A_5, D_23]: (r2_hidden(C_20, k1_relat_1(A_5)) | ~r2_hidden(k4_tarski(C_20, D_23), A_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.32/1.60  tff(c_173, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_166, c_10])).
% 3.32/1.60  tff(c_180, plain, (![A_119, B_120, C_121]: (k1_relset_1(A_119, B_120, C_121)=k1_relat_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.32/1.60  tff(c_184, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_48, c_180])).
% 3.32/1.60  tff(c_54, plain, (![E_87]: (~r2_hidden(k4_tarski('#skF_9', E_87), '#skF_8') | ~m1_subset_1(E_87, '#skF_7') | ~r2_hidden('#skF_9', k1_relset_1('#skF_6', '#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.32/1.60  tff(c_268, plain, (![E_133]: (~r2_hidden(k4_tarski('#skF_9', E_133), '#skF_8') | ~m1_subset_1(E_133, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_173, c_184, c_54])).
% 3.32/1.60  tff(c_271, plain, (~m1_subset_1('#skF_10', '#skF_7')), inference(resolution, [status(thm)], [c_166, c_268])).
% 3.32/1.60  tff(c_275, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_90, c_271])).
% 3.32/1.60  tff(c_276, plain, (r2_hidden('#skF_9', k1_relset_1('#skF_6', '#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_60])).
% 3.32/1.60  tff(c_288, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_286, c_276])).
% 3.32/1.60  tff(c_85, plain, (![C_93, A_94, B_95]: (v1_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.32/1.60  tff(c_89, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_48, c_85])).
% 3.32/1.60  tff(c_91, plain, (![C_96, B_97, A_98]: (v5_relat_1(C_96, B_97) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_98, B_97))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.32/1.60  tff(c_95, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_48, c_91])).
% 3.32/1.60  tff(c_6, plain, (![B_4, A_3]: (r1_tarski(k2_relat_1(B_4), A_3) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.32/1.60  tff(c_125, plain, (![B_113, A_114]: (k5_relat_1(B_113, k6_relat_1(A_114))=B_113 | ~r1_tarski(k2_relat_1(B_113), A_114) | ~v1_relat_1(B_113))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.32/1.60  tff(c_132, plain, (![B_4, A_3]: (k5_relat_1(B_4, k6_relat_1(A_3))=B_4 | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(resolution, [status(thm)], [c_6, c_125])).
% 3.32/1.60  tff(c_20, plain, (![A_24]: (v1_relat_1(k6_relat_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.32/1.60  tff(c_32, plain, (![A_34]: (k1_relat_1(k6_relat_1(A_34))=A_34)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.32/1.60  tff(c_293, plain, (![A_137, B_138]: (k10_relat_1(A_137, k1_relat_1(B_138))=k1_relat_1(k5_relat_1(A_137, B_138)) | ~v1_relat_1(B_138) | ~v1_relat_1(A_137))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.32/1.60  tff(c_302, plain, (![A_137, A_34]: (k1_relat_1(k5_relat_1(A_137, k6_relat_1(A_34)))=k10_relat_1(A_137, A_34) | ~v1_relat_1(k6_relat_1(A_34)) | ~v1_relat_1(A_137))), inference(superposition, [status(thm), theory('equality')], [c_32, c_293])).
% 3.32/1.60  tff(c_312, plain, (![A_139, A_140]: (k1_relat_1(k5_relat_1(A_139, k6_relat_1(A_140)))=k10_relat_1(A_139, A_140) | ~v1_relat_1(A_139))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_302])).
% 3.32/1.60  tff(c_355, plain, (![B_144, A_145]: (k10_relat_1(B_144, A_145)=k1_relat_1(B_144) | ~v1_relat_1(B_144) | ~v5_relat_1(B_144, A_145) | ~v1_relat_1(B_144))), inference(superposition, [status(thm), theory('equality')], [c_132, c_312])).
% 3.32/1.60  tff(c_361, plain, (k10_relat_1('#skF_8', '#skF_7')=k1_relat_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_95, c_355])).
% 3.32/1.60  tff(c_367, plain, (k10_relat_1('#skF_8', '#skF_7')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_361])).
% 3.32/1.60  tff(c_438, plain, (![A_152, B_153, C_154]: (r2_hidden('#skF_5'(A_152, B_153, C_154), B_153) | ~r2_hidden(A_152, k10_relat_1(C_154, B_153)) | ~v1_relat_1(C_154))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.32/1.60  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.32/1.60  tff(c_446, plain, (![A_157, B_158, C_159]: (m1_subset_1('#skF_5'(A_157, B_158, C_159), B_158) | ~r2_hidden(A_157, k10_relat_1(C_159, B_158)) | ~v1_relat_1(C_159))), inference(resolution, [status(thm)], [c_438, c_2])).
% 3.32/1.60  tff(c_457, plain, (![A_157]: (m1_subset_1('#skF_5'(A_157, '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_157, k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_367, c_446])).
% 3.32/1.60  tff(c_469, plain, (![A_160]: (m1_subset_1('#skF_5'(A_160, '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_160, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_457])).
% 3.32/1.60  tff(c_488, plain, (m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_288, c_469])).
% 3.32/1.60  tff(c_628, plain, (![A_187, B_188, C_189]: (r2_hidden(k4_tarski(A_187, '#skF_5'(A_187, B_188, C_189)), C_189) | ~r2_hidden(A_187, k10_relat_1(C_189, B_188)) | ~v1_relat_1(C_189))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.32/1.60  tff(c_277, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8')), inference(splitRight, [status(thm)], [c_60])).
% 3.32/1.60  tff(c_58, plain, (![E_87]: (~r2_hidden(k4_tarski('#skF_9', E_87), '#skF_8') | ~m1_subset_1(E_87, '#skF_7') | r2_hidden(k4_tarski('#skF_9', '#skF_10'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.32/1.60  tff(c_332, plain, (![E_87]: (~r2_hidden(k4_tarski('#skF_9', E_87), '#skF_8') | ~m1_subset_1(E_87, '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_277, c_58])).
% 3.32/1.60  tff(c_642, plain, (![B_188]: (~m1_subset_1('#skF_5'('#skF_9', B_188, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_188)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_628, c_332])).
% 3.32/1.60  tff(c_696, plain, (![B_193]: (~m1_subset_1('#skF_5'('#skF_9', B_193, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_193)))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_642])).
% 3.32/1.60  tff(c_699, plain, (~m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_367, c_696])).
% 3.32/1.60  tff(c_706, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_288, c_488, c_699])).
% 3.32/1.60  tff(c_708, plain, (~m1_subset_1('#skF_10', '#skF_7')), inference(splitRight, [status(thm)], [c_64])).
% 3.32/1.60  tff(c_845, plain, (![A_224, B_225, C_226]: (k1_relset_1(A_224, B_225, C_226)=k1_relat_1(C_226) | ~m1_subset_1(C_226, k1_zfmisc_1(k2_zfmisc_1(A_224, B_225))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.32/1.60  tff(c_849, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_48, c_845])).
% 3.32/1.60  tff(c_707, plain, (r2_hidden('#skF_9', k1_relset_1('#skF_6', '#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_64])).
% 3.32/1.60  tff(c_851, plain, (r2_hidden('#skF_9', k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_849, c_707])).
% 3.32/1.60  tff(c_729, plain, (![C_205, B_206, A_207]: (v5_relat_1(C_205, B_206) | ~m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_207, B_206))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.32/1.60  tff(c_733, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_48, c_729])).
% 3.32/1.60  tff(c_749, plain, (![B_212, A_213]: (k5_relat_1(B_212, k6_relat_1(A_213))=B_212 | ~r1_tarski(k2_relat_1(B_212), A_213) | ~v1_relat_1(B_212))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.32/1.60  tff(c_756, plain, (![B_4, A_3]: (k5_relat_1(B_4, k6_relat_1(A_3))=B_4 | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(resolution, [status(thm)], [c_6, c_749])).
% 3.32/1.60  tff(c_759, plain, (![A_214, B_215]: (k10_relat_1(A_214, k1_relat_1(B_215))=k1_relat_1(k5_relat_1(A_214, B_215)) | ~v1_relat_1(B_215) | ~v1_relat_1(A_214))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.32/1.60  tff(c_768, plain, (![A_214, A_34]: (k1_relat_1(k5_relat_1(A_214, k6_relat_1(A_34)))=k10_relat_1(A_214, A_34) | ~v1_relat_1(k6_relat_1(A_34)) | ~v1_relat_1(A_214))), inference(superposition, [status(thm), theory('equality')], [c_32, c_759])).
% 3.32/1.60  tff(c_804, plain, (![A_220, A_221]: (k1_relat_1(k5_relat_1(A_220, k6_relat_1(A_221)))=k10_relat_1(A_220, A_221) | ~v1_relat_1(A_220))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_768])).
% 3.32/1.60  tff(c_866, plain, (![B_229, A_230]: (k10_relat_1(B_229, A_230)=k1_relat_1(B_229) | ~v1_relat_1(B_229) | ~v5_relat_1(B_229, A_230) | ~v1_relat_1(B_229))), inference(superposition, [status(thm), theory('equality')], [c_756, c_804])).
% 3.32/1.60  tff(c_872, plain, (k10_relat_1('#skF_8', '#skF_7')=k1_relat_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_733, c_866])).
% 3.32/1.60  tff(c_878, plain, (k10_relat_1('#skF_8', '#skF_7')=k1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_872])).
% 3.32/1.60  tff(c_920, plain, (![A_233, B_234, C_235]: (r2_hidden('#skF_5'(A_233, B_234, C_235), B_234) | ~r2_hidden(A_233, k10_relat_1(C_235, B_234)) | ~v1_relat_1(C_235))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.32/1.60  tff(c_962, plain, (![A_243, B_244, C_245]: (m1_subset_1('#skF_5'(A_243, B_244, C_245), B_244) | ~r2_hidden(A_243, k10_relat_1(C_245, B_244)) | ~v1_relat_1(C_245))), inference(resolution, [status(thm)], [c_920, c_2])).
% 3.32/1.60  tff(c_970, plain, (![A_243]: (m1_subset_1('#skF_5'(A_243, '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_243, k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_878, c_962])).
% 3.32/1.60  tff(c_985, plain, (![A_246]: (m1_subset_1('#skF_5'(A_246, '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden(A_246, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_970])).
% 3.32/1.60  tff(c_1004, plain, (m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_851, c_985])).
% 3.32/1.60  tff(c_1136, plain, (![A_275, B_276, C_277]: (r2_hidden(k4_tarski(A_275, '#skF_5'(A_275, B_276, C_277)), C_277) | ~r2_hidden(A_275, k10_relat_1(C_277, B_276)) | ~v1_relat_1(C_277))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.32/1.60  tff(c_62, plain, (![E_87]: (~r2_hidden(k4_tarski('#skF_9', E_87), '#skF_8') | ~m1_subset_1(E_87, '#skF_7') | m1_subset_1('#skF_10', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.32/1.60  tff(c_709, plain, (![E_87]: (~r2_hidden(k4_tarski('#skF_9', E_87), '#skF_8') | ~m1_subset_1(E_87, '#skF_7'))), inference(splitLeft, [status(thm)], [c_62])).
% 3.32/1.60  tff(c_1153, plain, (![B_276]: (~m1_subset_1('#skF_5'('#skF_9', B_276, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_276)) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_1136, c_709])).
% 3.32/1.60  tff(c_1204, plain, (![B_281]: (~m1_subset_1('#skF_5'('#skF_9', B_281, '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k10_relat_1('#skF_8', B_281)))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_1153])).
% 3.32/1.60  tff(c_1207, plain, (~m1_subset_1('#skF_5'('#skF_9', '#skF_7', '#skF_8'), '#skF_7') | ~r2_hidden('#skF_9', k1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_878, c_1204])).
% 3.32/1.60  tff(c_1214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_851, c_1004, c_1207])).
% 3.32/1.60  tff(c_1215, plain, (m1_subset_1('#skF_10', '#skF_7')), inference(splitRight, [status(thm)], [c_62])).
% 3.32/1.60  tff(c_1216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_708, c_1215])).
% 3.32/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.60  
% 3.32/1.60  Inference rules
% 3.32/1.60  ----------------------
% 3.32/1.60  #Ref     : 0
% 3.32/1.60  #Sup     : 239
% 3.32/1.60  #Fact    : 0
% 3.32/1.60  #Define  : 0
% 3.32/1.60  #Split   : 3
% 3.32/1.60  #Chain   : 0
% 3.32/1.60  #Close   : 0
% 3.32/1.60  
% 3.32/1.60  Ordering : KBO
% 3.32/1.60  
% 3.32/1.60  Simplification rules
% 3.32/1.60  ----------------------
% 3.32/1.60  #Subsume      : 16
% 3.32/1.60  #Demod        : 106
% 3.32/1.60  #Tautology    : 72
% 3.32/1.60  #SimpNegUnit  : 2
% 3.32/1.60  #BackRed      : 4
% 3.32/1.60  
% 3.32/1.60  #Partial instantiations: 0
% 3.32/1.60  #Strategies tried      : 1
% 3.32/1.60  
% 3.32/1.60  Timing (in seconds)
% 3.32/1.60  ----------------------
% 3.32/1.61  Preprocessing        : 0.35
% 3.32/1.61  Parsing              : 0.18
% 3.32/1.61  CNF conversion       : 0.03
% 3.32/1.61  Main loop            : 0.44
% 3.32/1.61  Inferencing          : 0.18
% 3.32/1.61  Reduction            : 0.13
% 3.32/1.61  Demodulation         : 0.09
% 3.32/1.61  BG Simplification    : 0.02
% 3.32/1.61  Subsumption          : 0.07
% 3.32/1.61  Abstraction          : 0.03
% 3.32/1.61  MUC search           : 0.00
% 3.32/1.61  Cooper               : 0.00
% 3.32/1.61  Total                : 0.83
% 3.32/1.61  Index Insertion      : 0.00
% 3.32/1.61  Index Deletion       : 0.00
% 3.32/1.61  Index Matching       : 0.00
% 3.32/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
