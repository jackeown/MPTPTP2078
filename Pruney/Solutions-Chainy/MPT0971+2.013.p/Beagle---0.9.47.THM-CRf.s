%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:31 EST 2020

% Result     : Theorem 6.85s
% Output     : CNFRefutation 7.20s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 344 expanded)
%              Number of leaves         :   40 ( 136 expanded)
%              Depth                    :   14
%              Number of atoms          :  174 ( 848 expanded)
%              Number of equality atoms :   53 ( 262 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_140,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
            & ! [E] :
                ~ ( r2_hidden(E,A)
                  & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_67,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e9_44_1__funct_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_124,axiom,(
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

tff(f_85,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_62,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_165,plain,(
    ! [A_67,B_68,C_69] :
      ( k2_relset_1(A_67,B_68,C_69) = k2_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_169,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_165])).

tff(c_60,plain,(
    r2_hidden('#skF_5',k2_relset_1('#skF_3','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_172,plain,(
    r2_hidden('#skF_5',k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_60])).

tff(c_144,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_148,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_144])).

tff(c_194,plain,(
    ! [A_74,B_75,C_76] :
      ( m1_subset_1(k2_relset_1(A_74,B_75,C_76),k1_zfmisc_1(B_75))
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_209,plain,
    ( m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_194])).

tff(c_214,plain,(
    m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_209])).

tff(c_159,plain,(
    ! [C_62,A_63,B_64] :
      ( r2_hidden(C_62,A_63)
      | ~ r2_hidden(C_62,B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_162,plain,(
    ! [A_63] :
      ( r2_hidden('#skF_5',A_63)
      | ~ m1_subset_1(k2_relset_1('#skF_3','#skF_4','#skF_6'),k1_zfmisc_1(A_63)) ) ),
    inference(resolution,[status(thm)],[c_60,c_159])).

tff(c_170,plain,(
    ! [A_63] :
      ( r2_hidden('#skF_5',A_63)
      | ~ m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1(A_63)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_162])).

tff(c_219,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_214,c_170])).

tff(c_26,plain,(
    ! [A_14] : v1_relat_1('#skF_2'(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_22,plain,(
    ! [A_14] : k1_relat_1('#skF_2'(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_117,plain,(
    ! [A_55] :
      ( k2_relat_1(A_55) = k1_xboole_0
      | k1_relat_1(A_55) != k1_xboole_0
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_120,plain,(
    ! [A_14] :
      ( k2_relat_1('#skF_2'(A_14)) = k1_xboole_0
      | k1_relat_1('#skF_2'(A_14)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_117])).

tff(c_129,plain,(
    k2_relat_1('#skF_2'(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_120])).

tff(c_85,plain,(
    ! [A_51] :
      ( k9_relat_1(A_51,k1_relat_1(A_51)) = k2_relat_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_94,plain,(
    ! [A_14] :
      ( k9_relat_1('#skF_2'(A_14),A_14) = k2_relat_1('#skF_2'(A_14))
      | ~ v1_relat_1('#skF_2'(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_85])).

tff(c_98,plain,(
    ! [A_14] : k9_relat_1('#skF_2'(A_14),A_14) = k2_relat_1('#skF_2'(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_94])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_228,plain,(
    ! [A_81,B_82,C_83] :
      ( r2_hidden('#skF_1'(A_81,B_82,C_83),B_82)
      | ~ r2_hidden(A_81,k9_relat_1(C_83,B_82))
      | ~ v1_relat_1(C_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_36,plain,(
    ! [B_26,A_25] :
      ( ~ r1_tarski(B_26,A_25)
      | ~ r2_hidden(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_242,plain,(
    ! [B_87,A_88,C_89] :
      ( ~ r1_tarski(B_87,'#skF_1'(A_88,B_87,C_89))
      | ~ r2_hidden(A_88,k9_relat_1(C_89,B_87))
      | ~ v1_relat_1(C_89) ) ),
    inference(resolution,[status(thm)],[c_228,c_36])).

tff(c_247,plain,(
    ! [A_90,C_91] :
      ( ~ r2_hidden(A_90,k9_relat_1(C_91,k1_xboole_0))
      | ~ v1_relat_1(C_91) ) ),
    inference(resolution,[status(thm)],[c_2,c_242])).

tff(c_255,plain,(
    ! [A_90] :
      ( ~ r2_hidden(A_90,k2_relat_1('#skF_2'(k1_xboole_0)))
      | ~ v1_relat_1('#skF_2'(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_247])).

tff(c_258,plain,(
    ! [A_90] : ~ r2_hidden(A_90,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_129,c_255])).

tff(c_24,plain,(
    ! [A_14] : v1_funct_1('#skF_2'(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_122,plain,(
    ! [A_14] :
      ( k2_relat_1('#skF_2'(A_14)) = k1_xboole_0
      | k1_xboole_0 != A_14 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_120])).

tff(c_265,plain,(
    ! [B_93,A_94] :
      ( r2_hidden(k1_funct_1(B_93,A_94),k2_relat_1(B_93))
      | ~ r2_hidden(A_94,k1_relat_1(B_93))
      | ~ v1_funct_1(B_93)
      | ~ v1_relat_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_273,plain,(
    ! [A_14,A_94] :
      ( r2_hidden(k1_funct_1('#skF_2'(A_14),A_94),k1_xboole_0)
      | ~ r2_hidden(A_94,k1_relat_1('#skF_2'(A_14)))
      | ~ v1_funct_1('#skF_2'(A_14))
      | ~ v1_relat_1('#skF_2'(A_14))
      | k1_xboole_0 != A_14 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_265])).

tff(c_280,plain,(
    ! [A_14,A_94] :
      ( r2_hidden(k1_funct_1('#skF_2'(A_14),A_94),k1_xboole_0)
      | ~ r2_hidden(A_94,A_14)
      | k1_xboole_0 != A_14 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_22,c_273])).

tff(c_285,plain,(
    ! [A_95,A_96] :
      ( ~ r2_hidden(A_95,A_96)
      | k1_xboole_0 != A_96 ) ),
    inference(negUnitSimplification,[status(thm)],[c_258,c_280])).

tff(c_300,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_219,c_285])).

tff(c_64,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_185,plain,(
    ! [A_71,B_72,C_73] :
      ( k1_relset_1(A_71,B_72,C_73) = k1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_189,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_185])).

tff(c_1543,plain,(
    ! [B_166,A_167,C_168] :
      ( k1_xboole_0 = B_166
      | k1_relset_1(A_167,B_166,C_168) = A_167
      | ~ v1_funct_2(C_168,A_167,B_166)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_167,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1550,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_1543])).

tff(c_1554,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_189,c_1550])).

tff(c_1555,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_300,c_1554])).

tff(c_14,plain,(
    ! [A_12] :
      ( k9_relat_1(A_12,k1_relat_1(A_12)) = k2_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1567,plain,
    ( k9_relat_1('#skF_6','#skF_3') = k2_relat_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1555,c_14])).

tff(c_1575,plain,(
    k9_relat_1('#skF_6','#skF_3') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_1567])).

tff(c_12,plain,(
    ! [A_6,B_7,C_8] :
      ( r2_hidden('#skF_1'(A_6,B_7,C_8),k1_relat_1(C_8))
      | ~ r2_hidden(A_6,k9_relat_1(C_8,B_7))
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1564,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_1'(A_6,B_7,'#skF_6'),'#skF_3')
      | ~ r2_hidden(A_6,k9_relat_1('#skF_6',B_7))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1555,c_12])).

tff(c_5054,plain,(
    ! [A_306,B_307] :
      ( r2_hidden('#skF_1'(A_306,B_307,'#skF_6'),'#skF_3')
      | ~ r2_hidden(A_306,k9_relat_1('#skF_6',B_307)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_1564])).

tff(c_58,plain,(
    ! [E_43] :
      ( k1_funct_1('#skF_6',E_43) != '#skF_5'
      | ~ r2_hidden(E_43,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_5142,plain,(
    ! [A_313,B_314] :
      ( k1_funct_1('#skF_6','#skF_1'(A_313,B_314,'#skF_6')) != '#skF_5'
      | ~ r2_hidden(A_313,k9_relat_1('#skF_6',B_314)) ) ),
    inference(resolution,[status(thm)],[c_5054,c_58])).

tff(c_5350,plain,(
    ! [A_318] :
      ( k1_funct_1('#skF_6','#skF_1'(A_318,'#skF_3','#skF_6')) != '#skF_5'
      | ~ r2_hidden(A_318,k2_relat_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1575,c_5142])).

tff(c_5396,plain,(
    k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_3','#skF_6')) != '#skF_5' ),
    inference(resolution,[status(thm)],[c_172,c_5350])).

tff(c_66,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_844,plain,(
    ! [A_136,B_137,C_138] :
      ( r2_hidden(k4_tarski('#skF_1'(A_136,B_137,C_138),A_136),C_138)
      | ~ r2_hidden(A_136,k9_relat_1(C_138,B_137))
      | ~ v1_relat_1(C_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_32,plain,(
    ! [C_24,A_22,B_23] :
      ( k1_funct_1(C_24,A_22) = B_23
      | ~ r2_hidden(k4_tarski(A_22,B_23),C_24)
      | ~ v1_funct_1(C_24)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3245,plain,(
    ! [C_232,A_233,B_234] :
      ( k1_funct_1(C_232,'#skF_1'(A_233,B_234,C_232)) = A_233
      | ~ v1_funct_1(C_232)
      | ~ r2_hidden(A_233,k9_relat_1(C_232,B_234))
      | ~ v1_relat_1(C_232) ) ),
    inference(resolution,[status(thm)],[c_844,c_32])).

tff(c_3252,plain,(
    ! [A_233] :
      ( k1_funct_1('#skF_6','#skF_1'(A_233,'#skF_3','#skF_6')) = A_233
      | ~ v1_funct_1('#skF_6')
      | ~ r2_hidden(A_233,k2_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1575,c_3245])).

tff(c_6618,plain,(
    ! [A_376] :
      ( k1_funct_1('#skF_6','#skF_1'(A_376,'#skF_3','#skF_6')) = A_376
      | ~ r2_hidden(A_376,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_66,c_3252])).

tff(c_6653,plain,(
    k1_funct_1('#skF_6','#skF_1'('#skF_5','#skF_3','#skF_6')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_172,c_6618])).

tff(c_6667,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5396,c_6653])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.30  % Computer   : n014.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.30  % CPULimit   : 60
% 0.11/0.30  % DateTime   : Tue Dec  1 15:40:22 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.16/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.85/2.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.85/2.48  
% 6.85/2.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.85/2.48  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 6.85/2.48  
% 6.85/2.48  %Foreground sorts:
% 6.85/2.48  
% 6.85/2.48  
% 6.85/2.48  %Background operators:
% 6.85/2.48  
% 6.85/2.48  
% 6.85/2.48  %Foreground operators:
% 6.85/2.48  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.85/2.48  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.85/2.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.85/2.48  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.85/2.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.85/2.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.85/2.48  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.85/2.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.85/2.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.85/2.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.85/2.48  tff('#skF_5', type, '#skF_5': $i).
% 6.85/2.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.85/2.48  tff('#skF_6', type, '#skF_6': $i).
% 6.85/2.48  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.85/2.48  tff('#skF_3', type, '#skF_3': $i).
% 6.85/2.48  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.85/2.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.85/2.48  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.85/2.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.85/2.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.85/2.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.85/2.48  tff('#skF_4', type, '#skF_4': $i).
% 6.85/2.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.85/2.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.85/2.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.85/2.48  
% 7.20/2.49  tff(f_140, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_funct_2)).
% 7.20/2.49  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.20/2.49  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.20/2.49  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 7.20/2.49  tff(f_34, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 7.20/2.49  tff(f_67, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e9_44_1__funct_1)).
% 7.20/2.49  tff(f_55, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 7.20/2.49  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 7.20/2.49  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.20/2.49  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 7.20/2.49  tff(f_90, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 7.20/2.49  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 7.20/2.49  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.20/2.49  tff(f_124, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 7.20/2.49  tff(f_85, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 7.20/2.49  tff(c_62, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_140])).
% 7.20/2.49  tff(c_165, plain, (![A_67, B_68, C_69]: (k2_relset_1(A_67, B_68, C_69)=k2_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.20/2.49  tff(c_169, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_62, c_165])).
% 7.20/2.49  tff(c_60, plain, (r2_hidden('#skF_5', k2_relset_1('#skF_3', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 7.20/2.49  tff(c_172, plain, (r2_hidden('#skF_5', k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_60])).
% 7.20/2.49  tff(c_144, plain, (![C_59, A_60, B_61]: (v1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.20/2.49  tff(c_148, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_62, c_144])).
% 7.20/2.49  tff(c_194, plain, (![A_74, B_75, C_76]: (m1_subset_1(k2_relset_1(A_74, B_75, C_76), k1_zfmisc_1(B_75)) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.20/2.49  tff(c_209, plain, (m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_169, c_194])).
% 7.20/2.49  tff(c_214, plain, (m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_209])).
% 7.20/2.49  tff(c_159, plain, (![C_62, A_63, B_64]: (r2_hidden(C_62, A_63) | ~r2_hidden(C_62, B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.20/2.49  tff(c_162, plain, (![A_63]: (r2_hidden('#skF_5', A_63) | ~m1_subset_1(k2_relset_1('#skF_3', '#skF_4', '#skF_6'), k1_zfmisc_1(A_63)))), inference(resolution, [status(thm)], [c_60, c_159])).
% 7.20/2.49  tff(c_170, plain, (![A_63]: (r2_hidden('#skF_5', A_63) | ~m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1(A_63)))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_162])).
% 7.20/2.49  tff(c_219, plain, (r2_hidden('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_214, c_170])).
% 7.20/2.49  tff(c_26, plain, (![A_14]: (v1_relat_1('#skF_2'(A_14)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.20/2.49  tff(c_22, plain, (![A_14]: (k1_relat_1('#skF_2'(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.20/2.49  tff(c_117, plain, (![A_55]: (k2_relat_1(A_55)=k1_xboole_0 | k1_relat_1(A_55)!=k1_xboole_0 | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.20/2.49  tff(c_120, plain, (![A_14]: (k2_relat_1('#skF_2'(A_14))=k1_xboole_0 | k1_relat_1('#skF_2'(A_14))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_117])).
% 7.20/2.49  tff(c_129, plain, (k2_relat_1('#skF_2'(k1_xboole_0))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_22, c_120])).
% 7.20/2.50  tff(c_85, plain, (![A_51]: (k9_relat_1(A_51, k1_relat_1(A_51))=k2_relat_1(A_51) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.20/2.50  tff(c_94, plain, (![A_14]: (k9_relat_1('#skF_2'(A_14), A_14)=k2_relat_1('#skF_2'(A_14)) | ~v1_relat_1('#skF_2'(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_85])).
% 7.20/2.50  tff(c_98, plain, (![A_14]: (k9_relat_1('#skF_2'(A_14), A_14)=k2_relat_1('#skF_2'(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_94])).
% 7.20/2.50  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.20/2.50  tff(c_228, plain, (![A_81, B_82, C_83]: (r2_hidden('#skF_1'(A_81, B_82, C_83), B_82) | ~r2_hidden(A_81, k9_relat_1(C_83, B_82)) | ~v1_relat_1(C_83))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.20/2.50  tff(c_36, plain, (![B_26, A_25]: (~r1_tarski(B_26, A_25) | ~r2_hidden(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.20/2.50  tff(c_242, plain, (![B_87, A_88, C_89]: (~r1_tarski(B_87, '#skF_1'(A_88, B_87, C_89)) | ~r2_hidden(A_88, k9_relat_1(C_89, B_87)) | ~v1_relat_1(C_89))), inference(resolution, [status(thm)], [c_228, c_36])).
% 7.20/2.50  tff(c_247, plain, (![A_90, C_91]: (~r2_hidden(A_90, k9_relat_1(C_91, k1_xboole_0)) | ~v1_relat_1(C_91))), inference(resolution, [status(thm)], [c_2, c_242])).
% 7.20/2.50  tff(c_255, plain, (![A_90]: (~r2_hidden(A_90, k2_relat_1('#skF_2'(k1_xboole_0))) | ~v1_relat_1('#skF_2'(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_98, c_247])).
% 7.20/2.50  tff(c_258, plain, (![A_90]: (~r2_hidden(A_90, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_129, c_255])).
% 7.20/2.50  tff(c_24, plain, (![A_14]: (v1_funct_1('#skF_2'(A_14)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.20/2.50  tff(c_122, plain, (![A_14]: (k2_relat_1('#skF_2'(A_14))=k1_xboole_0 | k1_xboole_0!=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_120])).
% 7.20/2.50  tff(c_265, plain, (![B_93, A_94]: (r2_hidden(k1_funct_1(B_93, A_94), k2_relat_1(B_93)) | ~r2_hidden(A_94, k1_relat_1(B_93)) | ~v1_funct_1(B_93) | ~v1_relat_1(B_93))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.20/2.50  tff(c_273, plain, (![A_14, A_94]: (r2_hidden(k1_funct_1('#skF_2'(A_14), A_94), k1_xboole_0) | ~r2_hidden(A_94, k1_relat_1('#skF_2'(A_14))) | ~v1_funct_1('#skF_2'(A_14)) | ~v1_relat_1('#skF_2'(A_14)) | k1_xboole_0!=A_14)), inference(superposition, [status(thm), theory('equality')], [c_122, c_265])).
% 7.20/2.50  tff(c_280, plain, (![A_14, A_94]: (r2_hidden(k1_funct_1('#skF_2'(A_14), A_94), k1_xboole_0) | ~r2_hidden(A_94, A_14) | k1_xboole_0!=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_22, c_273])).
% 7.20/2.50  tff(c_285, plain, (![A_95, A_96]: (~r2_hidden(A_95, A_96) | k1_xboole_0!=A_96)), inference(negUnitSimplification, [status(thm)], [c_258, c_280])).
% 7.20/2.50  tff(c_300, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_219, c_285])).
% 7.20/2.50  tff(c_64, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_140])).
% 7.20/2.50  tff(c_185, plain, (![A_71, B_72, C_73]: (k1_relset_1(A_71, B_72, C_73)=k1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.20/2.50  tff(c_189, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_62, c_185])).
% 7.20/2.50  tff(c_1543, plain, (![B_166, A_167, C_168]: (k1_xboole_0=B_166 | k1_relset_1(A_167, B_166, C_168)=A_167 | ~v1_funct_2(C_168, A_167, B_166) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_167, B_166))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.20/2.50  tff(c_1550, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_62, c_1543])).
% 7.20/2.50  tff(c_1554, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_189, c_1550])).
% 7.20/2.50  tff(c_1555, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_300, c_1554])).
% 7.20/2.50  tff(c_14, plain, (![A_12]: (k9_relat_1(A_12, k1_relat_1(A_12))=k2_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.20/2.50  tff(c_1567, plain, (k9_relat_1('#skF_6', '#skF_3')=k2_relat_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1555, c_14])).
% 7.20/2.50  tff(c_1575, plain, (k9_relat_1('#skF_6', '#skF_3')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_1567])).
% 7.20/2.50  tff(c_12, plain, (![A_6, B_7, C_8]: (r2_hidden('#skF_1'(A_6, B_7, C_8), k1_relat_1(C_8)) | ~r2_hidden(A_6, k9_relat_1(C_8, B_7)) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.20/2.50  tff(c_1564, plain, (![A_6, B_7]: (r2_hidden('#skF_1'(A_6, B_7, '#skF_6'), '#skF_3') | ~r2_hidden(A_6, k9_relat_1('#skF_6', B_7)) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1555, c_12])).
% 7.20/2.50  tff(c_5054, plain, (![A_306, B_307]: (r2_hidden('#skF_1'(A_306, B_307, '#skF_6'), '#skF_3') | ~r2_hidden(A_306, k9_relat_1('#skF_6', B_307)))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_1564])).
% 7.20/2.50  tff(c_58, plain, (![E_43]: (k1_funct_1('#skF_6', E_43)!='#skF_5' | ~r2_hidden(E_43, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_140])).
% 7.20/2.50  tff(c_5142, plain, (![A_313, B_314]: (k1_funct_1('#skF_6', '#skF_1'(A_313, B_314, '#skF_6'))!='#skF_5' | ~r2_hidden(A_313, k9_relat_1('#skF_6', B_314)))), inference(resolution, [status(thm)], [c_5054, c_58])).
% 7.20/2.50  tff(c_5350, plain, (![A_318]: (k1_funct_1('#skF_6', '#skF_1'(A_318, '#skF_3', '#skF_6'))!='#skF_5' | ~r2_hidden(A_318, k2_relat_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_1575, c_5142])).
% 7.20/2.50  tff(c_5396, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_5', '#skF_3', '#skF_6'))!='#skF_5'), inference(resolution, [status(thm)], [c_172, c_5350])).
% 7.20/2.50  tff(c_66, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_140])).
% 7.20/2.50  tff(c_844, plain, (![A_136, B_137, C_138]: (r2_hidden(k4_tarski('#skF_1'(A_136, B_137, C_138), A_136), C_138) | ~r2_hidden(A_136, k9_relat_1(C_138, B_137)) | ~v1_relat_1(C_138))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.20/2.50  tff(c_32, plain, (![C_24, A_22, B_23]: (k1_funct_1(C_24, A_22)=B_23 | ~r2_hidden(k4_tarski(A_22, B_23), C_24) | ~v1_funct_1(C_24) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.20/2.50  tff(c_3245, plain, (![C_232, A_233, B_234]: (k1_funct_1(C_232, '#skF_1'(A_233, B_234, C_232))=A_233 | ~v1_funct_1(C_232) | ~r2_hidden(A_233, k9_relat_1(C_232, B_234)) | ~v1_relat_1(C_232))), inference(resolution, [status(thm)], [c_844, c_32])).
% 7.20/2.50  tff(c_3252, plain, (![A_233]: (k1_funct_1('#skF_6', '#skF_1'(A_233, '#skF_3', '#skF_6'))=A_233 | ~v1_funct_1('#skF_6') | ~r2_hidden(A_233, k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1575, c_3245])).
% 7.20/2.50  tff(c_6618, plain, (![A_376]: (k1_funct_1('#skF_6', '#skF_1'(A_376, '#skF_3', '#skF_6'))=A_376 | ~r2_hidden(A_376, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_66, c_3252])).
% 7.20/2.50  tff(c_6653, plain, (k1_funct_1('#skF_6', '#skF_1'('#skF_5', '#skF_3', '#skF_6'))='#skF_5'), inference(resolution, [status(thm)], [c_172, c_6618])).
% 7.20/2.50  tff(c_6667, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5396, c_6653])).
% 7.20/2.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.20/2.50  
% 7.20/2.50  Inference rules
% 7.20/2.50  ----------------------
% 7.20/2.50  #Ref     : 0
% 7.20/2.50  #Sup     : 1531
% 7.20/2.50  #Fact    : 0
% 7.20/2.50  #Define  : 0
% 7.20/2.50  #Split   : 9
% 7.20/2.50  #Chain   : 0
% 7.20/2.50  #Close   : 0
% 7.20/2.50  
% 7.20/2.50  Ordering : KBO
% 7.20/2.50  
% 7.20/2.50  Simplification rules
% 7.20/2.50  ----------------------
% 7.20/2.50  #Subsume      : 605
% 7.20/2.50  #Demod        : 608
% 7.20/2.50  #Tautology    : 66
% 7.20/2.50  #SimpNegUnit  : 64
% 7.20/2.50  #BackRed      : 7
% 7.20/2.50  
% 7.20/2.50  #Partial instantiations: 0
% 7.20/2.50  #Strategies tried      : 1
% 7.20/2.50  
% 7.20/2.50  Timing (in seconds)
% 7.20/2.50  ----------------------
% 7.20/2.50  Preprocessing        : 0.34
% 7.20/2.50  Parsing              : 0.18
% 7.20/2.50  CNF conversion       : 0.02
% 7.20/2.50  Main loop            : 1.41
% 7.20/2.50  Inferencing          : 0.38
% 7.20/2.50  Reduction            : 0.49
% 7.20/2.50  Demodulation         : 0.32
% 7.20/2.50  BG Simplification    : 0.04
% 7.20/2.50  Subsumption          : 0.37
% 7.20/2.50  Abstraction          : 0.06
% 7.20/2.50  MUC search           : 0.00
% 7.20/2.50  Cooper               : 0.00
% 7.20/2.50  Total                : 1.78
% 7.20/2.50  Index Insertion      : 0.00
% 7.20/2.50  Index Deletion       : 0.00
% 7.20/2.50  Index Matching       : 0.00
% 7.20/2.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
