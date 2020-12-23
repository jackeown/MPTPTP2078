%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:36 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 384 expanded)
%              Number of leaves         :   48 ( 158 expanded)
%              Depth                    :   14
%              Number of atoms          :  151 ( 759 expanded)
%              Number of equality atoms :   57 ( 294 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_127,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k1_relat_1(B))
      <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_62,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_115,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_39,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(c_2,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_79,plain,(
    ! [A_79] :
      ( k1_xboole_0 = A_79
      | ~ v1_xboole_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_83,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_79])).

tff(c_84,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_2])).

tff(c_64,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_112,plain,(
    ! [C_83,A_84,B_85] :
      ( v1_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_120,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_112])).

tff(c_68,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_246,plain,(
    ! [A_117,B_118,C_119,D_120] :
      ( k7_relset_1(A_117,B_118,C_119,D_120) = k9_relat_1(C_119,D_120)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_256,plain,(
    ! [D_120] : k7_relset_1(k1_tarski('#skF_5'),'#skF_6','#skF_7',D_120) = k9_relat_1('#skF_7',D_120) ),
    inference(resolution,[status(thm)],[c_64,c_246])).

tff(c_185,plain,(
    ! [A_106,B_107,C_108] :
      ( k2_relset_1(A_106,B_107,C_108) = k2_relat_1(C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_198,plain,(
    k2_relset_1(k1_tarski('#skF_5'),'#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_185])).

tff(c_423,plain,(
    ! [A_139,B_140,C_141] :
      ( k7_relset_1(A_139,B_140,C_141,A_139) = k2_relset_1(A_139,B_140,C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_431,plain,(
    k7_relset_1(k1_tarski('#skF_5'),'#skF_6','#skF_7',k1_tarski('#skF_5')) = k2_relset_1(k1_tarski('#skF_5'),'#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_64,c_423])).

tff(c_438,plain,(
    k9_relat_1('#skF_7',k1_tarski('#skF_5')) = k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_198,c_431])).

tff(c_18,plain,(
    ! [A_13,B_15] :
      ( k9_relat_1(A_13,k1_tarski(B_15)) = k11_relat_1(A_13,B_15)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_487,plain,
    ( k11_relat_1('#skF_7','#skF_5') = k2_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_18])).

tff(c_494,plain,(
    k11_relat_1('#skF_7','#skF_5') = k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_487])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( r2_hidden(A_16,k1_relat_1(B_17))
      | k11_relat_1(B_17,A_16) = k1_xboole_0
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_510,plain,(
    ! [B_148,A_149] :
      ( k1_tarski(k1_funct_1(B_148,A_149)) = k11_relat_1(B_148,A_149)
      | ~ r2_hidden(A_149,k1_relat_1(B_148))
      | ~ v1_funct_1(B_148)
      | ~ v1_relat_1(B_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_548,plain,(
    ! [B_154,A_155] :
      ( k1_tarski(k1_funct_1(B_154,A_155)) = k11_relat_1(B_154,A_155)
      | ~ v1_funct_1(B_154)
      | k11_relat_1(B_154,A_155) = k1_xboole_0
      | ~ v1_relat_1(B_154) ) ),
    inference(resolution,[status(thm)],[c_20,c_510])).

tff(c_60,plain,(
    k2_relset_1(k1_tarski('#skF_5'),'#skF_6','#skF_7') != k1_tarski(k1_funct_1('#skF_7','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_208,plain,(
    k1_tarski(k1_funct_1('#skF_7','#skF_5')) != k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_60])).

tff(c_554,plain,
    ( k11_relat_1('#skF_7','#skF_5') != k2_relat_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | k11_relat_1('#skF_7','#skF_5') = k1_xboole_0
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_548,c_208])).

tff(c_568,plain,(
    k2_relat_1('#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_494,c_68,c_494,c_554])).

tff(c_714,plain,(
    ! [A_164,B_165] :
      ( r2_hidden('#skF_2'(A_164,B_165),k1_relat_1(A_164))
      | r2_hidden('#skF_3'(A_164,B_165),B_165)
      | k2_relat_1(A_164) = B_165
      | ~ v1_funct_1(A_164)
      | ~ v1_relat_1(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_14,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_121,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_112])).

tff(c_257,plain,(
    ! [A_117,B_118,D_120] : k7_relset_1(A_117,B_118,k1_xboole_0,D_120) = k9_relat_1(k1_xboole_0,D_120) ),
    inference(resolution,[status(thm)],[c_14,c_246])).

tff(c_24,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_196,plain,(
    ! [A_106,B_107] : k2_relset_1(A_106,B_107,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_185])).

tff(c_200,plain,(
    ! [A_106,B_107] : k2_relset_1(A_106,B_107,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_196])).

tff(c_434,plain,(
    ! [A_139,B_140] : k7_relset_1(A_139,B_140,k1_xboole_0,A_139) = k2_relset_1(A_139,B_140,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_423])).

tff(c_442,plain,(
    ! [A_142] : k9_relat_1(k1_xboole_0,A_142) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_200,c_434])).

tff(c_448,plain,(
    ! [B_15] :
      ( k11_relat_1(k1_xboole_0,B_15) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_18])).

tff(c_457,plain,(
    ! [B_15] : k11_relat_1(k1_xboole_0,B_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_448])).

tff(c_26,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_140,plain,(
    ! [B_91,A_92] :
      ( k11_relat_1(B_91,A_92) != k1_xboole_0
      | ~ r2_hidden(A_92,k1_relat_1(B_91))
      | ~ v1_relat_1(B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_143,plain,(
    ! [A_92] :
      ( k11_relat_1(k1_xboole_0,A_92) != k1_xboole_0
      | ~ r2_hidden(A_92,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_140])).

tff(c_145,plain,(
    ! [A_92] :
      ( k11_relat_1(k1_xboole_0,A_92) != k1_xboole_0
      | ~ r2_hidden(A_92,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_143])).

tff(c_470,plain,(
    ! [A_92] : ~ r2_hidden(A_92,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_145])).

tff(c_28,plain,(
    ! [A_18,D_57] :
      ( r2_hidden(k1_funct_1(A_18,D_57),k2_relat_1(A_18))
      | ~ r2_hidden(D_57,k1_relat_1(A_18))
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_580,plain,(
    ! [D_57] :
      ( r2_hidden(k1_funct_1('#skF_7',D_57),k1_xboole_0)
      | ~ r2_hidden(D_57,k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_568,c_28])).

tff(c_586,plain,(
    ! [D_57] :
      ( r2_hidden(k1_funct_1('#skF_7',D_57),k1_xboole_0)
      | ~ r2_hidden(D_57,k1_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_68,c_580])).

tff(c_587,plain,(
    ! [D_57] : ~ r2_hidden(D_57,k1_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_470,c_586])).

tff(c_718,plain,(
    ! [B_165] :
      ( r2_hidden('#skF_3'('#skF_7',B_165),B_165)
      | k2_relat_1('#skF_7') = B_165
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_714,c_587])).

tff(c_744,plain,(
    ! [B_165] :
      ( r2_hidden('#skF_3'('#skF_7',B_165),B_165)
      | k1_xboole_0 = B_165 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_68,c_568,c_718])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_66,plain,(
    v1_funct_2('#skF_7',k1_tarski('#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_573,plain,(
    k2_relset_1(k1_tarski('#skF_5'),'#skF_6','#skF_7') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_568,c_198])).

tff(c_1145,plain,(
    ! [D_190,C_191,A_192,B_193] :
      ( r2_hidden(k1_funct_1(D_190,C_191),k2_relset_1(A_192,B_193,D_190))
      | k1_xboole_0 = B_193
      | ~ r2_hidden(C_191,A_192)
      | ~ m1_subset_1(D_190,k1_zfmisc_1(k2_zfmisc_1(A_192,B_193)))
      | ~ v1_funct_2(D_190,A_192,B_193)
      | ~ v1_funct_1(D_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1154,plain,(
    ! [C_191] :
      ( r2_hidden(k1_funct_1('#skF_7',C_191),k1_xboole_0)
      | k1_xboole_0 = '#skF_6'
      | ~ r2_hidden(C_191,k1_tarski('#skF_5'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_5'),'#skF_6')))
      | ~ v1_funct_2('#skF_7',k1_tarski('#skF_5'),'#skF_6')
      | ~ v1_funct_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_573,c_1145])).

tff(c_1162,plain,(
    ! [C_191] :
      ( r2_hidden(k1_funct_1('#skF_7',C_191),k1_xboole_0)
      | k1_xboole_0 = '#skF_6'
      | ~ r2_hidden(C_191,k1_tarski('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_1154])).

tff(c_1167,plain,(
    ! [C_194] : ~ r2_hidden(C_194,k1_tarski('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_470,c_1162])).

tff(c_1190,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_744,c_1167])).

tff(c_12,plain,(
    ! [A_8] : ~ v1_xboole_0(k1_tarski(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1206,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1190,c_12])).

tff(c_1211,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1206])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:02:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.56  
% 3.17/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.56  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 3.17/1.56  
% 3.17/1.56  %Foreground sorts:
% 3.17/1.56  
% 3.17/1.56  
% 3.17/1.56  %Background operators:
% 3.17/1.56  
% 3.17/1.56  
% 3.17/1.56  %Foreground operators:
% 3.17/1.56  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.17/1.56  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 3.17/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.17/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.17/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.17/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.17/1.56  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.17/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.17/1.56  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.17/1.56  tff('#skF_7', type, '#skF_7': $i).
% 3.17/1.56  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.17/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.17/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.17/1.57  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.17/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.17/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.17/1.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.17/1.57  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.17/1.57  tff('#skF_6', type, '#skF_6': $i).
% 3.17/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.17/1.57  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.17/1.57  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.17/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.17/1.57  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.17/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.17/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.17/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.17/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.17/1.57  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.17/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.17/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.17/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.17/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.17/1.57  
% 3.59/1.58  tff(f_26, axiom, v1_xboole_0(o_0_0_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_o_0_0_xboole_0)).
% 3.59/1.58  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.59/1.58  tff(f_127, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 3.59/1.58  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.59/1.58  tff(f_97, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.59/1.58  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.59/1.58  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 3.59/1.58  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 3.59/1.58  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 3.59/1.58  tff(f_85, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_funct_1)).
% 3.59/1.58  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 3.59/1.58  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.59/1.58  tff(f_62, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.59/1.58  tff(f_115, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 3.59/1.58  tff(f_39, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 3.59/1.58  tff(c_2, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.59/1.58  tff(c_79, plain, (![A_79]: (k1_xboole_0=A_79 | ~v1_xboole_0(A_79))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.59/1.58  tff(c_83, plain, (o_0_0_xboole_0=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_79])).
% 3.59/1.58  tff(c_84, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_83, c_2])).
% 3.59/1.58  tff(c_64, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.59/1.58  tff(c_112, plain, (![C_83, A_84, B_85]: (v1_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.59/1.58  tff(c_120, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_64, c_112])).
% 3.59/1.58  tff(c_68, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.59/1.58  tff(c_246, plain, (![A_117, B_118, C_119, D_120]: (k7_relset_1(A_117, B_118, C_119, D_120)=k9_relat_1(C_119, D_120) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.59/1.58  tff(c_256, plain, (![D_120]: (k7_relset_1(k1_tarski('#skF_5'), '#skF_6', '#skF_7', D_120)=k9_relat_1('#skF_7', D_120))), inference(resolution, [status(thm)], [c_64, c_246])).
% 3.59/1.58  tff(c_185, plain, (![A_106, B_107, C_108]: (k2_relset_1(A_106, B_107, C_108)=k2_relat_1(C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.59/1.58  tff(c_198, plain, (k2_relset_1(k1_tarski('#skF_5'), '#skF_6', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_64, c_185])).
% 3.59/1.58  tff(c_423, plain, (![A_139, B_140, C_141]: (k7_relset_1(A_139, B_140, C_141, A_139)=k2_relset_1(A_139, B_140, C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.59/1.58  tff(c_431, plain, (k7_relset_1(k1_tarski('#skF_5'), '#skF_6', '#skF_7', k1_tarski('#skF_5'))=k2_relset_1(k1_tarski('#skF_5'), '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_64, c_423])).
% 3.59/1.58  tff(c_438, plain, (k9_relat_1('#skF_7', k1_tarski('#skF_5'))=k2_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_256, c_198, c_431])).
% 3.59/1.58  tff(c_18, plain, (![A_13, B_15]: (k9_relat_1(A_13, k1_tarski(B_15))=k11_relat_1(A_13, B_15) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.59/1.58  tff(c_487, plain, (k11_relat_1('#skF_7', '#skF_5')=k2_relat_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_438, c_18])).
% 3.59/1.58  tff(c_494, plain, (k11_relat_1('#skF_7', '#skF_5')=k2_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_120, c_487])).
% 3.59/1.58  tff(c_20, plain, (![A_16, B_17]: (r2_hidden(A_16, k1_relat_1(B_17)) | k11_relat_1(B_17, A_16)=k1_xboole_0 | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.59/1.58  tff(c_510, plain, (![B_148, A_149]: (k1_tarski(k1_funct_1(B_148, A_149))=k11_relat_1(B_148, A_149) | ~r2_hidden(A_149, k1_relat_1(B_148)) | ~v1_funct_1(B_148) | ~v1_relat_1(B_148))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.59/1.58  tff(c_548, plain, (![B_154, A_155]: (k1_tarski(k1_funct_1(B_154, A_155))=k11_relat_1(B_154, A_155) | ~v1_funct_1(B_154) | k11_relat_1(B_154, A_155)=k1_xboole_0 | ~v1_relat_1(B_154))), inference(resolution, [status(thm)], [c_20, c_510])).
% 3.59/1.58  tff(c_60, plain, (k2_relset_1(k1_tarski('#skF_5'), '#skF_6', '#skF_7')!=k1_tarski(k1_funct_1('#skF_7', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.59/1.58  tff(c_208, plain, (k1_tarski(k1_funct_1('#skF_7', '#skF_5'))!=k2_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_198, c_60])).
% 3.59/1.58  tff(c_554, plain, (k11_relat_1('#skF_7', '#skF_5')!=k2_relat_1('#skF_7') | ~v1_funct_1('#skF_7') | k11_relat_1('#skF_7', '#skF_5')=k1_xboole_0 | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_548, c_208])).
% 3.59/1.58  tff(c_568, plain, (k2_relat_1('#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_120, c_494, c_68, c_494, c_554])).
% 3.59/1.58  tff(c_714, plain, (![A_164, B_165]: (r2_hidden('#skF_2'(A_164, B_165), k1_relat_1(A_164)) | r2_hidden('#skF_3'(A_164, B_165), B_165) | k2_relat_1(A_164)=B_165 | ~v1_funct_1(A_164) | ~v1_relat_1(A_164))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.59/1.58  tff(c_14, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.59/1.58  tff(c_121, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_112])).
% 3.59/1.58  tff(c_257, plain, (![A_117, B_118, D_120]: (k7_relset_1(A_117, B_118, k1_xboole_0, D_120)=k9_relat_1(k1_xboole_0, D_120))), inference(resolution, [status(thm)], [c_14, c_246])).
% 3.59/1.58  tff(c_24, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.59/1.58  tff(c_196, plain, (![A_106, B_107]: (k2_relset_1(A_106, B_107, k1_xboole_0)=k2_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_185])).
% 3.59/1.58  tff(c_200, plain, (![A_106, B_107]: (k2_relset_1(A_106, B_107, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_196])).
% 3.59/1.58  tff(c_434, plain, (![A_139, B_140]: (k7_relset_1(A_139, B_140, k1_xboole_0, A_139)=k2_relset_1(A_139, B_140, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_423])).
% 3.59/1.58  tff(c_442, plain, (![A_142]: (k9_relat_1(k1_xboole_0, A_142)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_257, c_200, c_434])).
% 3.59/1.58  tff(c_448, plain, (![B_15]: (k11_relat_1(k1_xboole_0, B_15)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_442, c_18])).
% 3.59/1.58  tff(c_457, plain, (![B_15]: (k11_relat_1(k1_xboole_0, B_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_121, c_448])).
% 3.59/1.58  tff(c_26, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.59/1.58  tff(c_140, plain, (![B_91, A_92]: (k11_relat_1(B_91, A_92)!=k1_xboole_0 | ~r2_hidden(A_92, k1_relat_1(B_91)) | ~v1_relat_1(B_91))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.59/1.58  tff(c_143, plain, (![A_92]: (k11_relat_1(k1_xboole_0, A_92)!=k1_xboole_0 | ~r2_hidden(A_92, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_140])).
% 3.59/1.58  tff(c_145, plain, (![A_92]: (k11_relat_1(k1_xboole_0, A_92)!=k1_xboole_0 | ~r2_hidden(A_92, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_143])).
% 3.59/1.58  tff(c_470, plain, (![A_92]: (~r2_hidden(A_92, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_457, c_145])).
% 3.59/1.58  tff(c_28, plain, (![A_18, D_57]: (r2_hidden(k1_funct_1(A_18, D_57), k2_relat_1(A_18)) | ~r2_hidden(D_57, k1_relat_1(A_18)) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.59/1.58  tff(c_580, plain, (![D_57]: (r2_hidden(k1_funct_1('#skF_7', D_57), k1_xboole_0) | ~r2_hidden(D_57, k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_568, c_28])).
% 3.59/1.58  tff(c_586, plain, (![D_57]: (r2_hidden(k1_funct_1('#skF_7', D_57), k1_xboole_0) | ~r2_hidden(D_57, k1_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_68, c_580])).
% 3.59/1.58  tff(c_587, plain, (![D_57]: (~r2_hidden(D_57, k1_relat_1('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_470, c_586])).
% 3.59/1.58  tff(c_718, plain, (![B_165]: (r2_hidden('#skF_3'('#skF_7', B_165), B_165) | k2_relat_1('#skF_7')=B_165 | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_714, c_587])).
% 3.59/1.58  tff(c_744, plain, (![B_165]: (r2_hidden('#skF_3'('#skF_7', B_165), B_165) | k1_xboole_0=B_165)), inference(demodulation, [status(thm), theory('equality')], [c_120, c_68, c_568, c_718])).
% 3.59/1.58  tff(c_62, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.59/1.58  tff(c_66, plain, (v1_funct_2('#skF_7', k1_tarski('#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.59/1.58  tff(c_573, plain, (k2_relset_1(k1_tarski('#skF_5'), '#skF_6', '#skF_7')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_568, c_198])).
% 3.59/1.58  tff(c_1145, plain, (![D_190, C_191, A_192, B_193]: (r2_hidden(k1_funct_1(D_190, C_191), k2_relset_1(A_192, B_193, D_190)) | k1_xboole_0=B_193 | ~r2_hidden(C_191, A_192) | ~m1_subset_1(D_190, k1_zfmisc_1(k2_zfmisc_1(A_192, B_193))) | ~v1_funct_2(D_190, A_192, B_193) | ~v1_funct_1(D_190))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.59/1.58  tff(c_1154, plain, (![C_191]: (r2_hidden(k1_funct_1('#skF_7', C_191), k1_xboole_0) | k1_xboole_0='#skF_6' | ~r2_hidden(C_191, k1_tarski('#skF_5')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_5'), '#skF_6'))) | ~v1_funct_2('#skF_7', k1_tarski('#skF_5'), '#skF_6') | ~v1_funct_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_573, c_1145])).
% 3.59/1.58  tff(c_1162, plain, (![C_191]: (r2_hidden(k1_funct_1('#skF_7', C_191), k1_xboole_0) | k1_xboole_0='#skF_6' | ~r2_hidden(C_191, k1_tarski('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_1154])).
% 3.59/1.58  tff(c_1167, plain, (![C_194]: (~r2_hidden(C_194, k1_tarski('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_62, c_470, c_1162])).
% 3.59/1.58  tff(c_1190, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_744, c_1167])).
% 3.59/1.58  tff(c_12, plain, (![A_8]: (~v1_xboole_0(k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.59/1.58  tff(c_1206, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1190, c_12])).
% 3.59/1.58  tff(c_1211, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_1206])).
% 3.59/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/1.58  
% 3.59/1.58  Inference rules
% 3.59/1.58  ----------------------
% 3.59/1.58  #Ref     : 0
% 3.59/1.58  #Sup     : 245
% 3.59/1.58  #Fact    : 0
% 3.59/1.58  #Define  : 0
% 3.59/1.58  #Split   : 1
% 3.59/1.58  #Chain   : 0
% 3.59/1.58  #Close   : 0
% 3.59/1.58  
% 3.59/1.58  Ordering : KBO
% 3.59/1.58  
% 3.59/1.58  Simplification rules
% 3.59/1.58  ----------------------
% 3.59/1.58  #Subsume      : 37
% 3.59/1.58  #Demod        : 194
% 3.59/1.58  #Tautology    : 140
% 3.59/1.58  #SimpNegUnit  : 18
% 3.59/1.58  #BackRed      : 17
% 3.59/1.58  
% 3.59/1.58  #Partial instantiations: 0
% 3.59/1.58  #Strategies tried      : 1
% 3.59/1.58  
% 3.59/1.58  Timing (in seconds)
% 3.59/1.58  ----------------------
% 3.59/1.59  Preprocessing        : 0.39
% 3.59/1.59  Parsing              : 0.20
% 3.59/1.59  CNF conversion       : 0.03
% 3.59/1.59  Main loop            : 0.42
% 3.59/1.59  Inferencing          : 0.16
% 3.59/1.59  Reduction            : 0.13
% 3.59/1.59  Demodulation         : 0.09
% 3.59/1.59  BG Simplification    : 0.03
% 3.59/1.59  Subsumption          : 0.07
% 3.59/1.59  Abstraction          : 0.02
% 3.59/1.59  MUC search           : 0.00
% 3.59/1.59  Cooper               : 0.00
% 3.59/1.59  Total                : 0.86
% 3.59/1.59  Index Insertion      : 0.00
% 3.59/1.59  Index Deletion       : 0.00
% 3.59/1.59  Index Matching       : 0.00
% 3.59/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
