%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:21 EST 2020

% Result     : Theorem 4.21s
% Output     : CNFRefutation 4.54s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 286 expanded)
%              Number of leaves         :   38 ( 115 expanded)
%              Depth                    :   11
%              Number of atoms          :  188 ( 777 expanded)
%              Number of equality atoms :   48 ( 233 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_117,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_98,axiom,(
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

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_123,plain,(
    ! [C_51,A_52,B_53] :
      ( v1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_131,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_123])).

tff(c_161,plain,(
    ! [C_64,B_65,A_66] :
      ( v5_relat_1(C_64,B_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_66,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_171,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_161])).

tff(c_26,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k2_relat_1(B_14),A_13)
      | ~ v5_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_386,plain,(
    ! [A_110,B_111,C_112] :
      ( k2_relset_1(A_110,B_111,C_112) = k2_relat_1(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_396,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_386])).

tff(c_52,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_401,plain,(
    k2_relat_1('#skF_6') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_52])).

tff(c_283,plain,(
    ! [A_95,B_96] :
      ( r2_hidden('#skF_2'(A_95,B_96),B_96)
      | r2_hidden('#skF_3'(A_95,B_96),A_95)
      | B_96 = A_95 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1469,plain,(
    ! [A_238,B_239,B_240] :
      ( r2_hidden('#skF_3'(A_238,B_239),B_240)
      | ~ r1_tarski(A_238,B_240)
      | r2_hidden('#skF_2'(A_238,B_239),B_239)
      | B_239 = A_238 ) ),
    inference(resolution,[status(thm)],[c_283,c_2])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | ~ r2_hidden('#skF_3'(A_6,B_7),B_7)
      | B_7 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1504,plain,(
    ! [A_238,B_240] :
      ( ~ r1_tarski(A_238,B_240)
      | r2_hidden('#skF_2'(A_238,B_240),B_240)
      | B_240 = A_238 ) ),
    inference(resolution,[status(thm)],[c_1469,c_10])).

tff(c_99,plain,(
    ! [A_45,B_46] :
      ( r2_hidden('#skF_1'(A_45,B_46),A_45)
      | r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_108,plain,(
    ! [A_45] : r1_tarski(A_45,A_45) ),
    inference(resolution,[status(thm)],[c_99,c_4])).

tff(c_56,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_375,plain,(
    ! [A_107,B_108,C_109] :
      ( k1_relset_1(A_107,B_108,C_109) = k1_relat_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_385,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_375])).

tff(c_500,plain,(
    ! [B_150,A_151,C_152] :
      ( k1_xboole_0 = B_150
      | k1_relset_1(A_151,B_150,C_152) = A_151
      | ~ v1_funct_2(C_152,A_151,B_150)
      | ~ m1_subset_1(C_152,k1_zfmisc_1(k2_zfmisc_1(A_151,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_503,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_500])).

tff(c_512,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_385,c_503])).

tff(c_514,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_512])).

tff(c_62,plain,(
    ! [D_35] :
      ( r2_hidden('#skF_7'(D_35),'#skF_4')
      | ~ r2_hidden(D_35,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_142,plain,(
    ! [C_56,B_57,A_58] :
      ( r2_hidden(C_56,B_57)
      | ~ r2_hidden(C_56,A_58)
      | ~ r1_tarski(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_148,plain,(
    ! [D_35,B_57] :
      ( r2_hidden('#skF_7'(D_35),B_57)
      | ~ r1_tarski('#skF_4',B_57)
      | ~ r2_hidden(D_35,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_62,c_142])).

tff(c_58,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_60,plain,(
    ! [D_35] :
      ( k1_funct_1('#skF_6','#skF_7'(D_35)) = D_35
      | ~ r2_hidden(D_35,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_436,plain,(
    ! [B_130,A_131] :
      ( r2_hidden(k1_funct_1(B_130,A_131),k2_relat_1(B_130))
      | ~ r2_hidden(A_131,k1_relat_1(B_130))
      | ~ v1_funct_1(B_130)
      | ~ v1_relat_1(B_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_441,plain,(
    ! [D_35] :
      ( r2_hidden(D_35,k2_relat_1('#skF_6'))
      | ~ r2_hidden('#skF_7'(D_35),k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(D_35,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_436])).

tff(c_445,plain,(
    ! [D_132] :
      ( r2_hidden(D_132,k2_relat_1('#skF_6'))
      | ~ r2_hidden('#skF_7'(D_132),k1_relat_1('#skF_6'))
      | ~ r2_hidden(D_132,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_58,c_441])).

tff(c_450,plain,(
    ! [D_35] :
      ( r2_hidden(D_35,k2_relat_1('#skF_6'))
      | ~ r1_tarski('#skF_4',k1_relat_1('#skF_6'))
      | ~ r2_hidden(D_35,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_148,c_445])).

tff(c_451,plain,(
    ~ r1_tarski('#skF_4',k1_relat_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_450])).

tff(c_515,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_451])).

tff(c_520,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_515])).

tff(c_521,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_512])).

tff(c_18,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_551,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_521,c_521,c_18])).

tff(c_616,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_551,c_54])).

tff(c_20,plain,(
    ! [B_10] : k2_zfmisc_1(k1_xboole_0,B_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_170,plain,(
    ! [C_64,B_10] :
      ( v5_relat_1(C_64,B_10)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_161])).

tff(c_700,plain,(
    ! [C_165,B_166] :
      ( v5_relat_1(C_165,B_166)
      | ~ m1_subset_1(C_165,k1_zfmisc_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_521,c_170])).

tff(c_705,plain,(
    ! [B_167] : v5_relat_1('#skF_6',B_167) ),
    inference(resolution,[status(thm)],[c_616,c_700])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_205,plain,(
    ! [A_78,B_79,B_80] :
      ( r2_hidden('#skF_1'(A_78,B_79),B_80)
      | ~ r1_tarski(A_78,B_80)
      | r1_tarski(A_78,B_79) ) ),
    inference(resolution,[status(thm)],[c_6,c_142])).

tff(c_22,plain,(
    ! [A_11,B_12] : ~ r2_hidden(A_11,k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_262,plain,(
    ! [A_90,B_91,B_92] :
      ( ~ r1_tarski(A_90,k2_zfmisc_1('#skF_1'(A_90,B_91),B_92))
      | r1_tarski(A_90,B_91) ) ),
    inference(resolution,[status(thm)],[c_205,c_22])).

tff(c_279,plain,(
    ! [B_14,B_91,B_92] :
      ( r1_tarski(k2_relat_1(B_14),B_91)
      | ~ v5_relat_1(B_14,k2_zfmisc_1('#skF_1'(k2_relat_1(B_14),B_91),B_92))
      | ~ v1_relat_1(B_14) ) ),
    inference(resolution,[status(thm)],[c_26,c_262])).

tff(c_709,plain,(
    ! [B_91] :
      ( r1_tarski(k2_relat_1('#skF_6'),B_91)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_705,c_279])).

tff(c_724,plain,(
    ! [B_170] : r1_tarski(k2_relat_1('#skF_6'),B_170) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_709])).

tff(c_89,plain,(
    ! [A_39,B_40] : ~ r2_hidden(A_39,k2_zfmisc_1(A_39,B_40)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_92,plain,(
    ! [A_9] : ~ r2_hidden(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_89])).

tff(c_298,plain,(
    ! [B_97] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_97),B_97)
      | k1_xboole_0 = B_97 ) ),
    inference(resolution,[status(thm)],[c_283,c_92])).

tff(c_312,plain,(
    ! [B_98,B_99] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_98),B_99)
      | ~ r1_tarski(B_98,B_99)
      | k1_xboole_0 = B_98 ) ),
    inference(resolution,[status(thm)],[c_298,c_2])).

tff(c_328,plain,(
    ! [B_98] :
      ( ~ r1_tarski(B_98,k1_xboole_0)
      | k1_xboole_0 = B_98 ) ),
    inference(resolution,[status(thm)],[c_312,c_92])).

tff(c_537,plain,(
    ! [B_98] :
      ( ~ r1_tarski(B_98,'#skF_5')
      | B_98 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_521,c_521,c_328])).

tff(c_731,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_724,c_537])).

tff(c_746,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_401,c_731])).

tff(c_747,plain,(
    ! [D_35] :
      ( r2_hidden(D_35,k2_relat_1('#skF_6'))
      | ~ r2_hidden(D_35,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_450])).

tff(c_420,plain,(
    ! [A_126,B_127] :
      ( ~ r2_hidden('#skF_2'(A_126,B_127),A_126)
      | r2_hidden('#skF_3'(A_126,B_127),A_126)
      | B_127 = A_126 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1265,plain,(
    ! [A_220,B_221,B_222] :
      ( r2_hidden('#skF_3'(A_220,B_221),B_222)
      | ~ r1_tarski(A_220,B_222)
      | ~ r2_hidden('#skF_2'(A_220,B_221),A_220)
      | B_221 = A_220 ) ),
    inference(resolution,[status(thm)],[c_420,c_2])).

tff(c_1583,plain,(
    ! [B_247,B_248] :
      ( r2_hidden('#skF_3'(k2_relat_1('#skF_6'),B_247),B_248)
      | ~ r1_tarski(k2_relat_1('#skF_6'),B_248)
      | k2_relat_1('#skF_6') = B_247
      | ~ r2_hidden('#skF_2'(k2_relat_1('#skF_6'),B_247),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_747,c_1265])).

tff(c_754,plain,(
    ! [D_171] :
      ( r2_hidden(D_171,k2_relat_1('#skF_6'))
      | ~ r2_hidden(D_171,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_450])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( ~ r2_hidden('#skF_2'(A_6,B_7),A_6)
      | ~ r2_hidden('#skF_3'(A_6,B_7),B_7)
      | B_7 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_769,plain,(
    ! [B_7] :
      ( ~ r2_hidden('#skF_3'(k2_relat_1('#skF_6'),B_7),B_7)
      | k2_relat_1('#skF_6') = B_7
      | ~ r2_hidden('#skF_2'(k2_relat_1('#skF_6'),B_7),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_754,c_8])).

tff(c_2429,plain,(
    ! [B_301] :
      ( ~ r1_tarski(k2_relat_1('#skF_6'),B_301)
      | k2_relat_1('#skF_6') = B_301
      | ~ r2_hidden('#skF_2'(k2_relat_1('#skF_6'),B_301),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1583,c_769])).

tff(c_2445,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
    | k2_relat_1('#skF_6') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1504,c_2429])).

tff(c_2458,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_401,c_401,c_2445])).

tff(c_2464,plain,
    ( ~ v5_relat_1('#skF_6','#skF_5')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_2458])).

tff(c_2471,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_171,c_2464])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:06:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.21/1.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.21/1.73  
% 4.21/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.45/1.74  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 4.45/1.74  
% 4.45/1.74  %Foreground sorts:
% 4.45/1.74  
% 4.45/1.74  
% 4.45/1.74  %Background operators:
% 4.45/1.74  
% 4.45/1.74  
% 4.45/1.74  %Foreground operators:
% 4.45/1.74  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.45/1.74  tff('#skF_7', type, '#skF_7': $i > $i).
% 4.45/1.74  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.45/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.45/1.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.45/1.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.45/1.74  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.45/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.45/1.74  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.45/1.74  tff('#skF_5', type, '#skF_5': $i).
% 4.45/1.74  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.45/1.74  tff('#skF_6', type, '#skF_6': $i).
% 4.45/1.74  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.45/1.74  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.45/1.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.45/1.74  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.45/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.45/1.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.45/1.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.45/1.74  tff('#skF_4', type, '#skF_4': $i).
% 4.45/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.45/1.74  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.45/1.74  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.45/1.74  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.45/1.74  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.45/1.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.45/1.74  
% 4.54/1.75  tff(f_117, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 4.54/1.75  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.54/1.75  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.54/1.75  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 4.54/1.75  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.54/1.75  tff(f_39, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 4.54/1.75  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.54/1.75  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.54/1.75  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.54/1.75  tff(f_62, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_1)).
% 4.54/1.75  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.54/1.75  tff(f_48, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 4.54/1.75  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.54/1.75  tff(c_123, plain, (![C_51, A_52, B_53]: (v1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.54/1.75  tff(c_131, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_123])).
% 4.54/1.75  tff(c_161, plain, (![C_64, B_65, A_66]: (v5_relat_1(C_64, B_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_66, B_65))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.54/1.75  tff(c_171, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_161])).
% 4.54/1.75  tff(c_26, plain, (![B_14, A_13]: (r1_tarski(k2_relat_1(B_14), A_13) | ~v5_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.54/1.75  tff(c_386, plain, (![A_110, B_111, C_112]: (k2_relset_1(A_110, B_111, C_112)=k2_relat_1(C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.54/1.75  tff(c_396, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_386])).
% 4.54/1.75  tff(c_52, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.54/1.75  tff(c_401, plain, (k2_relat_1('#skF_6')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_396, c_52])).
% 4.54/1.75  tff(c_283, plain, (![A_95, B_96]: (r2_hidden('#skF_2'(A_95, B_96), B_96) | r2_hidden('#skF_3'(A_95, B_96), A_95) | B_96=A_95)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.54/1.75  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.54/1.75  tff(c_1469, plain, (![A_238, B_239, B_240]: (r2_hidden('#skF_3'(A_238, B_239), B_240) | ~r1_tarski(A_238, B_240) | r2_hidden('#skF_2'(A_238, B_239), B_239) | B_239=A_238)), inference(resolution, [status(thm)], [c_283, c_2])).
% 4.54/1.75  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | ~r2_hidden('#skF_3'(A_6, B_7), B_7) | B_7=A_6)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.54/1.75  tff(c_1504, plain, (![A_238, B_240]: (~r1_tarski(A_238, B_240) | r2_hidden('#skF_2'(A_238, B_240), B_240) | B_240=A_238)), inference(resolution, [status(thm)], [c_1469, c_10])).
% 4.54/1.75  tff(c_99, plain, (![A_45, B_46]: (r2_hidden('#skF_1'(A_45, B_46), A_45) | r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.54/1.75  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.54/1.75  tff(c_108, plain, (![A_45]: (r1_tarski(A_45, A_45))), inference(resolution, [status(thm)], [c_99, c_4])).
% 4.54/1.75  tff(c_56, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.54/1.75  tff(c_375, plain, (![A_107, B_108, C_109]: (k1_relset_1(A_107, B_108, C_109)=k1_relat_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.54/1.75  tff(c_385, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_375])).
% 4.54/1.75  tff(c_500, plain, (![B_150, A_151, C_152]: (k1_xboole_0=B_150 | k1_relset_1(A_151, B_150, C_152)=A_151 | ~v1_funct_2(C_152, A_151, B_150) | ~m1_subset_1(C_152, k1_zfmisc_1(k2_zfmisc_1(A_151, B_150))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.54/1.75  tff(c_503, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_500])).
% 4.54/1.75  tff(c_512, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_385, c_503])).
% 4.54/1.75  tff(c_514, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_512])).
% 4.54/1.75  tff(c_62, plain, (![D_35]: (r2_hidden('#skF_7'(D_35), '#skF_4') | ~r2_hidden(D_35, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.54/1.75  tff(c_142, plain, (![C_56, B_57, A_58]: (r2_hidden(C_56, B_57) | ~r2_hidden(C_56, A_58) | ~r1_tarski(A_58, B_57))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.54/1.75  tff(c_148, plain, (![D_35, B_57]: (r2_hidden('#skF_7'(D_35), B_57) | ~r1_tarski('#skF_4', B_57) | ~r2_hidden(D_35, '#skF_5'))), inference(resolution, [status(thm)], [c_62, c_142])).
% 4.54/1.75  tff(c_58, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.54/1.75  tff(c_60, plain, (![D_35]: (k1_funct_1('#skF_6', '#skF_7'(D_35))=D_35 | ~r2_hidden(D_35, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.54/1.75  tff(c_436, plain, (![B_130, A_131]: (r2_hidden(k1_funct_1(B_130, A_131), k2_relat_1(B_130)) | ~r2_hidden(A_131, k1_relat_1(B_130)) | ~v1_funct_1(B_130) | ~v1_relat_1(B_130))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.54/1.75  tff(c_441, plain, (![D_35]: (r2_hidden(D_35, k2_relat_1('#skF_6')) | ~r2_hidden('#skF_7'(D_35), k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~r2_hidden(D_35, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_436])).
% 4.54/1.75  tff(c_445, plain, (![D_132]: (r2_hidden(D_132, k2_relat_1('#skF_6')) | ~r2_hidden('#skF_7'(D_132), k1_relat_1('#skF_6')) | ~r2_hidden(D_132, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_58, c_441])).
% 4.54/1.75  tff(c_450, plain, (![D_35]: (r2_hidden(D_35, k2_relat_1('#skF_6')) | ~r1_tarski('#skF_4', k1_relat_1('#skF_6')) | ~r2_hidden(D_35, '#skF_5'))), inference(resolution, [status(thm)], [c_148, c_445])).
% 4.54/1.75  tff(c_451, plain, (~r1_tarski('#skF_4', k1_relat_1('#skF_6'))), inference(splitLeft, [status(thm)], [c_450])).
% 4.54/1.75  tff(c_515, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_514, c_451])).
% 4.54/1.75  tff(c_520, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_108, c_515])).
% 4.54/1.75  tff(c_521, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_512])).
% 4.54/1.75  tff(c_18, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.54/1.75  tff(c_551, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_521, c_521, c_18])).
% 4.54/1.75  tff(c_616, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_551, c_54])).
% 4.54/1.75  tff(c_20, plain, (![B_10]: (k2_zfmisc_1(k1_xboole_0, B_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.54/1.75  tff(c_170, plain, (![C_64, B_10]: (v5_relat_1(C_64, B_10) | ~m1_subset_1(C_64, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_161])).
% 4.54/1.75  tff(c_700, plain, (![C_165, B_166]: (v5_relat_1(C_165, B_166) | ~m1_subset_1(C_165, k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_521, c_170])).
% 4.54/1.75  tff(c_705, plain, (![B_167]: (v5_relat_1('#skF_6', B_167))), inference(resolution, [status(thm)], [c_616, c_700])).
% 4.54/1.75  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.54/1.75  tff(c_205, plain, (![A_78, B_79, B_80]: (r2_hidden('#skF_1'(A_78, B_79), B_80) | ~r1_tarski(A_78, B_80) | r1_tarski(A_78, B_79))), inference(resolution, [status(thm)], [c_6, c_142])).
% 4.54/1.75  tff(c_22, plain, (![A_11, B_12]: (~r2_hidden(A_11, k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.54/1.75  tff(c_262, plain, (![A_90, B_91, B_92]: (~r1_tarski(A_90, k2_zfmisc_1('#skF_1'(A_90, B_91), B_92)) | r1_tarski(A_90, B_91))), inference(resolution, [status(thm)], [c_205, c_22])).
% 4.54/1.75  tff(c_279, plain, (![B_14, B_91, B_92]: (r1_tarski(k2_relat_1(B_14), B_91) | ~v5_relat_1(B_14, k2_zfmisc_1('#skF_1'(k2_relat_1(B_14), B_91), B_92)) | ~v1_relat_1(B_14))), inference(resolution, [status(thm)], [c_26, c_262])).
% 4.54/1.75  tff(c_709, plain, (![B_91]: (r1_tarski(k2_relat_1('#skF_6'), B_91) | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_705, c_279])).
% 4.54/1.75  tff(c_724, plain, (![B_170]: (r1_tarski(k2_relat_1('#skF_6'), B_170))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_709])).
% 4.54/1.75  tff(c_89, plain, (![A_39, B_40]: (~r2_hidden(A_39, k2_zfmisc_1(A_39, B_40)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.54/1.75  tff(c_92, plain, (![A_9]: (~r2_hidden(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_89])).
% 4.54/1.75  tff(c_298, plain, (![B_97]: (r2_hidden('#skF_2'(k1_xboole_0, B_97), B_97) | k1_xboole_0=B_97)), inference(resolution, [status(thm)], [c_283, c_92])).
% 4.54/1.75  tff(c_312, plain, (![B_98, B_99]: (r2_hidden('#skF_2'(k1_xboole_0, B_98), B_99) | ~r1_tarski(B_98, B_99) | k1_xboole_0=B_98)), inference(resolution, [status(thm)], [c_298, c_2])).
% 4.54/1.75  tff(c_328, plain, (![B_98]: (~r1_tarski(B_98, k1_xboole_0) | k1_xboole_0=B_98)), inference(resolution, [status(thm)], [c_312, c_92])).
% 4.54/1.75  tff(c_537, plain, (![B_98]: (~r1_tarski(B_98, '#skF_5') | B_98='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_521, c_521, c_328])).
% 4.54/1.75  tff(c_731, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_724, c_537])).
% 4.54/1.75  tff(c_746, plain, $false, inference(negUnitSimplification, [status(thm)], [c_401, c_731])).
% 4.54/1.75  tff(c_747, plain, (![D_35]: (r2_hidden(D_35, k2_relat_1('#skF_6')) | ~r2_hidden(D_35, '#skF_5'))), inference(splitRight, [status(thm)], [c_450])).
% 4.54/1.75  tff(c_420, plain, (![A_126, B_127]: (~r2_hidden('#skF_2'(A_126, B_127), A_126) | r2_hidden('#skF_3'(A_126, B_127), A_126) | B_127=A_126)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.54/1.75  tff(c_1265, plain, (![A_220, B_221, B_222]: (r2_hidden('#skF_3'(A_220, B_221), B_222) | ~r1_tarski(A_220, B_222) | ~r2_hidden('#skF_2'(A_220, B_221), A_220) | B_221=A_220)), inference(resolution, [status(thm)], [c_420, c_2])).
% 4.54/1.75  tff(c_1583, plain, (![B_247, B_248]: (r2_hidden('#skF_3'(k2_relat_1('#skF_6'), B_247), B_248) | ~r1_tarski(k2_relat_1('#skF_6'), B_248) | k2_relat_1('#skF_6')=B_247 | ~r2_hidden('#skF_2'(k2_relat_1('#skF_6'), B_247), '#skF_5'))), inference(resolution, [status(thm)], [c_747, c_1265])).
% 4.54/1.75  tff(c_754, plain, (![D_171]: (r2_hidden(D_171, k2_relat_1('#skF_6')) | ~r2_hidden(D_171, '#skF_5'))), inference(splitRight, [status(thm)], [c_450])).
% 4.54/1.75  tff(c_8, plain, (![A_6, B_7]: (~r2_hidden('#skF_2'(A_6, B_7), A_6) | ~r2_hidden('#skF_3'(A_6, B_7), B_7) | B_7=A_6)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.54/1.75  tff(c_769, plain, (![B_7]: (~r2_hidden('#skF_3'(k2_relat_1('#skF_6'), B_7), B_7) | k2_relat_1('#skF_6')=B_7 | ~r2_hidden('#skF_2'(k2_relat_1('#skF_6'), B_7), '#skF_5'))), inference(resolution, [status(thm)], [c_754, c_8])).
% 4.54/1.75  tff(c_2429, plain, (![B_301]: (~r1_tarski(k2_relat_1('#skF_6'), B_301) | k2_relat_1('#skF_6')=B_301 | ~r2_hidden('#skF_2'(k2_relat_1('#skF_6'), B_301), '#skF_5'))), inference(resolution, [status(thm)], [c_1583, c_769])).
% 4.54/1.75  tff(c_2445, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | k2_relat_1('#skF_6')='#skF_5'), inference(resolution, [status(thm)], [c_1504, c_2429])).
% 4.54/1.75  tff(c_2458, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_401, c_401, c_2445])).
% 4.54/1.75  tff(c_2464, plain, (~v5_relat_1('#skF_6', '#skF_5') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_26, c_2458])).
% 4.54/1.75  tff(c_2471, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_131, c_171, c_2464])).
% 4.54/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.54/1.75  
% 4.54/1.75  Inference rules
% 4.54/1.75  ----------------------
% 4.54/1.75  #Ref     : 0
% 4.54/1.75  #Sup     : 502
% 4.54/1.75  #Fact    : 0
% 4.54/1.75  #Define  : 0
% 4.54/1.75  #Split   : 11
% 4.54/1.75  #Chain   : 0
% 4.54/1.75  #Close   : 0
% 4.54/1.75  
% 4.54/1.75  Ordering : KBO
% 4.54/1.75  
% 4.54/1.75  Simplification rules
% 4.54/1.75  ----------------------
% 4.54/1.75  #Subsume      : 179
% 4.54/1.75  #Demod        : 209
% 4.54/1.75  #Tautology    : 80
% 4.54/1.75  #SimpNegUnit  : 14
% 4.54/1.75  #BackRed      : 65
% 4.54/1.75  
% 4.54/1.75  #Partial instantiations: 0
% 4.54/1.75  #Strategies tried      : 1
% 4.54/1.75  
% 4.54/1.75  Timing (in seconds)
% 4.54/1.75  ----------------------
% 4.54/1.76  Preprocessing        : 0.32
% 4.54/1.76  Parsing              : 0.16
% 4.54/1.76  CNF conversion       : 0.02
% 4.54/1.76  Main loop            : 0.67
% 4.54/1.76  Inferencing          : 0.25
% 4.54/1.76  Reduction            : 0.19
% 4.54/1.76  Demodulation         : 0.12
% 4.54/1.76  BG Simplification    : 0.03
% 4.54/1.76  Subsumption          : 0.16
% 4.54/1.76  Abstraction          : 0.03
% 4.54/1.76  MUC search           : 0.00
% 4.54/1.76  Cooper               : 0.00
% 4.54/1.76  Total                : 1.03
% 4.54/1.76  Index Insertion      : 0.00
% 4.54/1.76  Index Deletion       : 0.00
% 4.54/1.76  Index Matching       : 0.00
% 4.54/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
