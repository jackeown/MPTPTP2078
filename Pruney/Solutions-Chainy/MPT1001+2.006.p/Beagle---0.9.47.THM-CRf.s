%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:56 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 312 expanded)
%              Number of leaves         :   37 ( 118 expanded)
%              Depth                    :   11
%              Number of atoms          :  167 ( 681 expanded)
%              Number of equality atoms :   47 ( 190 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_107,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & k8_relset_1(A,B,C,k1_tarski(D)) = k1_xboole_0 )
        <=> k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_funct_2)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( ! [C] :
            ~ ( r2_hidden(C,A)
              & k10_relat_1(B,k1_tarski(C)) = k1_xboole_0 )
       => r1_tarski(A,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_funct_1)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1157,plain,(
    ! [A_190,B_191] :
      ( r2_hidden('#skF_1'(A_190,B_191),B_191)
      | ~ r2_hidden(A_190,B_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(k1_tarski(A_4),B_5)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1068,plain,(
    ! [B_178,A_179] :
      ( B_178 = A_179
      | ~ r1_tarski(B_178,A_179)
      | ~ r1_tarski(A_179,B_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1084,plain,(
    ! [A_180] :
      ( k1_xboole_0 = A_180
      | ~ r1_tarski(A_180,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_1068])).

tff(c_1097,plain,(
    ! [A_4] :
      ( k1_tarski(A_4) = k1_xboole_0
      | ~ r2_hidden(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_1084])).

tff(c_1181,plain,(
    ! [A_197] :
      ( k1_tarski('#skF_1'(A_197,k1_xboole_0)) = k1_xboole_0
      | ~ r2_hidden(A_197,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1157,c_1097])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | ~ r1_tarski(k1_tarski(A_4),B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1193,plain,(
    ! [A_197,B_5] :
      ( r2_hidden('#skF_1'(A_197,k1_xboole_0),B_5)
      | ~ r1_tarski(k1_xboole_0,B_5)
      | ~ r2_hidden(A_197,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1181,c_10])).

tff(c_1200,plain,(
    ! [A_197,B_5] :
      ( r2_hidden('#skF_1'(A_197,k1_xboole_0),B_5)
      | ~ r2_hidden(A_197,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1193])).

tff(c_1270,plain,(
    ! [D_206,A_207,B_208] :
      ( ~ r2_hidden(D_206,'#skF_1'(A_207,B_208))
      | ~ r2_hidden(D_206,B_208)
      | ~ r2_hidden(A_207,B_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1287,plain,(
    ! [A_209,B_210,A_211] :
      ( ~ r2_hidden('#skF_1'(A_209,k1_xboole_0),B_210)
      | ~ r2_hidden(A_211,B_210)
      | ~ r2_hidden(A_209,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1200,c_1270])).

tff(c_1296,plain,(
    ! [A_211,B_5,A_197] :
      ( ~ r2_hidden(A_211,B_5)
      | ~ r2_hidden(A_197,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1200,c_1287])).

tff(c_1299,plain,(
    ! [A_197] : ~ r2_hidden(A_197,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1296])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_750,plain,(
    ! [A_137,B_138,C_139] :
      ( k2_relset_1(A_137,B_138,C_139) = k2_relat_1(C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_759,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_750])).

tff(c_48,plain,
    ( k2_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_4'
    | r2_hidden('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_71,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_760,plain,(
    k2_relat_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_759,c_71])).

tff(c_831,plain,(
    ! [A_154,B_155,C_156] :
      ( m1_subset_1(k2_relset_1(A_154,B_155,C_156),k1_zfmisc_1(B_155))
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_851,plain,
    ( m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_759,c_831])).

tff(c_856,plain,(
    m1_subset_1(k2_relat_1('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_851])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_860,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_856,c_18])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_862,plain,
    ( k2_relat_1('#skF_5') = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_860,c_2])).

tff(c_865,plain,(
    ~ r1_tarski('#skF_4',k2_relat_1('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_760,c_862])).

tff(c_123,plain,(
    ! [C_55,A_56,B_57] :
      ( v1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_132,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_123])).

tff(c_26,plain,(
    ! [A_16,B_17] :
      ( r2_hidden('#skF_2'(A_16,B_17),A_16)
      | r1_tarski(A_16,k2_relat_1(B_17))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    ! [B_17,A_16] :
      ( k10_relat_1(B_17,k1_tarski('#skF_2'(A_16,B_17))) = k1_xboole_0
      | r1_tarski(A_16,k2_relat_1(B_17))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_976,plain,(
    ! [A_166,B_167,C_168,D_169] :
      ( k8_relset_1(A_166,B_167,C_168,D_169) = k10_relat_1(C_168,D_169)
      | ~ m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(A_166,B_167))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_991,plain,(
    ! [D_169] : k8_relset_1('#skF_3','#skF_4','#skF_5',D_169) = k10_relat_1('#skF_5',D_169) ),
    inference(resolution,[status(thm)],[c_38,c_976])).

tff(c_54,plain,(
    ! [D_36] :
      ( k8_relset_1('#skF_3','#skF_4','#skF_5',k1_tarski(D_36)) != k1_xboole_0
      | ~ r2_hidden(D_36,'#skF_4')
      | k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_720,plain,(
    ! [D_36] :
      ( k8_relset_1('#skF_3','#skF_4','#skF_5',k1_tarski(D_36)) != k1_xboole_0
      | ~ r2_hidden(D_36,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_54])).

tff(c_1004,plain,(
    ! [D_171] :
      ( k10_relat_1('#skF_5',k1_tarski(D_171)) != k1_xboole_0
      | ~ r2_hidden(D_171,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_991,c_720])).

tff(c_1008,plain,(
    ! [A_16] :
      ( ~ r2_hidden('#skF_2'(A_16,'#skF_5'),'#skF_4')
      | r1_tarski(A_16,k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1004])).

tff(c_1042,plain,(
    ! [A_173] :
      ( ~ r2_hidden('#skF_2'(A_173,'#skF_5'),'#skF_4')
      | r1_tarski(A_173,k2_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_1008])).

tff(c_1046,plain,
    ( r1_tarski('#skF_4',k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_1042])).

tff(c_1049,plain,(
    r1_tarski('#skF_4',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_1046])).

tff(c_1051,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_865,c_1049])).

tff(c_1052,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1103,plain,(
    ! [C_182,A_183,B_184] :
      ( v1_relat_1(C_182)
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(A_183,B_184))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1112,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_1103])).

tff(c_22,plain,(
    ! [A_15] :
      ( k10_relat_1(A_15,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1122,plain,(
    k10_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1112,c_22])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1053,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_1312,plain,(
    ! [A_213,B_214,C_215] :
      ( k2_relset_1(A_213,B_214,C_215) = k2_relat_1(C_215)
      | ~ m1_subset_1(C_215,k1_zfmisc_1(k2_zfmisc_1(A_213,B_214))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1319,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_1312])).

tff(c_1322,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1053,c_1319])).

tff(c_1420,plain,(
    ! [B_233,A_234] :
      ( k9_relat_1(B_233,k10_relat_1(B_233,A_234)) = A_234
      | ~ r1_tarski(A_234,k2_relat_1(B_233))
      | ~ v1_funct_1(B_233)
      | ~ v1_relat_1(B_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1422,plain,(
    ! [A_234] :
      ( k9_relat_1('#skF_5',k10_relat_1('#skF_5',A_234)) = A_234
      | ~ r1_tarski(A_234,'#skF_4')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1322,c_1420])).

tff(c_1442,plain,(
    ! [A_235] :
      ( k9_relat_1('#skF_5',k10_relat_1('#skF_5',A_235)) = A_235
      | ~ r1_tarski(A_235,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1112,c_42,c_1422])).

tff(c_1455,plain,
    ( k9_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1122,c_1442])).

tff(c_1461,plain,(
    k9_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1455])).

tff(c_1519,plain,(
    ! [A_242,B_243,C_244,D_245] :
      ( k8_relset_1(A_242,B_243,C_244,D_245) = k10_relat_1(C_244,D_245)
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(A_242,B_243))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1584,plain,(
    ! [D_248] : k8_relset_1('#skF_3','#skF_4','#skF_5',D_248) = k10_relat_1('#skF_5',D_248) ),
    inference(resolution,[status(thm)],[c_38,c_1519])).

tff(c_44,plain,
    ( k2_relset_1('#skF_3','#skF_4','#skF_5') != '#skF_4'
    | k8_relset_1('#skF_3','#skF_4','#skF_5',k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1114,plain,(
    k8_relset_1('#skF_3','#skF_4','#skF_5',k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1053,c_44])).

tff(c_1590,plain,(
    k10_relat_1('#skF_5',k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1584,c_1114])).

tff(c_1433,plain,(
    ! [A_234] :
      ( k9_relat_1('#skF_5',k10_relat_1('#skF_5',A_234)) = A_234
      | ~ r1_tarski(A_234,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1112,c_42,c_1422])).

tff(c_1638,plain,
    ( k9_relat_1('#skF_5',k1_xboole_0) = k1_tarski('#skF_6')
    | ~ r1_tarski(k1_tarski('#skF_6'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1590,c_1433])).

tff(c_1641,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | ~ r1_tarski(k1_tarski('#skF_6'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1461,c_1638])).

tff(c_1705,plain,(
    ~ r1_tarski(k1_tarski('#skF_6'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1641])).

tff(c_1708,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_1705])).

tff(c_1712,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1052,c_1708])).

tff(c_1713,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1641])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_59,plain,(
    ! [A_40,B_41] :
      ( r2_hidden(A_40,B_41)
      | ~ r1_tarski(k1_tarski(A_40),B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_64,plain,(
    ! [A_40] : r2_hidden(A_40,k1_tarski(A_40)) ),
    inference(resolution,[status(thm)],[c_6,c_59])).

tff(c_1729,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1713,c_64])).

tff(c_1739,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1299,c_1729])).

tff(c_1740,plain,(
    ! [A_211,B_5] : ~ r2_hidden(A_211,B_5) ),
    inference(splitRight,[status(thm)],[c_1296])).

tff(c_1747,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1740,c_1052])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:54:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.39/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.58  
% 3.39/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.58  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.39/1.58  
% 3.39/1.58  %Foreground sorts:
% 3.39/1.58  
% 3.39/1.58  
% 3.39/1.58  %Background operators:
% 3.39/1.58  
% 3.39/1.58  
% 3.39/1.58  %Foreground operators:
% 3.39/1.58  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.39/1.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.39/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.39/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.39/1.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.39/1.58  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.39/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.39/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.39/1.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.39/1.58  tff('#skF_5', type, '#skF_5': $i).
% 3.39/1.58  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.39/1.58  tff('#skF_6', type, '#skF_6': $i).
% 3.39/1.58  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.39/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.39/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.39/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.39/1.58  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.39/1.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.39/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.39/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.39/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.39/1.58  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.39/1.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.39/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.39/1.58  
% 3.39/1.60  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.39/1.60  tff(f_50, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 3.39/1.60  tff(f_37, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 3.39/1.60  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.39/1.60  tff(f_107, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (k8_relset_1(A, B, C, k1_tarski(D)) = k1_xboole_0))) <=> (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_funct_2)).
% 3.39/1.60  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.39/1.60  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.39/1.60  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.39/1.60  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.39/1.60  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => ((![C]: ~(r2_hidden(C, A) & (k10_relat_1(B, k1_tarski(C)) = k1_xboole_0))) => r1_tarski(A, k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_funct_1)).
% 3.39/1.60  tff(f_92, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.39/1.60  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t171_relat_1)).
% 3.39/1.60  tff(f_76, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 3.39/1.60  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.39/1.60  tff(c_1157, plain, (![A_190, B_191]: (r2_hidden('#skF_1'(A_190, B_191), B_191) | ~r2_hidden(A_190, B_191))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.39/1.60  tff(c_12, plain, (![A_4, B_5]: (r1_tarski(k1_tarski(A_4), B_5) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.39/1.60  tff(c_1068, plain, (![B_178, A_179]: (B_178=A_179 | ~r1_tarski(B_178, A_179) | ~r1_tarski(A_179, B_178))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.39/1.60  tff(c_1084, plain, (![A_180]: (k1_xboole_0=A_180 | ~r1_tarski(A_180, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_1068])).
% 3.39/1.60  tff(c_1097, plain, (![A_4]: (k1_tarski(A_4)=k1_xboole_0 | ~r2_hidden(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_1084])).
% 3.39/1.60  tff(c_1181, plain, (![A_197]: (k1_tarski('#skF_1'(A_197, k1_xboole_0))=k1_xboole_0 | ~r2_hidden(A_197, k1_xboole_0))), inference(resolution, [status(thm)], [c_1157, c_1097])).
% 3.39/1.60  tff(c_10, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | ~r1_tarski(k1_tarski(A_4), B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.39/1.60  tff(c_1193, plain, (![A_197, B_5]: (r2_hidden('#skF_1'(A_197, k1_xboole_0), B_5) | ~r1_tarski(k1_xboole_0, B_5) | ~r2_hidden(A_197, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1181, c_10])).
% 3.39/1.60  tff(c_1200, plain, (![A_197, B_5]: (r2_hidden('#skF_1'(A_197, k1_xboole_0), B_5) | ~r2_hidden(A_197, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1193])).
% 3.39/1.60  tff(c_1270, plain, (![D_206, A_207, B_208]: (~r2_hidden(D_206, '#skF_1'(A_207, B_208)) | ~r2_hidden(D_206, B_208) | ~r2_hidden(A_207, B_208))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.39/1.60  tff(c_1287, plain, (![A_209, B_210, A_211]: (~r2_hidden('#skF_1'(A_209, k1_xboole_0), B_210) | ~r2_hidden(A_211, B_210) | ~r2_hidden(A_209, k1_xboole_0))), inference(resolution, [status(thm)], [c_1200, c_1270])).
% 3.39/1.60  tff(c_1296, plain, (![A_211, B_5, A_197]: (~r2_hidden(A_211, B_5) | ~r2_hidden(A_197, k1_xboole_0))), inference(resolution, [status(thm)], [c_1200, c_1287])).
% 3.39/1.60  tff(c_1299, plain, (![A_197]: (~r2_hidden(A_197, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_1296])).
% 3.39/1.60  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.39/1.60  tff(c_750, plain, (![A_137, B_138, C_139]: (k2_relset_1(A_137, B_138, C_139)=k2_relat_1(C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.39/1.60  tff(c_759, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_750])).
% 3.39/1.60  tff(c_48, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_4' | r2_hidden('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.39/1.60  tff(c_71, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_4'), inference(splitLeft, [status(thm)], [c_48])).
% 3.39/1.60  tff(c_760, plain, (k2_relat_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_759, c_71])).
% 3.39/1.60  tff(c_831, plain, (![A_154, B_155, C_156]: (m1_subset_1(k2_relset_1(A_154, B_155, C_156), k1_zfmisc_1(B_155)) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.39/1.60  tff(c_851, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_759, c_831])).
% 3.39/1.60  tff(c_856, plain, (m1_subset_1(k2_relat_1('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_851])).
% 3.39/1.60  tff(c_18, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.39/1.60  tff(c_860, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_856, c_18])).
% 3.39/1.60  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.39/1.60  tff(c_862, plain, (k2_relat_1('#skF_5')='#skF_4' | ~r1_tarski('#skF_4', k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_860, c_2])).
% 3.39/1.60  tff(c_865, plain, (~r1_tarski('#skF_4', k2_relat_1('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_760, c_862])).
% 3.39/1.60  tff(c_123, plain, (![C_55, A_56, B_57]: (v1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.39/1.60  tff(c_132, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_123])).
% 3.39/1.60  tff(c_26, plain, (![A_16, B_17]: (r2_hidden('#skF_2'(A_16, B_17), A_16) | r1_tarski(A_16, k2_relat_1(B_17)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.39/1.60  tff(c_24, plain, (![B_17, A_16]: (k10_relat_1(B_17, k1_tarski('#skF_2'(A_16, B_17)))=k1_xboole_0 | r1_tarski(A_16, k2_relat_1(B_17)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.39/1.60  tff(c_976, plain, (![A_166, B_167, C_168, D_169]: (k8_relset_1(A_166, B_167, C_168, D_169)=k10_relat_1(C_168, D_169) | ~m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(A_166, B_167))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.39/1.60  tff(c_991, plain, (![D_169]: (k8_relset_1('#skF_3', '#skF_4', '#skF_5', D_169)=k10_relat_1('#skF_5', D_169))), inference(resolution, [status(thm)], [c_38, c_976])).
% 3.39/1.60  tff(c_54, plain, (![D_36]: (k8_relset_1('#skF_3', '#skF_4', '#skF_5', k1_tarski(D_36))!=k1_xboole_0 | ~r2_hidden(D_36, '#skF_4') | k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.39/1.60  tff(c_720, plain, (![D_36]: (k8_relset_1('#skF_3', '#skF_4', '#skF_5', k1_tarski(D_36))!=k1_xboole_0 | ~r2_hidden(D_36, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_71, c_54])).
% 3.39/1.60  tff(c_1004, plain, (![D_171]: (k10_relat_1('#skF_5', k1_tarski(D_171))!=k1_xboole_0 | ~r2_hidden(D_171, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_991, c_720])).
% 3.39/1.60  tff(c_1008, plain, (![A_16]: (~r2_hidden('#skF_2'(A_16, '#skF_5'), '#skF_4') | r1_tarski(A_16, k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1004])).
% 3.39/1.60  tff(c_1042, plain, (![A_173]: (~r2_hidden('#skF_2'(A_173, '#skF_5'), '#skF_4') | r1_tarski(A_173, k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_1008])).
% 3.39/1.60  tff(c_1046, plain, (r1_tarski('#skF_4', k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_26, c_1042])).
% 3.39/1.60  tff(c_1049, plain, (r1_tarski('#skF_4', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_1046])).
% 3.39/1.60  tff(c_1051, plain, $false, inference(negUnitSimplification, [status(thm)], [c_865, c_1049])).
% 3.39/1.60  tff(c_1052, plain, (r2_hidden('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_48])).
% 3.39/1.60  tff(c_1103, plain, (![C_182, A_183, B_184]: (v1_relat_1(C_182) | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(A_183, B_184))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.39/1.60  tff(c_1112, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_1103])).
% 3.39/1.60  tff(c_22, plain, (![A_15]: (k10_relat_1(A_15, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.39/1.60  tff(c_1122, plain, (k10_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_1112, c_22])).
% 3.39/1.60  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.39/1.60  tff(c_1053, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_48])).
% 3.39/1.60  tff(c_1312, plain, (![A_213, B_214, C_215]: (k2_relset_1(A_213, B_214, C_215)=k2_relat_1(C_215) | ~m1_subset_1(C_215, k1_zfmisc_1(k2_zfmisc_1(A_213, B_214))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.39/1.60  tff(c_1319, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_1312])).
% 3.39/1.60  tff(c_1322, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1053, c_1319])).
% 3.39/1.60  tff(c_1420, plain, (![B_233, A_234]: (k9_relat_1(B_233, k10_relat_1(B_233, A_234))=A_234 | ~r1_tarski(A_234, k2_relat_1(B_233)) | ~v1_funct_1(B_233) | ~v1_relat_1(B_233))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.39/1.60  tff(c_1422, plain, (![A_234]: (k9_relat_1('#skF_5', k10_relat_1('#skF_5', A_234))=A_234 | ~r1_tarski(A_234, '#skF_4') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1322, c_1420])).
% 3.39/1.60  tff(c_1442, plain, (![A_235]: (k9_relat_1('#skF_5', k10_relat_1('#skF_5', A_235))=A_235 | ~r1_tarski(A_235, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1112, c_42, c_1422])).
% 3.39/1.60  tff(c_1455, plain, (k9_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1122, c_1442])).
% 3.39/1.60  tff(c_1461, plain, (k9_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1455])).
% 3.39/1.60  tff(c_1519, plain, (![A_242, B_243, C_244, D_245]: (k8_relset_1(A_242, B_243, C_244, D_245)=k10_relat_1(C_244, D_245) | ~m1_subset_1(C_244, k1_zfmisc_1(k2_zfmisc_1(A_242, B_243))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.39/1.60  tff(c_1584, plain, (![D_248]: (k8_relset_1('#skF_3', '#skF_4', '#skF_5', D_248)=k10_relat_1('#skF_5', D_248))), inference(resolution, [status(thm)], [c_38, c_1519])).
% 3.39/1.60  tff(c_44, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')!='#skF_4' | k8_relset_1('#skF_3', '#skF_4', '#skF_5', k1_tarski('#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.39/1.60  tff(c_1114, plain, (k8_relset_1('#skF_3', '#skF_4', '#skF_5', k1_tarski('#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1053, c_44])).
% 3.39/1.60  tff(c_1590, plain, (k10_relat_1('#skF_5', k1_tarski('#skF_6'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1584, c_1114])).
% 3.39/1.60  tff(c_1433, plain, (![A_234]: (k9_relat_1('#skF_5', k10_relat_1('#skF_5', A_234))=A_234 | ~r1_tarski(A_234, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1112, c_42, c_1422])).
% 3.39/1.60  tff(c_1638, plain, (k9_relat_1('#skF_5', k1_xboole_0)=k1_tarski('#skF_6') | ~r1_tarski(k1_tarski('#skF_6'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1590, c_1433])).
% 3.39/1.60  tff(c_1641, plain, (k1_tarski('#skF_6')=k1_xboole_0 | ~r1_tarski(k1_tarski('#skF_6'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1461, c_1638])).
% 3.39/1.60  tff(c_1705, plain, (~r1_tarski(k1_tarski('#skF_6'), '#skF_4')), inference(splitLeft, [status(thm)], [c_1641])).
% 3.39/1.60  tff(c_1708, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_12, c_1705])).
% 3.39/1.60  tff(c_1712, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1052, c_1708])).
% 3.39/1.60  tff(c_1713, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1641])).
% 3.39/1.60  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.39/1.60  tff(c_59, plain, (![A_40, B_41]: (r2_hidden(A_40, B_41) | ~r1_tarski(k1_tarski(A_40), B_41))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.39/1.60  tff(c_64, plain, (![A_40]: (r2_hidden(A_40, k1_tarski(A_40)))), inference(resolution, [status(thm)], [c_6, c_59])).
% 3.39/1.60  tff(c_1729, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1713, c_64])).
% 3.39/1.60  tff(c_1739, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1299, c_1729])).
% 3.39/1.60  tff(c_1740, plain, (![A_211, B_5]: (~r2_hidden(A_211, B_5))), inference(splitRight, [status(thm)], [c_1296])).
% 3.39/1.60  tff(c_1747, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1740, c_1052])).
% 3.39/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.60  
% 3.39/1.60  Inference rules
% 3.39/1.60  ----------------------
% 3.39/1.60  #Ref     : 0
% 3.39/1.60  #Sup     : 355
% 3.39/1.60  #Fact    : 0
% 3.39/1.60  #Define  : 0
% 3.39/1.60  #Split   : 12
% 3.39/1.60  #Chain   : 0
% 3.39/1.60  #Close   : 0
% 3.39/1.60  
% 3.39/1.60  Ordering : KBO
% 3.39/1.60  
% 3.39/1.60  Simplification rules
% 3.39/1.60  ----------------------
% 3.39/1.60  #Subsume      : 59
% 3.39/1.60  #Demod        : 169
% 3.39/1.60  #Tautology    : 170
% 3.39/1.60  #SimpNegUnit  : 13
% 3.39/1.60  #BackRed      : 22
% 3.39/1.60  
% 3.39/1.60  #Partial instantiations: 0
% 3.39/1.60  #Strategies tried      : 1
% 3.39/1.60  
% 3.39/1.60  Timing (in seconds)
% 3.39/1.60  ----------------------
% 3.39/1.60  Preprocessing        : 0.31
% 3.39/1.60  Parsing              : 0.16
% 3.39/1.60  CNF conversion       : 0.02
% 3.39/1.60  Main loop            : 0.48
% 3.39/1.60  Inferencing          : 0.19
% 3.39/1.61  Reduction            : 0.14
% 3.39/1.61  Demodulation         : 0.10
% 3.39/1.61  BG Simplification    : 0.02
% 3.39/1.61  Subsumption          : 0.08
% 3.39/1.61  Abstraction          : 0.03
% 3.39/1.61  MUC search           : 0.00
% 3.39/1.61  Cooper               : 0.00
% 3.39/1.61  Total                : 0.84
% 3.39/1.61  Index Insertion      : 0.00
% 3.39/1.61  Index Deletion       : 0.00
% 3.39/1.61  Index Matching       : 0.00
% 3.39/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
