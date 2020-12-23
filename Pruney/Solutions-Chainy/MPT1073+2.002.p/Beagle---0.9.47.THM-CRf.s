%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:58 EST 2020

% Result     : Theorem 4.39s
% Output     : CNFRefutation 4.39s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 186 expanded)
%              Number of leaves         :   46 (  83 expanded)
%              Depth                    :   10
%              Number of atoms          :  151 ( 414 expanded)
%              Number of equality atoms :   37 ( 104 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_132,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
        & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_62,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_214,plain,(
    ! [C_75,B_76,A_77] :
      ( v5_relat_1(C_75,B_76)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_77,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_234,plain,(
    v5_relat_1('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_214])).

tff(c_368,plain,(
    ! [A_101,B_102,C_103] :
      ( k2_relset_1(A_101,B_102,C_103) = k2_relat_1(C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_388,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_368])).

tff(c_60,plain,(
    r2_hidden('#skF_3',k2_relset_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_403,plain,(
    r2_hidden('#skF_3',k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_60])).

tff(c_143,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_161,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_143])).

tff(c_66,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_64,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1046,plain,(
    ! [B_217,A_218,C_219] :
      ( k1_xboole_0 = B_217
      | k8_relset_1(A_218,B_217,C_219,B_217) = A_218
      | ~ m1_subset_1(C_219,k1_zfmisc_1(k2_zfmisc_1(A_218,B_217)))
      | ~ v1_funct_2(C_219,A_218,B_217)
      | ~ v1_funct_1(C_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1054,plain,
    ( k1_xboole_0 = '#skF_5'
    | k8_relset_1('#skF_4','#skF_5','#skF_6','#skF_5') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_1046])).

tff(c_1063,plain,
    ( k1_xboole_0 = '#skF_5'
    | k8_relset_1('#skF_4','#skF_5','#skF_6','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_1054])).

tff(c_1065,plain,(
    k8_relset_1('#skF_4','#skF_5','#skF_6','#skF_5') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1063])).

tff(c_975,plain,(
    ! [B_214,A_215,C_216] :
      ( k7_relset_1(B_214,A_215,C_216,k8_relset_1(B_214,A_215,C_216,A_215)) = k2_relset_1(B_214,A_215,C_216)
      | ~ m1_subset_1(C_216,k1_zfmisc_1(k2_zfmisc_1(B_214,A_215))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_983,plain,(
    k7_relset_1('#skF_4','#skF_5','#skF_6',k8_relset_1('#skF_4','#skF_5','#skF_6','#skF_5')) = k2_relset_1('#skF_4','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_975])).

tff(c_991,plain,(
    k7_relset_1('#skF_4','#skF_5','#skF_6',k8_relset_1('#skF_4','#skF_5','#skF_6','#skF_5')) = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_983])).

tff(c_487,plain,(
    ! [A_126,B_127,C_128,D_129] :
      ( k7_relset_1(A_126,B_127,C_128,D_129) = k9_relat_1(C_128,D_129)
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_502,plain,(
    ! [D_129] : k7_relset_1('#skF_4','#skF_5','#skF_6',D_129) = k9_relat_1('#skF_6',D_129) ),
    inference(resolution,[status(thm)],[c_62,c_487])).

tff(c_995,plain,(
    k9_relat_1('#skF_6',k8_relset_1('#skF_4','#skF_5','#skF_6','#skF_5')) = k2_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_991,c_502])).

tff(c_1067,plain,(
    k9_relat_1('#skF_6','#skF_4') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1065,c_995])).

tff(c_420,plain,(
    ! [A_108,B_109,C_110] :
      ( r2_hidden('#skF_2'(A_108,B_109,C_110),B_109)
      | ~ r2_hidden(A_108,k9_relat_1(C_110,B_109))
      | ~ v1_relat_1(C_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,B_8)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1144,plain,(
    ! [A_224,B_225,C_226] :
      ( m1_subset_1('#skF_2'(A_224,B_225,C_226),B_225)
      | ~ r2_hidden(A_224,k9_relat_1(C_226,B_225))
      | ~ v1_relat_1(C_226) ) ),
    inference(resolution,[status(thm)],[c_420,c_14])).

tff(c_1146,plain,(
    ! [A_224] :
      ( m1_subset_1('#skF_2'(A_224,'#skF_4','#skF_6'),'#skF_4')
      | ~ r2_hidden(A_224,k2_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1067,c_1144])).

tff(c_1168,plain,(
    ! [A_227] :
      ( m1_subset_1('#skF_2'(A_227,'#skF_4','#skF_6'),'#skF_4')
      | ~ r2_hidden(A_227,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_1146])).

tff(c_1191,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_4','#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_403,c_1168])).

tff(c_58,plain,(
    ! [E_46] :
      ( k1_funct_1('#skF_6',E_46) != '#skF_3'
      | ~ m1_subset_1(E_46,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1199,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_3','#skF_4','#skF_6')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_1191,c_58])).

tff(c_574,plain,(
    ! [A_149,B_150,C_151] :
      ( r2_hidden(k4_tarski('#skF_2'(A_149,B_150,C_151),A_149),C_151)
      | ~ r2_hidden(A_149,k9_relat_1(C_151,B_150))
      | ~ v1_relat_1(C_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_34,plain,(
    ! [C_21,A_19,B_20] :
      ( k1_funct_1(C_21,A_19) = B_20
      | ~ r2_hidden(k4_tarski(A_19,B_20),C_21)
      | ~ v1_funct_1(C_21)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1881,plain,(
    ! [C_303,A_304,B_305] :
      ( k1_funct_1(C_303,'#skF_2'(A_304,B_305,C_303)) = A_304
      | ~ v1_funct_1(C_303)
      | ~ r2_hidden(A_304,k9_relat_1(C_303,B_305))
      | ~ v1_relat_1(C_303) ) ),
    inference(resolution,[status(thm)],[c_574,c_34])).

tff(c_1883,plain,(
    ! [A_304] :
      ( k1_funct_1('#skF_6','#skF_2'(A_304,'#skF_4','#skF_6')) = A_304
      | ~ v1_funct_1('#skF_6')
      | ~ r2_hidden(A_304,k2_relat_1('#skF_6'))
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1067,c_1881])).

tff(c_1905,plain,(
    ! [A_306] :
      ( k1_funct_1('#skF_6','#skF_2'(A_306,'#skF_4','#skF_6')) = A_306
      | ~ r2_hidden(A_306,k2_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_66,c_1883])).

tff(c_1920,plain,(
    k1_funct_1('#skF_6','#skF_2'('#skF_3','#skF_4','#skF_6')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_403,c_1905])).

tff(c_1931,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1199,c_1920])).

tff(c_1932,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1063])).

tff(c_22,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k2_relat_1(B_12),A_11)
      | ~ v5_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_332,plain,(
    ! [C_97,B_98,A_99] :
      ( v1_xboole_0(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(B_98,A_99)))
      | ~ v1_xboole_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_346,plain,(
    ! [C_97] :
      ( v1_xboole_0(C_97)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_332])).

tff(c_356,plain,(
    ! [C_100] :
      ( v1_xboole_0(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_346])).

tff(c_389,plain,(
    ! [A_104] :
      ( v1_xboole_0(A_104)
      | ~ r1_tarski(A_104,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_356])).

tff(c_429,plain,(
    ! [B_111] :
      ( v1_xboole_0(k2_relat_1(B_111))
      | ~ v5_relat_1(B_111,k1_xboole_0)
      | ~ v1_relat_1(B_111) ) ),
    inference(resolution,[status(thm)],[c_22,c_389])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_108,plain,(
    ~ v1_xboole_0(k2_relset_1('#skF_4','#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_60,c_2])).

tff(c_402,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_108])).

tff(c_432,plain,
    ( ~ v5_relat_1('#skF_6',k1_xboole_0)
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_429,c_402])).

tff(c_435,plain,(
    ~ v5_relat_1('#skF_6',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_432])).

tff(c_1954,plain,(
    ~ v5_relat_1('#skF_6','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1932,c_435])).

tff(c_1971,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_1954])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:36:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.39/1.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.39/1.84  
% 4.39/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.39/1.84  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 4.39/1.84  
% 4.39/1.84  %Foreground sorts:
% 4.39/1.84  
% 4.39/1.84  
% 4.39/1.84  %Background operators:
% 4.39/1.84  
% 4.39/1.84  
% 4.39/1.84  %Foreground operators:
% 4.39/1.84  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.39/1.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.39/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.39/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.39/1.84  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.39/1.84  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.39/1.84  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.39/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.39/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.39/1.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.39/1.84  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.39/1.84  tff('#skF_5', type, '#skF_5': $i).
% 4.39/1.84  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.39/1.84  tff('#skF_6', type, '#skF_6': $i).
% 4.39/1.84  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.39/1.84  tff('#skF_3', type, '#skF_3': $i).
% 4.39/1.84  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.39/1.84  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.39/1.84  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.39/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.39/1.84  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.39/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.39/1.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.39/1.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.39/1.84  tff('#skF_4', type, '#skF_4': $i).
% 4.39/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.39/1.84  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.39/1.84  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.39/1.84  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.39/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.39/1.84  
% 4.39/1.86  tff(f_132, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 4.39/1.86  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.39/1.86  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.39/1.86  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.39/1.86  tff(f_116, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_2)).
% 4.39/1.86  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_relset_1)).
% 4.39/1.86  tff(f_98, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.39/1.86  tff(f_63, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 4.39/1.86  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 4.39/1.86  tff(f_73, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 4.39/1.86  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 4.39/1.86  tff(f_46, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.39/1.86  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.39/1.86  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.39/1.86  tff(f_90, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 4.39/1.86  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.39/1.86  tff(c_62, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.39/1.86  tff(c_214, plain, (![C_75, B_76, A_77]: (v5_relat_1(C_75, B_76) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_77, B_76))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.39/1.86  tff(c_234, plain, (v5_relat_1('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_62, c_214])).
% 4.39/1.86  tff(c_368, plain, (![A_101, B_102, C_103]: (k2_relset_1(A_101, B_102, C_103)=k2_relat_1(C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.39/1.86  tff(c_388, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_62, c_368])).
% 4.39/1.86  tff(c_60, plain, (r2_hidden('#skF_3', k2_relset_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.39/1.86  tff(c_403, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_388, c_60])).
% 4.39/1.86  tff(c_143, plain, (![C_62, A_63, B_64]: (v1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.39/1.86  tff(c_161, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_62, c_143])).
% 4.39/1.86  tff(c_66, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.39/1.86  tff(c_64, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.39/1.86  tff(c_1046, plain, (![B_217, A_218, C_219]: (k1_xboole_0=B_217 | k8_relset_1(A_218, B_217, C_219, B_217)=A_218 | ~m1_subset_1(C_219, k1_zfmisc_1(k2_zfmisc_1(A_218, B_217))) | ~v1_funct_2(C_219, A_218, B_217) | ~v1_funct_1(C_219))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.39/1.86  tff(c_1054, plain, (k1_xboole_0='#skF_5' | k8_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_5')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_62, c_1046])).
% 4.39/1.86  tff(c_1063, plain, (k1_xboole_0='#skF_5' | k8_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_1054])).
% 4.39/1.86  tff(c_1065, plain, (k8_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_5')='#skF_4'), inference(splitLeft, [status(thm)], [c_1063])).
% 4.39/1.86  tff(c_975, plain, (![B_214, A_215, C_216]: (k7_relset_1(B_214, A_215, C_216, k8_relset_1(B_214, A_215, C_216, A_215))=k2_relset_1(B_214, A_215, C_216) | ~m1_subset_1(C_216, k1_zfmisc_1(k2_zfmisc_1(B_214, A_215))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.39/1.86  tff(c_983, plain, (k7_relset_1('#skF_4', '#skF_5', '#skF_6', k8_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_5'))=k2_relset_1('#skF_4', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_62, c_975])).
% 4.39/1.86  tff(c_991, plain, (k7_relset_1('#skF_4', '#skF_5', '#skF_6', k8_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_5'))=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_388, c_983])).
% 4.39/1.86  tff(c_487, plain, (![A_126, B_127, C_128, D_129]: (k7_relset_1(A_126, B_127, C_128, D_129)=k9_relat_1(C_128, D_129) | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.39/1.86  tff(c_502, plain, (![D_129]: (k7_relset_1('#skF_4', '#skF_5', '#skF_6', D_129)=k9_relat_1('#skF_6', D_129))), inference(resolution, [status(thm)], [c_62, c_487])).
% 4.39/1.86  tff(c_995, plain, (k9_relat_1('#skF_6', k8_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_5'))=k2_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_991, c_502])).
% 4.39/1.86  tff(c_1067, plain, (k9_relat_1('#skF_6', '#skF_4')=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1065, c_995])).
% 4.39/1.86  tff(c_420, plain, (![A_108, B_109, C_110]: (r2_hidden('#skF_2'(A_108, B_109, C_110), B_109) | ~r2_hidden(A_108, k9_relat_1(C_110, B_109)) | ~v1_relat_1(C_110))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.39/1.86  tff(c_14, plain, (![A_7, B_8]: (m1_subset_1(A_7, B_8) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.39/1.86  tff(c_1144, plain, (![A_224, B_225, C_226]: (m1_subset_1('#skF_2'(A_224, B_225, C_226), B_225) | ~r2_hidden(A_224, k9_relat_1(C_226, B_225)) | ~v1_relat_1(C_226))), inference(resolution, [status(thm)], [c_420, c_14])).
% 4.39/1.86  tff(c_1146, plain, (![A_224]: (m1_subset_1('#skF_2'(A_224, '#skF_4', '#skF_6'), '#skF_4') | ~r2_hidden(A_224, k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1067, c_1144])).
% 4.39/1.86  tff(c_1168, plain, (![A_227]: (m1_subset_1('#skF_2'(A_227, '#skF_4', '#skF_6'), '#skF_4') | ~r2_hidden(A_227, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_1146])).
% 4.39/1.86  tff(c_1191, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4', '#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_403, c_1168])).
% 4.39/1.86  tff(c_58, plain, (![E_46]: (k1_funct_1('#skF_6', E_46)!='#skF_3' | ~m1_subset_1(E_46, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.39/1.86  tff(c_1199, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_3', '#skF_4', '#skF_6'))!='#skF_3'), inference(resolution, [status(thm)], [c_1191, c_58])).
% 4.39/1.86  tff(c_574, plain, (![A_149, B_150, C_151]: (r2_hidden(k4_tarski('#skF_2'(A_149, B_150, C_151), A_149), C_151) | ~r2_hidden(A_149, k9_relat_1(C_151, B_150)) | ~v1_relat_1(C_151))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.39/1.86  tff(c_34, plain, (![C_21, A_19, B_20]: (k1_funct_1(C_21, A_19)=B_20 | ~r2_hidden(k4_tarski(A_19, B_20), C_21) | ~v1_funct_1(C_21) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.39/1.86  tff(c_1881, plain, (![C_303, A_304, B_305]: (k1_funct_1(C_303, '#skF_2'(A_304, B_305, C_303))=A_304 | ~v1_funct_1(C_303) | ~r2_hidden(A_304, k9_relat_1(C_303, B_305)) | ~v1_relat_1(C_303))), inference(resolution, [status(thm)], [c_574, c_34])).
% 4.39/1.86  tff(c_1883, plain, (![A_304]: (k1_funct_1('#skF_6', '#skF_2'(A_304, '#skF_4', '#skF_6'))=A_304 | ~v1_funct_1('#skF_6') | ~r2_hidden(A_304, k2_relat_1('#skF_6')) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1067, c_1881])).
% 4.39/1.86  tff(c_1905, plain, (![A_306]: (k1_funct_1('#skF_6', '#skF_2'(A_306, '#skF_4', '#skF_6'))=A_306 | ~r2_hidden(A_306, k2_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_66, c_1883])).
% 4.39/1.86  tff(c_1920, plain, (k1_funct_1('#skF_6', '#skF_2'('#skF_3', '#skF_4', '#skF_6'))='#skF_3'), inference(resolution, [status(thm)], [c_403, c_1905])).
% 4.39/1.86  tff(c_1931, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1199, c_1920])).
% 4.39/1.86  tff(c_1932, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1063])).
% 4.39/1.86  tff(c_22, plain, (![B_12, A_11]: (r1_tarski(k2_relat_1(B_12), A_11) | ~v5_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.39/1.86  tff(c_18, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.39/1.86  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.39/1.86  tff(c_10, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.39/1.86  tff(c_332, plain, (![C_97, B_98, A_99]: (v1_xboole_0(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(B_98, A_99))) | ~v1_xboole_0(A_99))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.39/1.86  tff(c_346, plain, (![C_97]: (v1_xboole_0(C_97) | ~m1_subset_1(C_97, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_332])).
% 4.39/1.86  tff(c_356, plain, (![C_100]: (v1_xboole_0(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_346])).
% 4.39/1.86  tff(c_389, plain, (![A_104]: (v1_xboole_0(A_104) | ~r1_tarski(A_104, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_356])).
% 4.39/1.86  tff(c_429, plain, (![B_111]: (v1_xboole_0(k2_relat_1(B_111)) | ~v5_relat_1(B_111, k1_xboole_0) | ~v1_relat_1(B_111))), inference(resolution, [status(thm)], [c_22, c_389])).
% 4.39/1.86  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.39/1.86  tff(c_108, plain, (~v1_xboole_0(k2_relset_1('#skF_4', '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_60, c_2])).
% 4.39/1.86  tff(c_402, plain, (~v1_xboole_0(k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_388, c_108])).
% 4.39/1.86  tff(c_432, plain, (~v5_relat_1('#skF_6', k1_xboole_0) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_429, c_402])).
% 4.39/1.86  tff(c_435, plain, (~v5_relat_1('#skF_6', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_161, c_432])).
% 4.39/1.86  tff(c_1954, plain, (~v5_relat_1('#skF_6', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1932, c_435])).
% 4.39/1.86  tff(c_1971, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_234, c_1954])).
% 4.39/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.39/1.86  
% 4.39/1.86  Inference rules
% 4.39/1.86  ----------------------
% 4.39/1.86  #Ref     : 0
% 4.39/1.86  #Sup     : 390
% 4.39/1.86  #Fact    : 0
% 4.39/1.86  #Define  : 0
% 4.39/1.86  #Split   : 8
% 4.39/1.86  #Chain   : 0
% 4.39/1.86  #Close   : 0
% 4.39/1.86  
% 4.39/1.86  Ordering : KBO
% 4.39/1.86  
% 4.39/1.86  Simplification rules
% 4.39/1.86  ----------------------
% 4.39/1.86  #Subsume      : 133
% 4.39/1.86  #Demod        : 138
% 4.39/1.86  #Tautology    : 76
% 4.39/1.86  #SimpNegUnit  : 74
% 4.39/1.86  #BackRed      : 77
% 4.39/1.86  
% 4.39/1.86  #Partial instantiations: 0
% 4.39/1.86  #Strategies tried      : 1
% 4.39/1.86  
% 4.39/1.86  Timing (in seconds)
% 4.39/1.86  ----------------------
% 4.39/1.86  Preprocessing        : 0.38
% 4.39/1.86  Parsing              : 0.19
% 4.39/1.86  CNF conversion       : 0.03
% 4.39/1.86  Main loop            : 0.66
% 4.39/1.86  Inferencing          : 0.24
% 4.39/1.86  Reduction            : 0.19
% 4.39/1.86  Demodulation         : 0.13
% 4.39/1.86  BG Simplification    : 0.03
% 4.39/1.86  Subsumption          : 0.13
% 4.39/1.86  Abstraction          : 0.04
% 4.39/1.86  MUC search           : 0.00
% 4.39/1.86  Cooper               : 0.00
% 4.39/1.86  Total                : 1.08
% 4.39/1.86  Index Insertion      : 0.00
% 4.39/1.86  Index Deletion       : 0.00
% 4.39/1.87  Index Matching       : 0.00
% 4.39/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
