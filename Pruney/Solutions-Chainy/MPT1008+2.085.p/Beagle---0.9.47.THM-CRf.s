%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:37 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 485 expanded)
%              Number of leaves         :   42 ( 181 expanded)
%              Depth                    :   19
%              Number of atoms          :  217 (1075 expanded)
%              Number of equality atoms :  116 ( 485 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_144,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_31,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(D,k1_enumset1(A,B,C))
    <=> ~ ( D != k1_xboole_0
          & D != k1_tarski(A)
          & D != k1_tarski(B)
          & D != k1_tarski(C)
          & D != k2_tarski(A,B)
          & D != k2_tarski(B,C)
          & D != k2_tarski(A,C)
          & D != k1_enumset1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_67,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_120,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_132,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_88,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_153,plain,(
    ! [C_76,A_77,B_78] :
      ( v1_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_162,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_153])).

tff(c_38,plain,(
    ! [A_14] :
      ( k1_relat_1(A_14) != k1_xboole_0
      | k1_xboole_0 = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_169,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_162,c_38])).

tff(c_171,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_169])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_373,plain,(
    ! [B_125,A_126] :
      ( k1_tarski(k1_funct_1(B_125,A_126)) = k2_relat_1(B_125)
      | k1_tarski(A_126) != k1_relat_1(B_125)
      | ~ v1_funct_1(B_125)
      | ~ v1_relat_1(B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_279,plain,(
    ! [A_112,B_113,C_114] :
      ( k2_relset_1(A_112,B_113,C_114) = k2_relat_1(C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_288,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_279])).

tff(c_60,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') != k1_tarski(k1_funct_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_296,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_60])).

tff(c_379,plain,
    ( k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_296])).

tff(c_407,plain,(
    k1_tarski('#skF_2') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_68,c_379])).

tff(c_253,plain,(
    ! [A_106,B_107,C_108] :
      ( k1_relset_1(A_106,B_107,C_108) = k1_relat_1(C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_262,plain,(
    k1_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_253])).

tff(c_301,plain,(
    ! [A_117,B_118,C_119] :
      ( m1_subset_1(k1_relset_1(A_117,B_118,C_119),k1_zfmisc_1(A_117))
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_322,plain,
    ( m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(k1_tarski('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_301])).

tff(c_328,plain,(
    m1_subset_1(k1_relat_1('#skF_4'),k1_zfmisc_1(k1_tarski('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_322])).

tff(c_28,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_332,plain,(
    r1_tarski(k1_relat_1('#skF_4'),k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_328,c_28])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_3,B_4] : k1_enumset1(A_3,A_3,B_4) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_505,plain,(
    ! [A_146,B_147,C_148,D_149] :
      ( k1_enumset1(A_146,B_147,C_148) = D_149
      | k2_tarski(A_146,C_148) = D_149
      | k2_tarski(B_147,C_148) = D_149
      | k2_tarski(A_146,B_147) = D_149
      | k1_tarski(C_148) = D_149
      | k1_tarski(B_147) = D_149
      | k1_tarski(A_146) = D_149
      | k1_xboole_0 = D_149
      | ~ r1_tarski(D_149,k1_enumset1(A_146,B_147,C_148)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_527,plain,(
    ! [A_3,B_4,D_149] :
      ( k1_enumset1(A_3,A_3,B_4) = D_149
      | k2_tarski(A_3,B_4) = D_149
      | k2_tarski(A_3,B_4) = D_149
      | k2_tarski(A_3,A_3) = D_149
      | k1_tarski(B_4) = D_149
      | k1_tarski(A_3) = D_149
      | k1_tarski(A_3) = D_149
      | k1_xboole_0 = D_149
      | ~ r1_tarski(D_149,k2_tarski(A_3,B_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_505])).

tff(c_802,plain,(
    ! [A_219,B_220,D_221] :
      ( k2_tarski(A_219,B_220) = D_221
      | k2_tarski(A_219,B_220) = D_221
      | k2_tarski(A_219,B_220) = D_221
      | k1_tarski(A_219) = D_221
      | k1_tarski(B_220) = D_221
      | k1_tarski(A_219) = D_221
      | k1_tarski(A_219) = D_221
      | k1_xboole_0 = D_221
      | ~ r1_tarski(D_221,k2_tarski(A_219,B_220)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_527])).

tff(c_828,plain,(
    ! [A_2,D_221] :
      ( k2_tarski(A_2,A_2) = D_221
      | k2_tarski(A_2,A_2) = D_221
      | k2_tarski(A_2,A_2) = D_221
      | k1_tarski(A_2) = D_221
      | k1_tarski(A_2) = D_221
      | k1_tarski(A_2) = D_221
      | k1_tarski(A_2) = D_221
      | k1_xboole_0 = D_221
      | ~ r1_tarski(D_221,k1_tarski(A_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_802])).

tff(c_846,plain,(
    ! [A_222,D_223] :
      ( k1_tarski(A_222) = D_223
      | k1_tarski(A_222) = D_223
      | k1_tarski(A_222) = D_223
      | k1_tarski(A_222) = D_223
      | k1_tarski(A_222) = D_223
      | k1_tarski(A_222) = D_223
      | k1_tarski(A_222) = D_223
      | k1_xboole_0 = D_223
      | ~ r1_tarski(D_223,k1_tarski(A_222)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_4,c_828])).

tff(c_863,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_332,c_846])).

tff(c_877,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_171,c_407,c_407,c_407,c_407,c_407,c_407,c_407,c_863])).

tff(c_878,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_884,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_878,c_2])).

tff(c_879,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_169])).

tff(c_907,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_878,c_879])).

tff(c_32,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_885,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_878,c_878,c_32])).

tff(c_1125,plain,(
    ! [B_275,A_276] :
      ( k1_tarski(k1_funct_1(B_275,A_276)) = k2_relat_1(B_275)
      | k1_tarski(A_276) != k1_relat_1(B_275)
      | ~ v1_funct_1(B_275)
      | ~ v1_relat_1(B_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_998,plain,(
    ! [A_256,B_257,C_258] :
      ( k2_relset_1(A_256,B_257,C_258) = k2_relat_1(C_258)
      | ~ m1_subset_1(C_258,k1_zfmisc_1(k2_zfmisc_1(A_256,B_257))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1005,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_998])).

tff(c_1008,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_885,c_1005])).

tff(c_1009,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_60])).

tff(c_1131,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1125,c_1009])).

tff(c_1158,plain,(
    k1_tarski('#skF_2') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_68,c_907,c_885,c_1131])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_887,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_878,c_62])).

tff(c_66,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_52,plain,(
    ! [A_31] :
      ( r2_hidden('#skF_1'(A_31),A_31)
      | k1_xboole_0 = A_31 ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_883,plain,(
    ! [A_31] :
      ( r2_hidden('#skF_1'(A_31),A_31)
      | A_31 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_878,c_52])).

tff(c_30,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1014,plain,(
    ! [A_259,B_260,C_261] :
      ( k1_relset_1(A_259,B_260,C_261) = k1_relat_1(C_261)
      | ~ m1_subset_1(C_261,k1_zfmisc_1(k2_zfmisc_1(A_259,B_260))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1029,plain,(
    ! [A_262,B_263,A_264] :
      ( k1_relset_1(A_262,B_263,A_264) = k1_relat_1(A_264)
      | ~ r1_tarski(A_264,k2_zfmisc_1(A_262,B_263)) ) ),
    inference(resolution,[status(thm)],[c_30,c_1014])).

tff(c_1033,plain,(
    ! [A_262,B_263] : k1_relset_1(A_262,B_263,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_884,c_1029])).

tff(c_1062,plain,(
    ! [A_268,B_269] : k1_relset_1(A_268,B_269,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_907,c_1033])).

tff(c_46,plain,(
    ! [A_22,B_23,C_24] :
      ( m1_subset_1(k1_relset_1(A_22,B_23,C_24),k1_zfmisc_1(A_22))
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1077,plain,(
    ! [A_270,B_271] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(A_270))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_270,B_271))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1062,c_46])).

tff(c_1080,plain,(
    ! [A_270,B_271] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(A_270))
      | ~ r1_tarski('#skF_4',k2_zfmisc_1(A_270,B_271)) ) ),
    inference(resolution,[status(thm)],[c_30,c_1077])).

tff(c_1086,plain,(
    ! [A_270] : m1_subset_1('#skF_4',k1_zfmisc_1(A_270)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_884,c_1080])).

tff(c_1093,plain,(
    ! [A_272] : m1_subset_1('#skF_4',k1_zfmisc_1(A_272)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_884,c_1080])).

tff(c_50,plain,(
    ! [A_28,B_29,C_30] :
      ( k2_relset_1(A_28,B_29,C_30) = k2_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1101,plain,(
    ! [A_28,B_29] : k2_relset_1(A_28,B_29,'#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1093,c_50])).

tff(c_1112,plain,(
    ! [A_28,B_29] : k2_relset_1(A_28,B_29,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_885,c_1101])).

tff(c_58,plain,(
    ! [D_44,C_43,A_41,B_42] :
      ( r2_hidden(k1_funct_1(D_44,C_43),k2_relset_1(A_41,B_42,D_44))
      | k1_xboole_0 = B_42
      | ~ r2_hidden(C_43,A_41)
      | ~ m1_subset_1(D_44,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42)))
      | ~ v1_funct_2(D_44,A_41,B_42)
      | ~ v1_funct_1(D_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1182,plain,(
    ! [D_283,C_284,A_285,B_286] :
      ( r2_hidden(k1_funct_1(D_283,C_284),k2_relset_1(A_285,B_286,D_283))
      | B_286 = '#skF_4'
      | ~ r2_hidden(C_284,A_285)
      | ~ m1_subset_1(D_283,k1_zfmisc_1(k2_zfmisc_1(A_285,B_286)))
      | ~ v1_funct_2(D_283,A_285,B_286)
      | ~ v1_funct_1(D_283) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_878,c_58])).

tff(c_1192,plain,(
    ! [C_284,B_29,A_28] :
      ( r2_hidden(k1_funct_1('#skF_4',C_284),'#skF_4')
      | B_29 = '#skF_4'
      | ~ r2_hidden(C_284,A_28)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ v1_funct_2('#skF_4',A_28,B_29)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1112,c_1182])).

tff(c_1231,plain,(
    ! [C_294,B_295,A_296] :
      ( r2_hidden(k1_funct_1('#skF_4',C_294),'#skF_4')
      | B_295 = '#skF_4'
      | ~ r2_hidden(C_294,A_296)
      | ~ v1_funct_2('#skF_4',A_296,B_295) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1086,c_1192])).

tff(c_1238,plain,(
    ! [A_297,B_298] :
      ( r2_hidden(k1_funct_1('#skF_4','#skF_1'(A_297)),'#skF_4')
      | B_298 = '#skF_4'
      | ~ v1_funct_2('#skF_4',A_297,B_298)
      | A_297 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_883,c_1231])).

tff(c_1240,plain,
    ( r2_hidden(k1_funct_1('#skF_4','#skF_1'(k1_tarski('#skF_2'))),'#skF_4')
    | '#skF_3' = '#skF_4'
    | k1_tarski('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_66,c_1238])).

tff(c_1243,plain,(
    r2_hidden(k1_funct_1('#skF_4','#skF_1'(k1_tarski('#skF_2'))),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1158,c_887,c_1240])).

tff(c_42,plain,(
    ! [B_18,A_17] :
      ( ~ r1_tarski(B_18,A_17)
      | ~ r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1252,plain,(
    ~ r1_tarski('#skF_4',k1_funct_1('#skF_4','#skF_1'(k1_tarski('#skF_2')))) ),
    inference(resolution,[status(thm)],[c_1243,c_42])).

tff(c_1261,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_884,c_1252])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:57:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.65/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.65/1.64  
% 3.65/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.65/1.65  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.65/1.65  
% 3.65/1.65  %Foreground sorts:
% 3.65/1.65  
% 3.65/1.65  
% 3.65/1.65  %Background operators:
% 3.65/1.65  
% 3.65/1.65  
% 3.65/1.65  %Foreground operators:
% 3.65/1.65  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.65/1.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.65/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.65/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.65/1.65  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.65/1.65  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.65/1.65  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.65/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.65/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.65/1.65  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.65/1.65  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.65/1.65  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.65/1.65  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.65/1.65  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.65/1.65  tff('#skF_2', type, '#skF_2': $i).
% 3.65/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.65/1.65  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.65/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.65/1.65  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.65/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.65/1.65  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.65/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.65/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.65/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.65/1.65  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.65/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.65/1.65  
% 3.65/1.66  tff(f_144, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 3.65/1.66  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.65/1.66  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.65/1.66  tff(f_83, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.65/1.66  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.65/1.66  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.65/1.66  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.65/1.66  tff(f_64, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.65/1.66  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.65/1.66  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.65/1.66  tff(f_60, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 3.65/1.66  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.65/1.66  tff(f_67, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.65/1.66  tff(f_120, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 3.65/1.66  tff(f_132, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 3.65/1.66  tff(f_88, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.65/1.66  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.65/1.66  tff(c_153, plain, (![C_76, A_77, B_78]: (v1_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.65/1.66  tff(c_162, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_153])).
% 3.65/1.66  tff(c_38, plain, (![A_14]: (k1_relat_1(A_14)!=k1_xboole_0 | k1_xboole_0=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.65/1.66  tff(c_169, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_162, c_38])).
% 3.65/1.66  tff(c_171, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_169])).
% 3.65/1.66  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.65/1.66  tff(c_373, plain, (![B_125, A_126]: (k1_tarski(k1_funct_1(B_125, A_126))=k2_relat_1(B_125) | k1_tarski(A_126)!=k1_relat_1(B_125) | ~v1_funct_1(B_125) | ~v1_relat_1(B_125))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.65/1.66  tff(c_279, plain, (![A_112, B_113, C_114]: (k2_relset_1(A_112, B_113, C_114)=k2_relat_1(C_114) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.65/1.66  tff(c_288, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_279])).
% 3.65/1.66  tff(c_60, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')!=k1_tarski(k1_funct_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.65/1.66  tff(c_296, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_288, c_60])).
% 3.65/1.66  tff(c_379, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_373, c_296])).
% 3.65/1.66  tff(c_407, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_68, c_379])).
% 3.65/1.66  tff(c_253, plain, (![A_106, B_107, C_108]: (k1_relset_1(A_106, B_107, C_108)=k1_relat_1(C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.65/1.66  tff(c_262, plain, (k1_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_253])).
% 3.65/1.66  tff(c_301, plain, (![A_117, B_118, C_119]: (m1_subset_1(k1_relset_1(A_117, B_118, C_119), k1_zfmisc_1(A_117)) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.65/1.66  tff(c_322, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(k1_tarski('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_262, c_301])).
% 3.65/1.66  tff(c_328, plain, (m1_subset_1(k1_relat_1('#skF_4'), k1_zfmisc_1(k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_322])).
% 3.65/1.66  tff(c_28, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.65/1.66  tff(c_332, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_328, c_28])).
% 3.65/1.66  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.65/1.66  tff(c_6, plain, (![A_3, B_4]: (k1_enumset1(A_3, A_3, B_4)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.65/1.66  tff(c_505, plain, (![A_146, B_147, C_148, D_149]: (k1_enumset1(A_146, B_147, C_148)=D_149 | k2_tarski(A_146, C_148)=D_149 | k2_tarski(B_147, C_148)=D_149 | k2_tarski(A_146, B_147)=D_149 | k1_tarski(C_148)=D_149 | k1_tarski(B_147)=D_149 | k1_tarski(A_146)=D_149 | k1_xboole_0=D_149 | ~r1_tarski(D_149, k1_enumset1(A_146, B_147, C_148)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.65/1.66  tff(c_527, plain, (![A_3, B_4, D_149]: (k1_enumset1(A_3, A_3, B_4)=D_149 | k2_tarski(A_3, B_4)=D_149 | k2_tarski(A_3, B_4)=D_149 | k2_tarski(A_3, A_3)=D_149 | k1_tarski(B_4)=D_149 | k1_tarski(A_3)=D_149 | k1_tarski(A_3)=D_149 | k1_xboole_0=D_149 | ~r1_tarski(D_149, k2_tarski(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_505])).
% 3.65/1.66  tff(c_802, plain, (![A_219, B_220, D_221]: (k2_tarski(A_219, B_220)=D_221 | k2_tarski(A_219, B_220)=D_221 | k2_tarski(A_219, B_220)=D_221 | k1_tarski(A_219)=D_221 | k1_tarski(B_220)=D_221 | k1_tarski(A_219)=D_221 | k1_tarski(A_219)=D_221 | k1_xboole_0=D_221 | ~r1_tarski(D_221, k2_tarski(A_219, B_220)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6, c_527])).
% 3.65/1.66  tff(c_828, plain, (![A_2, D_221]: (k2_tarski(A_2, A_2)=D_221 | k2_tarski(A_2, A_2)=D_221 | k2_tarski(A_2, A_2)=D_221 | k1_tarski(A_2)=D_221 | k1_tarski(A_2)=D_221 | k1_tarski(A_2)=D_221 | k1_tarski(A_2)=D_221 | k1_xboole_0=D_221 | ~r1_tarski(D_221, k1_tarski(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_802])).
% 3.65/1.66  tff(c_846, plain, (![A_222, D_223]: (k1_tarski(A_222)=D_223 | k1_tarski(A_222)=D_223 | k1_tarski(A_222)=D_223 | k1_tarski(A_222)=D_223 | k1_tarski(A_222)=D_223 | k1_tarski(A_222)=D_223 | k1_tarski(A_222)=D_223 | k1_xboole_0=D_223 | ~r1_tarski(D_223, k1_tarski(A_222)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_4, c_828])).
% 3.65/1.66  tff(c_863, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_332, c_846])).
% 3.65/1.66  tff(c_877, plain, $false, inference(negUnitSimplification, [status(thm)], [c_171, c_407, c_407, c_407, c_407, c_407, c_407, c_407, c_863])).
% 3.65/1.66  tff(c_878, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_169])).
% 3.65/1.66  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.65/1.66  tff(c_884, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_878, c_2])).
% 3.65/1.66  tff(c_879, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_169])).
% 3.65/1.66  tff(c_907, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_878, c_879])).
% 3.65/1.66  tff(c_32, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.65/1.66  tff(c_885, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_878, c_878, c_32])).
% 3.65/1.66  tff(c_1125, plain, (![B_275, A_276]: (k1_tarski(k1_funct_1(B_275, A_276))=k2_relat_1(B_275) | k1_tarski(A_276)!=k1_relat_1(B_275) | ~v1_funct_1(B_275) | ~v1_relat_1(B_275))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.65/1.66  tff(c_998, plain, (![A_256, B_257, C_258]: (k2_relset_1(A_256, B_257, C_258)=k2_relat_1(C_258) | ~m1_subset_1(C_258, k1_zfmisc_1(k2_zfmisc_1(A_256, B_257))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.65/1.66  tff(c_1005, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_998])).
% 3.65/1.66  tff(c_1008, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_885, c_1005])).
% 3.65/1.66  tff(c_1009, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1008, c_60])).
% 3.65/1.66  tff(c_1131, plain, (k2_relat_1('#skF_4')!='#skF_4' | k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1125, c_1009])).
% 3.65/1.66  tff(c_1158, plain, (k1_tarski('#skF_2')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_162, c_68, c_907, c_885, c_1131])).
% 3.65/1.66  tff(c_62, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.65/1.66  tff(c_887, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_878, c_62])).
% 3.65/1.66  tff(c_66, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.65/1.66  tff(c_52, plain, (![A_31]: (r2_hidden('#skF_1'(A_31), A_31) | k1_xboole_0=A_31)), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.65/1.66  tff(c_883, plain, (![A_31]: (r2_hidden('#skF_1'(A_31), A_31) | A_31='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_878, c_52])).
% 3.65/1.66  tff(c_30, plain, (![A_12, B_13]: (m1_subset_1(A_12, k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.65/1.66  tff(c_1014, plain, (![A_259, B_260, C_261]: (k1_relset_1(A_259, B_260, C_261)=k1_relat_1(C_261) | ~m1_subset_1(C_261, k1_zfmisc_1(k2_zfmisc_1(A_259, B_260))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.65/1.66  tff(c_1029, plain, (![A_262, B_263, A_264]: (k1_relset_1(A_262, B_263, A_264)=k1_relat_1(A_264) | ~r1_tarski(A_264, k2_zfmisc_1(A_262, B_263)))), inference(resolution, [status(thm)], [c_30, c_1014])).
% 3.65/1.66  tff(c_1033, plain, (![A_262, B_263]: (k1_relset_1(A_262, B_263, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_884, c_1029])).
% 3.65/1.66  tff(c_1062, plain, (![A_268, B_269]: (k1_relset_1(A_268, B_269, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_907, c_1033])).
% 3.65/1.66  tff(c_46, plain, (![A_22, B_23, C_24]: (m1_subset_1(k1_relset_1(A_22, B_23, C_24), k1_zfmisc_1(A_22)) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.65/1.66  tff(c_1077, plain, (![A_270, B_271]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_270)) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_270, B_271))))), inference(superposition, [status(thm), theory('equality')], [c_1062, c_46])).
% 3.65/1.66  tff(c_1080, plain, (![A_270, B_271]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_270)) | ~r1_tarski('#skF_4', k2_zfmisc_1(A_270, B_271)))), inference(resolution, [status(thm)], [c_30, c_1077])).
% 3.65/1.66  tff(c_1086, plain, (![A_270]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_270)))), inference(demodulation, [status(thm), theory('equality')], [c_884, c_1080])).
% 3.65/1.66  tff(c_1093, plain, (![A_272]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_272)))), inference(demodulation, [status(thm), theory('equality')], [c_884, c_1080])).
% 3.65/1.66  tff(c_50, plain, (![A_28, B_29, C_30]: (k2_relset_1(A_28, B_29, C_30)=k2_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.65/1.66  tff(c_1101, plain, (![A_28, B_29]: (k2_relset_1(A_28, B_29, '#skF_4')=k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1093, c_50])).
% 3.65/1.66  tff(c_1112, plain, (![A_28, B_29]: (k2_relset_1(A_28, B_29, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_885, c_1101])).
% 3.65/1.66  tff(c_58, plain, (![D_44, C_43, A_41, B_42]: (r2_hidden(k1_funct_1(D_44, C_43), k2_relset_1(A_41, B_42, D_44)) | k1_xboole_0=B_42 | ~r2_hidden(C_43, A_41) | ~m1_subset_1(D_44, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))) | ~v1_funct_2(D_44, A_41, B_42) | ~v1_funct_1(D_44))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.65/1.66  tff(c_1182, plain, (![D_283, C_284, A_285, B_286]: (r2_hidden(k1_funct_1(D_283, C_284), k2_relset_1(A_285, B_286, D_283)) | B_286='#skF_4' | ~r2_hidden(C_284, A_285) | ~m1_subset_1(D_283, k1_zfmisc_1(k2_zfmisc_1(A_285, B_286))) | ~v1_funct_2(D_283, A_285, B_286) | ~v1_funct_1(D_283))), inference(demodulation, [status(thm), theory('equality')], [c_878, c_58])).
% 3.65/1.66  tff(c_1192, plain, (![C_284, B_29, A_28]: (r2_hidden(k1_funct_1('#skF_4', C_284), '#skF_4') | B_29='#skF_4' | ~r2_hidden(C_284, A_28) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~v1_funct_2('#skF_4', A_28, B_29) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1112, c_1182])).
% 3.65/1.66  tff(c_1231, plain, (![C_294, B_295, A_296]: (r2_hidden(k1_funct_1('#skF_4', C_294), '#skF_4') | B_295='#skF_4' | ~r2_hidden(C_294, A_296) | ~v1_funct_2('#skF_4', A_296, B_295))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1086, c_1192])).
% 3.65/1.66  tff(c_1238, plain, (![A_297, B_298]: (r2_hidden(k1_funct_1('#skF_4', '#skF_1'(A_297)), '#skF_4') | B_298='#skF_4' | ~v1_funct_2('#skF_4', A_297, B_298) | A_297='#skF_4')), inference(resolution, [status(thm)], [c_883, c_1231])).
% 3.65/1.66  tff(c_1240, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_1'(k1_tarski('#skF_2'))), '#skF_4') | '#skF_3'='#skF_4' | k1_tarski('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_66, c_1238])).
% 3.65/1.66  tff(c_1243, plain, (r2_hidden(k1_funct_1('#skF_4', '#skF_1'(k1_tarski('#skF_2'))), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1158, c_887, c_1240])).
% 3.65/1.66  tff(c_42, plain, (![B_18, A_17]: (~r1_tarski(B_18, A_17) | ~r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.65/1.66  tff(c_1252, plain, (~r1_tarski('#skF_4', k1_funct_1('#skF_4', '#skF_1'(k1_tarski('#skF_2'))))), inference(resolution, [status(thm)], [c_1243, c_42])).
% 3.65/1.66  tff(c_1261, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_884, c_1252])).
% 3.65/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.65/1.66  
% 3.65/1.66  Inference rules
% 3.65/1.66  ----------------------
% 3.65/1.66  #Ref     : 0
% 3.65/1.66  #Sup     : 250
% 3.65/1.66  #Fact    : 0
% 3.65/1.66  #Define  : 0
% 3.65/1.66  #Split   : 3
% 3.65/1.66  #Chain   : 0
% 3.65/1.67  #Close   : 0
% 3.65/1.67  
% 3.65/1.67  Ordering : KBO
% 3.65/1.67  
% 3.65/1.67  Simplification rules
% 3.65/1.67  ----------------------
% 3.65/1.67  #Subsume      : 25
% 3.65/1.67  #Demod        : 177
% 3.65/1.67  #Tautology    : 119
% 3.65/1.67  #SimpNegUnit  : 6
% 3.65/1.67  #BackRed      : 10
% 3.65/1.67  
% 3.65/1.67  #Partial instantiations: 0
% 3.65/1.67  #Strategies tried      : 1
% 3.65/1.67  
% 3.65/1.67  Timing (in seconds)
% 3.65/1.67  ----------------------
% 3.65/1.67  Preprocessing        : 0.36
% 3.65/1.67  Parsing              : 0.19
% 3.65/1.67  CNF conversion       : 0.02
% 3.65/1.67  Main loop            : 0.50
% 3.65/1.67  Inferencing          : 0.19
% 3.65/1.67  Reduction            : 0.16
% 3.65/1.67  Demodulation         : 0.12
% 3.65/1.67  BG Simplification    : 0.03
% 3.65/1.67  Subsumption          : 0.09
% 3.65/1.67  Abstraction          : 0.03
% 3.65/1.67  MUC search           : 0.00
% 3.65/1.67  Cooper               : 0.00
% 3.65/1.67  Total                : 0.89
% 3.65/1.67  Index Insertion      : 0.00
% 3.65/1.67  Index Deletion       : 0.00
% 3.65/1.67  Index Matching       : 0.00
% 3.65/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
