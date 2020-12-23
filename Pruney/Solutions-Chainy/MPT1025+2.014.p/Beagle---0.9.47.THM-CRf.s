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
% DateTime   : Thu Dec  3 10:16:32 EST 2020

% Result     : Theorem 16.19s
% Output     : CNFRefutation 16.19s
% Verified   : 
% Statistics : Number of formulae       :  152 (1051 expanded)
%              Number of leaves         :   42 ( 381 expanded)
%              Depth                    :   15
%              Number of atoms          :  382 (3058 expanded)
%              Number of equality atoms :   31 ( 364 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_151,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ( m1_subset_1(F,A)
                 => ~ ( r2_hidden(F,C)
                      & E = k1_funct_1(D,F) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_132,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ~ v1_xboole_0(C)
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
                 => ! [E] :
                      ( m1_subset_1(E,A)
                     => ( r2_hidden(E,k7_relset_1(C,A,D,B))
                      <=> ? [F] :
                            ( m1_subset_1(F,C)
                            & r2_hidden(k4_tarski(F,E),D)
                            & r2_hidden(F,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(c_62,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_117,plain,(
    ! [C_158,A_159,B_160] :
      ( v1_relat_1(C_158)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_121,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_62,c_117])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_306,plain,(
    ! [A_210,B_211,C_212] :
      ( r2_hidden('#skF_3'(A_210,B_211,C_212),B_211)
      | ~ r2_hidden(A_210,k9_relat_1(C_212,B_211))
      | ~ v1_relat_1(C_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_320,plain,(
    ! [B_216,A_217,C_218] :
      ( ~ v1_xboole_0(B_216)
      | ~ r2_hidden(A_217,k9_relat_1(C_218,B_216))
      | ~ v1_relat_1(C_218) ) ),
    inference(resolution,[status(thm)],[c_306,c_2])).

tff(c_345,plain,(
    ! [B_216,C_218] :
      ( ~ v1_xboole_0(B_216)
      | ~ v1_relat_1(C_218)
      | v1_xboole_0(k9_relat_1(C_218,B_216)) ) ),
    inference(resolution,[status(thm)],[c_4,c_320])).

tff(c_528,plain,(
    ! [A_255,B_256,C_257,D_258] :
      ( k7_relset_1(A_255,B_256,C_257,D_258) = k9_relat_1(C_257,D_258)
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(A_255,B_256))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_535,plain,(
    ! [D_258] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_258) = k9_relat_1('#skF_8',D_258) ),
    inference(resolution,[status(thm)],[c_62,c_528])).

tff(c_60,plain,(
    r2_hidden('#skF_9',k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_78,plain,(
    ~ v1_xboole_0(k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(resolution,[status(thm)],[c_60,c_2])).

tff(c_537,plain,(
    ~ v1_xboole_0(k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_535,c_78])).

tff(c_555,plain,
    ( ~ v1_xboole_0('#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_345,c_537])).

tff(c_558,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_555])).

tff(c_538,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_535,c_60])).

tff(c_539,plain,(
    ! [D_259] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_259) = k9_relat_1('#skF_8',D_259) ),
    inference(resolution,[status(thm)],[c_62,c_528])).

tff(c_46,plain,(
    ! [A_36,B_37,C_38,D_39] :
      ( m1_subset_1(k7_relset_1(A_36,B_37,C_38,D_39),k1_zfmisc_1(B_37))
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_545,plain,(
    ! [D_259] :
      ( m1_subset_1(k9_relat_1('#skF_8',D_259),k1_zfmisc_1('#skF_6'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_539,c_46])).

tff(c_580,plain,(
    ! [D_263] : m1_subset_1(k9_relat_1('#skF_8',D_263),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_545])).

tff(c_18,plain,(
    ! [A_12,C_14,B_13] :
      ( m1_subset_1(A_12,C_14)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(C_14))
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_635,plain,(
    ! [A_267,D_268] :
      ( m1_subset_1(A_267,'#skF_6')
      | ~ r2_hidden(A_267,k9_relat_1('#skF_8',D_268)) ) ),
    inference(resolution,[status(thm)],[c_580,c_18])).

tff(c_659,plain,(
    m1_subset_1('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_538,c_635])).

tff(c_572,plain,(
    ! [A_260,B_261,C_262] :
      ( r2_hidden('#skF_3'(A_260,B_261,C_262),k1_relat_1(C_262))
      | ~ r2_hidden(A_260,k9_relat_1(C_262,B_261))
      | ~ v1_relat_1(C_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_665,plain,(
    ! [C_269,A_270,B_271] :
      ( ~ v1_xboole_0(k1_relat_1(C_269))
      | ~ r2_hidden(A_270,k9_relat_1(C_269,B_271))
      | ~ v1_relat_1(C_269) ) ),
    inference(resolution,[status(thm)],[c_572,c_2])).

tff(c_668,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_538,c_665])).

tff(c_691,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_668])).

tff(c_66,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_129,plain,(
    ! [C_163,B_164,A_165] :
      ( v5_relat_1(C_163,B_164)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_165,B_164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_133,plain,(
    v5_relat_1('#skF_8','#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_129])).

tff(c_1146,plain,(
    ! [B_311,C_312,A_313] :
      ( r2_hidden(k1_funct_1(B_311,C_312),A_313)
      | ~ r2_hidden(C_312,k1_relat_1(B_311))
      | ~ v1_funct_1(B_311)
      | ~ v5_relat_1(B_311,A_313)
      | ~ v1_relat_1(B_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1427,plain,(
    ! [A_333,C_334,B_335] :
      ( ~ v1_xboole_0(A_333)
      | ~ r2_hidden(C_334,k1_relat_1(B_335))
      | ~ v1_funct_1(B_335)
      | ~ v5_relat_1(B_335,A_333)
      | ~ v1_relat_1(B_335) ) ),
    inference(resolution,[status(thm)],[c_1146,c_2])).

tff(c_1463,plain,(
    ! [A_336,B_337] :
      ( ~ v1_xboole_0(A_336)
      | ~ v1_funct_1(B_337)
      | ~ v5_relat_1(B_337,A_336)
      | ~ v1_relat_1(B_337)
      | v1_xboole_0(k1_relat_1(B_337)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1427])).

tff(c_1465,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | v1_xboole_0(k1_relat_1('#skF_8')) ),
    inference(resolution,[status(thm)],[c_133,c_1463])).

tff(c_1468,plain,
    ( ~ v1_xboole_0('#skF_6')
    | v1_xboole_0(k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_66,c_1465])).

tff(c_1469,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_691,c_1468])).

tff(c_135,plain,(
    ! [C_166,A_167,B_168] :
      ( v4_relat_1(C_166,A_167)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_167,B_168))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_139,plain,(
    v4_relat_1('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_135])).

tff(c_140,plain,(
    ! [B_169,A_170] :
      ( r1_tarski(k1_relat_1(B_169),A_170)
      | ~ v4_relat_1(B_169,A_170)
      | ~ v1_relat_1(B_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_92,plain,(
    ! [A_150,B_151] :
      ( r2_hidden('#skF_2'(A_150,B_151),A_150)
      | r1_tarski(A_150,B_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_102,plain,(
    ! [A_152,B_153] :
      ( ~ v1_xboole_0(A_152)
      | r1_tarski(A_152,B_153) ) ),
    inference(resolution,[status(thm)],[c_92,c_2])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_105,plain,(
    ! [B_153,A_152] :
      ( B_153 = A_152
      | ~ r1_tarski(B_153,A_152)
      | ~ v1_xboole_0(A_152) ) ),
    inference(resolution,[status(thm)],[c_102,c_12])).

tff(c_218,plain,(
    ! [B_188,A_189] :
      ( k1_relat_1(B_188) = A_189
      | ~ v1_xboole_0(A_189)
      | ~ v4_relat_1(B_188,A_189)
      | ~ v1_relat_1(B_188) ) ),
    inference(resolution,[status(thm)],[c_140,c_105])).

tff(c_224,plain,
    ( k1_relat_1('#skF_8') = '#skF_5'
    | ~ v1_xboole_0('#skF_5')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_139,c_218])).

tff(c_229,plain,
    ( k1_relat_1('#skF_8') = '#skF_5'
    | ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_224])).

tff(c_230,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_229])).

tff(c_1860,plain,(
    ! [B_374,C_372,D_375,A_376,E_373] :
      ( r2_hidden('#skF_4'(C_372,E_373,B_374,D_375,A_376),B_374)
      | ~ r2_hidden(E_373,k7_relset_1(C_372,A_376,D_375,B_374))
      | ~ m1_subset_1(E_373,A_376)
      | ~ m1_subset_1(D_375,k1_zfmisc_1(k2_zfmisc_1(C_372,A_376)))
      | v1_xboole_0(C_372)
      | v1_xboole_0(B_374)
      | v1_xboole_0(A_376) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1865,plain,(
    ! [E_373,B_374] :
      ( r2_hidden('#skF_4'('#skF_5',E_373,B_374,'#skF_8','#skF_6'),B_374)
      | ~ r2_hidden(E_373,k7_relset_1('#skF_5','#skF_6','#skF_8',B_374))
      | ~ m1_subset_1(E_373,'#skF_6')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(B_374)
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_62,c_1860])).

tff(c_1868,plain,(
    ! [E_373,B_374] :
      ( r2_hidden('#skF_4'('#skF_5',E_373,B_374,'#skF_8','#skF_6'),B_374)
      | ~ r2_hidden(E_373,k9_relat_1('#skF_8',B_374))
      | ~ m1_subset_1(E_373,'#skF_6')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(B_374)
      | v1_xboole_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_535,c_1865])).

tff(c_5228,plain,(
    ! [E_649,B_650] :
      ( r2_hidden('#skF_4'('#skF_5',E_649,B_650,'#skF_8','#skF_6'),B_650)
      | ~ r2_hidden(E_649,k9_relat_1('#skF_8',B_650))
      | ~ m1_subset_1(E_649,'#skF_6')
      | v1_xboole_0(B_650) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1469,c_230,c_1868])).

tff(c_58,plain,(
    ! [F_142] :
      ( k1_funct_1('#skF_8',F_142) != '#skF_9'
      | ~ r2_hidden(F_142,'#skF_7')
      | ~ m1_subset_1(F_142,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_5320,plain,(
    ! [E_649] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_5',E_649,'#skF_7','#skF_8','#skF_6')) != '#skF_9'
      | ~ m1_subset_1('#skF_4'('#skF_5',E_649,'#skF_7','#skF_8','#skF_6'),'#skF_5')
      | ~ r2_hidden(E_649,k9_relat_1('#skF_8','#skF_7'))
      | ~ m1_subset_1(E_649,'#skF_6')
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_5228,c_58])).

tff(c_6244,plain,(
    ! [E_774] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_5',E_774,'#skF_7','#skF_8','#skF_6')) != '#skF_9'
      | ~ m1_subset_1('#skF_4'('#skF_5',E_774,'#skF_7','#skF_8','#skF_6'),'#skF_5')
      | ~ r2_hidden(E_774,k9_relat_1('#skF_8','#skF_7'))
      | ~ m1_subset_1(E_774,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_558,c_5320])).

tff(c_6299,plain,
    ( k1_funct_1('#skF_8','#skF_4'('#skF_5','#skF_9','#skF_7','#skF_8','#skF_6')) != '#skF_9'
    | ~ m1_subset_1('#skF_4'('#skF_5','#skF_9','#skF_7','#skF_8','#skF_6'),'#skF_5')
    | ~ m1_subset_1('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_538,c_6244])).

tff(c_6339,plain,
    ( k1_funct_1('#skF_8','#skF_4'('#skF_5','#skF_9','#skF_7','#skF_8','#skF_6')) != '#skF_9'
    | ~ m1_subset_1('#skF_4'('#skF_5','#skF_9','#skF_7','#skF_8','#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_659,c_6299])).

tff(c_15268,plain,(
    ~ m1_subset_1('#skF_4'('#skF_5','#skF_9','#skF_7','#skF_8','#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_6339])).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_30,plain,(
    ! [A_17,B_18,C_19] :
      ( r2_hidden('#skF_3'(A_17,B_18,C_19),k1_relat_1(C_19))
      | ~ r2_hidden(A_17,k9_relat_1(C_19,B_18))
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_710,plain,(
    ! [A_274,B_275,C_276] :
      ( r2_hidden(k4_tarski('#skF_3'(A_274,B_275,C_276),A_274),C_276)
      | ~ r2_hidden(A_274,k9_relat_1(C_276,B_275))
      | ~ v1_relat_1(C_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_36,plain,(
    ! [C_29,A_27,B_28] :
      ( k1_funct_1(C_29,A_27) = B_28
      | ~ r2_hidden(k4_tarski(A_27,B_28),C_29)
      | ~ v1_funct_1(C_29)
      | ~ v1_relat_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_3748,plain,(
    ! [C_553,A_554,B_555] :
      ( k1_funct_1(C_553,'#skF_3'(A_554,B_555,C_553)) = A_554
      | ~ v1_funct_1(C_553)
      | ~ r2_hidden(A_554,k9_relat_1(C_553,B_555))
      | ~ v1_relat_1(C_553) ) ),
    inference(resolution,[status(thm)],[c_710,c_36])).

tff(c_3767,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_9','#skF_7','#skF_8')) = '#skF_9'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_538,c_3748])).

tff(c_3791,plain,(
    k1_funct_1('#skF_8','#skF_3'('#skF_9','#skF_7','#skF_8')) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_66,c_3767])).

tff(c_32,plain,(
    ! [B_24,C_26,A_23] :
      ( r2_hidden(k1_funct_1(B_24,C_26),A_23)
      | ~ r2_hidden(C_26,k1_relat_1(B_24))
      | ~ v1_funct_1(B_24)
      | ~ v5_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3800,plain,(
    ! [A_23] :
      ( r2_hidden('#skF_9',A_23)
      | ~ r2_hidden('#skF_3'('#skF_9','#skF_7','#skF_8'),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v5_relat_1('#skF_8',A_23)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3791,c_32])).

tff(c_3807,plain,(
    ! [A_23] :
      ( r2_hidden('#skF_9',A_23)
      | ~ r2_hidden('#skF_3'('#skF_9','#skF_7','#skF_8'),k1_relat_1('#skF_8'))
      | ~ v5_relat_1('#skF_8',A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_66,c_3800])).

tff(c_3811,plain,(
    ~ r2_hidden('#skF_3'('#skF_9','#skF_7','#skF_8'),k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_3807])).

tff(c_3817,plain,
    ( ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_30,c_3811])).

tff(c_3824,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_538,c_3817])).

tff(c_3826,plain,(
    r2_hidden('#skF_3'('#skF_9','#skF_7','#skF_8'),k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_3807])).

tff(c_908,plain,(
    ! [A_291,C_292] :
      ( r2_hidden(k4_tarski(A_291,k1_funct_1(C_292,A_291)),C_292)
      | ~ r2_hidden(A_291,k1_relat_1(C_292))
      | ~ v1_funct_1(C_292)
      | ~ v1_relat_1(C_292) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4591,plain,(
    ! [A_608,C_609,B_610] :
      ( r2_hidden(k4_tarski(A_608,k1_funct_1(C_609,A_608)),B_610)
      | ~ r1_tarski(C_609,B_610)
      | ~ r2_hidden(A_608,k1_relat_1(C_609))
      | ~ v1_funct_1(C_609)
      | ~ v1_relat_1(C_609) ) ),
    inference(resolution,[status(thm)],[c_908,c_6])).

tff(c_4692,plain,(
    ! [B_610] :
      ( r2_hidden(k4_tarski('#skF_3'('#skF_9','#skF_7','#skF_8'),'#skF_9'),B_610)
      | ~ r1_tarski('#skF_8',B_610)
      | ~ r2_hidden('#skF_3'('#skF_9','#skF_7','#skF_8'),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3791,c_4591])).

tff(c_4723,plain,(
    ! [B_611] :
      ( r2_hidden(k4_tarski('#skF_3'('#skF_9','#skF_7','#skF_8'),'#skF_9'),B_611)
      | ~ r1_tarski('#skF_8',B_611) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_66,c_3826,c_4692])).

tff(c_38,plain,(
    ! [A_27,C_29,B_28] :
      ( r2_hidden(A_27,k1_relat_1(C_29))
      | ~ r2_hidden(k4_tarski(A_27,B_28),C_29)
      | ~ v1_funct_1(C_29)
      | ~ v1_relat_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4846,plain,(
    ! [B_611] :
      ( r2_hidden('#skF_3'('#skF_9','#skF_7','#skF_8'),k1_relat_1(B_611))
      | ~ v1_funct_1(B_611)
      | ~ v1_relat_1(B_611)
      | ~ r1_tarski('#skF_8',B_611) ) ),
    inference(resolution,[status(thm)],[c_4723,c_38])).

tff(c_4722,plain,(
    ! [B_610] :
      ( r2_hidden(k4_tarski('#skF_3'('#skF_9','#skF_7','#skF_8'),'#skF_9'),B_610)
      | ~ r1_tarski('#skF_8',B_610) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_66,c_3826,c_4692])).

tff(c_26,plain,(
    ! [A_17,B_18,C_19] :
      ( r2_hidden('#skF_3'(A_17,B_18,C_19),B_18)
      | ~ r2_hidden(A_17,k9_relat_1(C_19,B_18))
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1395,plain,(
    ! [A_327,C_328,B_329,D_330] :
      ( r2_hidden(A_327,k9_relat_1(C_328,B_329))
      | ~ r2_hidden(D_330,B_329)
      | ~ r2_hidden(k4_tarski(D_330,A_327),C_328)
      | ~ r2_hidden(D_330,k1_relat_1(C_328))
      | ~ v1_relat_1(C_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6401,plain,(
    ! [C_785,A_786,B_787,C_784,A_788] :
      ( r2_hidden(A_788,k9_relat_1(C_785,B_787))
      | ~ r2_hidden(k4_tarski('#skF_3'(A_786,B_787,C_784),A_788),C_785)
      | ~ r2_hidden('#skF_3'(A_786,B_787,C_784),k1_relat_1(C_785))
      | ~ v1_relat_1(C_785)
      | ~ r2_hidden(A_786,k9_relat_1(C_784,B_787))
      | ~ v1_relat_1(C_784) ) ),
    inference(resolution,[status(thm)],[c_26,c_1395])).

tff(c_6410,plain,(
    ! [B_610] :
      ( r2_hidden('#skF_9',k9_relat_1(B_610,'#skF_7'))
      | ~ r2_hidden('#skF_3'('#skF_9','#skF_7','#skF_8'),k1_relat_1(B_610))
      | ~ v1_relat_1(B_610)
      | ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7'))
      | ~ v1_relat_1('#skF_8')
      | ~ r1_tarski('#skF_8',B_610) ) ),
    inference(resolution,[status(thm)],[c_4722,c_6401])).

tff(c_14079,plain,(
    ! [B_1494] :
      ( r2_hidden('#skF_9',k9_relat_1(B_1494,'#skF_7'))
      | ~ r2_hidden('#skF_3'('#skF_9','#skF_7','#skF_8'),k1_relat_1(B_1494))
      | ~ v1_relat_1(B_1494)
      | ~ r1_tarski('#skF_8',B_1494) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_538,c_6410])).

tff(c_14107,plain,(
    ! [B_611] :
      ( r2_hidden('#skF_9',k9_relat_1(B_611,'#skF_7'))
      | ~ v1_funct_1(B_611)
      | ~ v1_relat_1(B_611)
      | ~ r1_tarski('#skF_8',B_611) ) ),
    inference(resolution,[status(thm)],[c_4846,c_14079])).

tff(c_1523,plain,(
    ! [D_343,E_341,A_344,C_340,B_342] :
      ( m1_subset_1('#skF_4'(C_340,E_341,B_342,D_343,A_344),C_340)
      | ~ r2_hidden(E_341,k7_relset_1(C_340,A_344,D_343,B_342))
      | ~ m1_subset_1(E_341,A_344)
      | ~ m1_subset_1(D_343,k1_zfmisc_1(k2_zfmisc_1(C_340,A_344)))
      | v1_xboole_0(C_340)
      | v1_xboole_0(B_342)
      | v1_xboole_0(A_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1534,plain,(
    ! [E_341,D_258] :
      ( m1_subset_1('#skF_4'('#skF_5',E_341,D_258,'#skF_8','#skF_6'),'#skF_5')
      | ~ r2_hidden(E_341,k9_relat_1('#skF_8',D_258))
      | ~ m1_subset_1(E_341,'#skF_6')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(D_258)
      | v1_xboole_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_535,c_1523])).

tff(c_1554,plain,(
    ! [E_341,D_258] :
      ( m1_subset_1('#skF_4'('#skF_5',E_341,D_258,'#skF_8','#skF_6'),'#skF_5')
      | ~ r2_hidden(E_341,k9_relat_1('#skF_8',D_258))
      | ~ m1_subset_1(E_341,'#skF_6')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(D_258)
      | v1_xboole_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1534])).

tff(c_18203,plain,(
    ! [E_1719,D_1720] :
      ( m1_subset_1('#skF_4'('#skF_5',E_1719,D_1720,'#skF_8','#skF_6'),'#skF_5')
      | ~ r2_hidden(E_1719,k9_relat_1('#skF_8',D_1720))
      | ~ m1_subset_1(E_1719,'#skF_6')
      | v1_xboole_0(D_1720) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1469,c_230,c_1554])).

tff(c_18223,plain,
    ( m1_subset_1('#skF_4'('#skF_5','#skF_9','#skF_7','#skF_8','#skF_6'),'#skF_5')
    | ~ m1_subset_1('#skF_9','#skF_6')
    | v1_xboole_0('#skF_7')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ r1_tarski('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_14107,c_18203])).

tff(c_18342,plain,
    ( m1_subset_1('#skF_4'('#skF_5','#skF_9','#skF_7','#skF_8','#skF_6'),'#skF_5')
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_121,c_66,c_659,c_18223])).

tff(c_18344,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_558,c_15268,c_18342])).

tff(c_18345,plain,(
    k1_funct_1('#skF_8','#skF_4'('#skF_5','#skF_9','#skF_7','#skF_8','#skF_6')) != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_6339])).

tff(c_2109,plain,(
    ! [A_408,D_407,B_406,C_404,E_405] :
      ( r2_hidden(k4_tarski('#skF_4'(C_404,E_405,B_406,D_407,A_408),E_405),D_407)
      | ~ r2_hidden(E_405,k7_relset_1(C_404,A_408,D_407,B_406))
      | ~ m1_subset_1(E_405,A_408)
      | ~ m1_subset_1(D_407,k1_zfmisc_1(k2_zfmisc_1(C_404,A_408)))
      | v1_xboole_0(C_404)
      | v1_xboole_0(B_406)
      | v1_xboole_0(A_408) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_8172,plain,(
    ! [D_966,A_968,C_967,B_970,E_969] :
      ( k1_funct_1(D_966,'#skF_4'(C_967,E_969,B_970,D_966,A_968)) = E_969
      | ~ v1_funct_1(D_966)
      | ~ v1_relat_1(D_966)
      | ~ r2_hidden(E_969,k7_relset_1(C_967,A_968,D_966,B_970))
      | ~ m1_subset_1(E_969,A_968)
      | ~ m1_subset_1(D_966,k1_zfmisc_1(k2_zfmisc_1(C_967,A_968)))
      | v1_xboole_0(C_967)
      | v1_xboole_0(B_970)
      | v1_xboole_0(A_968) ) ),
    inference(resolution,[status(thm)],[c_2109,c_36])).

tff(c_8216,plain,(
    ! [E_969,D_258] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_5',E_969,D_258,'#skF_8','#skF_6')) = E_969
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(E_969,k9_relat_1('#skF_8',D_258))
      | ~ m1_subset_1(E_969,'#skF_6')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(D_258)
      | v1_xboole_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_535,c_8172])).

tff(c_8247,plain,(
    ! [E_969,D_258] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_5',E_969,D_258,'#skF_8','#skF_6')) = E_969
      | ~ r2_hidden(E_969,k9_relat_1('#skF_8',D_258))
      | ~ m1_subset_1(E_969,'#skF_6')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(D_258)
      | v1_xboole_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_121,c_66,c_8216])).

tff(c_23012,plain,(
    ! [E_2007,D_2008] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_5',E_2007,D_2008,'#skF_8','#skF_6')) = E_2007
      | ~ r2_hidden(E_2007,k9_relat_1('#skF_8',D_2008))
      | ~ m1_subset_1(E_2007,'#skF_6')
      | v1_xboole_0(D_2008) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1469,c_230,c_8247])).

tff(c_23044,plain,
    ( k1_funct_1('#skF_8','#skF_4'('#skF_5','#skF_9','#skF_7','#skF_8','#skF_6')) = '#skF_9'
    | ~ m1_subset_1('#skF_9','#skF_6')
    | v1_xboole_0('#skF_7')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ r1_tarski('#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_14107,c_23012])).

tff(c_23168,plain,
    ( k1_funct_1('#skF_8','#skF_4'('#skF_5','#skF_9','#skF_7','#skF_8','#skF_6')) = '#skF_9'
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_121,c_66,c_659,c_23044])).

tff(c_23170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_558,c_18345,c_23168])).

tff(c_23172,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_229])).

tff(c_23171,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_229])).

tff(c_23622,plain,(
    ! [A_2068,B_2069,C_2070,D_2071] :
      ( k7_relset_1(A_2068,B_2069,C_2070,D_2071) = k9_relat_1(C_2070,D_2071)
      | ~ m1_subset_1(C_2070,k1_zfmisc_1(k2_zfmisc_1(A_2068,B_2069))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_23625,plain,(
    ! [D_2071] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_2071) = k9_relat_1('#skF_8',D_2071) ),
    inference(resolution,[status(thm)],[c_62,c_23622])).

tff(c_23670,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23625,c_60])).

tff(c_23471,plain,(
    ! [A_2052,B_2053,C_2054] :
      ( r2_hidden('#skF_3'(A_2052,B_2053,C_2054),k1_relat_1(C_2054))
      | ~ r2_hidden(A_2052,k9_relat_1(C_2054,B_2053))
      | ~ v1_relat_1(C_2054) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_24202,plain,(
    ! [C_2109,A_2110,B_2111] :
      ( ~ v1_xboole_0(k1_relat_1(C_2109))
      | ~ r2_hidden(A_2110,k9_relat_1(C_2109,B_2111))
      | ~ v1_relat_1(C_2109) ) ),
    inference(resolution,[status(thm)],[c_23471,c_2])).

tff(c_24213,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_23670,c_24202])).

tff(c_24242,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_23172,c_23171,c_24213])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:20:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.19/7.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.19/7.12  
% 16.19/7.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.19/7.12  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_2
% 16.19/7.12  
% 16.19/7.12  %Foreground sorts:
% 16.19/7.12  
% 16.19/7.12  
% 16.19/7.12  %Background operators:
% 16.19/7.12  
% 16.19/7.12  
% 16.19/7.12  %Foreground operators:
% 16.19/7.12  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 16.19/7.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.19/7.12  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.19/7.12  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 16.19/7.12  tff('#skF_1', type, '#skF_1': $i > $i).
% 16.19/7.12  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 16.19/7.12  tff('#skF_7', type, '#skF_7': $i).
% 16.19/7.12  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.19/7.12  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 16.19/7.12  tff('#skF_5', type, '#skF_5': $i).
% 16.19/7.12  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 16.19/7.12  tff('#skF_6', type, '#skF_6': $i).
% 16.19/7.12  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 16.19/7.12  tff('#skF_9', type, '#skF_9': $i).
% 16.19/7.12  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 16.19/7.12  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.19/7.12  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 16.19/7.12  tff('#skF_8', type, '#skF_8': $i).
% 16.19/7.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.19/7.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 16.19/7.12  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 16.19/7.12  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 16.19/7.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.19/7.12  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 16.19/7.12  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 16.19/7.12  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 16.19/7.12  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 16.19/7.12  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.19/7.12  
% 16.19/7.14  tff(f_151, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 16.19/7.14  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 16.19/7.14  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 16.19/7.14  tff(f_67, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 16.19/7.14  tff(f_106, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 16.19/7.14  tff(f_102, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 16.19/7.14  tff(f_50, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 16.19/7.14  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 16.19/7.14  tff(f_78, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 16.19/7.14  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 16.19/7.14  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 16.19/7.14  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 16.19/7.14  tff(f_132, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k7_relset_1(C, A, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(F, E), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relset_1)).
% 16.19/7.14  tff(f_88, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 16.19/7.14  tff(c_62, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 16.19/7.14  tff(c_117, plain, (![C_158, A_159, B_160]: (v1_relat_1(C_158) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 16.19/7.14  tff(c_121, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_62, c_117])).
% 16.19/7.14  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.19/7.14  tff(c_306, plain, (![A_210, B_211, C_212]: (r2_hidden('#skF_3'(A_210, B_211, C_212), B_211) | ~r2_hidden(A_210, k9_relat_1(C_212, B_211)) | ~v1_relat_1(C_212))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.19/7.14  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.19/7.14  tff(c_320, plain, (![B_216, A_217, C_218]: (~v1_xboole_0(B_216) | ~r2_hidden(A_217, k9_relat_1(C_218, B_216)) | ~v1_relat_1(C_218))), inference(resolution, [status(thm)], [c_306, c_2])).
% 16.19/7.14  tff(c_345, plain, (![B_216, C_218]: (~v1_xboole_0(B_216) | ~v1_relat_1(C_218) | v1_xboole_0(k9_relat_1(C_218, B_216)))), inference(resolution, [status(thm)], [c_4, c_320])).
% 16.19/7.14  tff(c_528, plain, (![A_255, B_256, C_257, D_258]: (k7_relset_1(A_255, B_256, C_257, D_258)=k9_relat_1(C_257, D_258) | ~m1_subset_1(C_257, k1_zfmisc_1(k2_zfmisc_1(A_255, B_256))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 16.19/7.14  tff(c_535, plain, (![D_258]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_258)=k9_relat_1('#skF_8', D_258))), inference(resolution, [status(thm)], [c_62, c_528])).
% 16.19/7.14  tff(c_60, plain, (r2_hidden('#skF_9', k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 16.19/7.14  tff(c_78, plain, (~v1_xboole_0(k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(resolution, [status(thm)], [c_60, c_2])).
% 16.19/7.14  tff(c_537, plain, (~v1_xboole_0(k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_535, c_78])).
% 16.19/7.14  tff(c_555, plain, (~v1_xboole_0('#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_345, c_537])).
% 16.19/7.14  tff(c_558, plain, (~v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_555])).
% 16.19/7.14  tff(c_538, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_535, c_60])).
% 16.19/7.14  tff(c_539, plain, (![D_259]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_259)=k9_relat_1('#skF_8', D_259))), inference(resolution, [status(thm)], [c_62, c_528])).
% 16.19/7.14  tff(c_46, plain, (![A_36, B_37, C_38, D_39]: (m1_subset_1(k7_relset_1(A_36, B_37, C_38, D_39), k1_zfmisc_1(B_37)) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 16.19/7.14  tff(c_545, plain, (![D_259]: (m1_subset_1(k9_relat_1('#skF_8', D_259), k1_zfmisc_1('#skF_6')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_539, c_46])).
% 16.19/7.14  tff(c_580, plain, (![D_263]: (m1_subset_1(k9_relat_1('#skF_8', D_263), k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_545])).
% 16.19/7.14  tff(c_18, plain, (![A_12, C_14, B_13]: (m1_subset_1(A_12, C_14) | ~m1_subset_1(B_13, k1_zfmisc_1(C_14)) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_50])).
% 16.19/7.14  tff(c_635, plain, (![A_267, D_268]: (m1_subset_1(A_267, '#skF_6') | ~r2_hidden(A_267, k9_relat_1('#skF_8', D_268)))), inference(resolution, [status(thm)], [c_580, c_18])).
% 16.19/7.14  tff(c_659, plain, (m1_subset_1('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_538, c_635])).
% 16.19/7.14  tff(c_572, plain, (![A_260, B_261, C_262]: (r2_hidden('#skF_3'(A_260, B_261, C_262), k1_relat_1(C_262)) | ~r2_hidden(A_260, k9_relat_1(C_262, B_261)) | ~v1_relat_1(C_262))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.19/7.14  tff(c_665, plain, (![C_269, A_270, B_271]: (~v1_xboole_0(k1_relat_1(C_269)) | ~r2_hidden(A_270, k9_relat_1(C_269, B_271)) | ~v1_relat_1(C_269))), inference(resolution, [status(thm)], [c_572, c_2])).
% 16.19/7.14  tff(c_668, plain, (~v1_xboole_0(k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_538, c_665])).
% 16.19/7.14  tff(c_691, plain, (~v1_xboole_0(k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_668])).
% 16.19/7.14  tff(c_66, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_151])).
% 16.19/7.14  tff(c_129, plain, (![C_163, B_164, A_165]: (v5_relat_1(C_163, B_164) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_165, B_164))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 16.19/7.14  tff(c_133, plain, (v5_relat_1('#skF_8', '#skF_6')), inference(resolution, [status(thm)], [c_62, c_129])).
% 16.19/7.14  tff(c_1146, plain, (![B_311, C_312, A_313]: (r2_hidden(k1_funct_1(B_311, C_312), A_313) | ~r2_hidden(C_312, k1_relat_1(B_311)) | ~v1_funct_1(B_311) | ~v5_relat_1(B_311, A_313) | ~v1_relat_1(B_311))), inference(cnfTransformation, [status(thm)], [f_78])).
% 16.19/7.14  tff(c_1427, plain, (![A_333, C_334, B_335]: (~v1_xboole_0(A_333) | ~r2_hidden(C_334, k1_relat_1(B_335)) | ~v1_funct_1(B_335) | ~v5_relat_1(B_335, A_333) | ~v1_relat_1(B_335))), inference(resolution, [status(thm)], [c_1146, c_2])).
% 16.19/7.14  tff(c_1463, plain, (![A_336, B_337]: (~v1_xboole_0(A_336) | ~v1_funct_1(B_337) | ~v5_relat_1(B_337, A_336) | ~v1_relat_1(B_337) | v1_xboole_0(k1_relat_1(B_337)))), inference(resolution, [status(thm)], [c_4, c_1427])).
% 16.19/7.14  tff(c_1465, plain, (~v1_xboole_0('#skF_6') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | v1_xboole_0(k1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_133, c_1463])).
% 16.19/7.14  tff(c_1468, plain, (~v1_xboole_0('#skF_6') | v1_xboole_0(k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_66, c_1465])).
% 16.19/7.14  tff(c_1469, plain, (~v1_xboole_0('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_691, c_1468])).
% 16.19/7.14  tff(c_135, plain, (![C_166, A_167, B_168]: (v4_relat_1(C_166, A_167) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_167, B_168))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 16.19/7.14  tff(c_139, plain, (v4_relat_1('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_62, c_135])).
% 16.19/7.14  tff(c_140, plain, (![B_169, A_170]: (r1_tarski(k1_relat_1(B_169), A_170) | ~v4_relat_1(B_169, A_170) | ~v1_relat_1(B_169))), inference(cnfTransformation, [status(thm)], [f_56])).
% 16.19/7.14  tff(c_92, plain, (![A_150, B_151]: (r2_hidden('#skF_2'(A_150, B_151), A_150) | r1_tarski(A_150, B_151))), inference(cnfTransformation, [status(thm)], [f_38])).
% 16.19/7.14  tff(c_102, plain, (![A_152, B_153]: (~v1_xboole_0(A_152) | r1_tarski(A_152, B_153))), inference(resolution, [status(thm)], [c_92, c_2])).
% 16.19/7.14  tff(c_12, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 16.19/7.14  tff(c_105, plain, (![B_153, A_152]: (B_153=A_152 | ~r1_tarski(B_153, A_152) | ~v1_xboole_0(A_152))), inference(resolution, [status(thm)], [c_102, c_12])).
% 16.19/7.14  tff(c_218, plain, (![B_188, A_189]: (k1_relat_1(B_188)=A_189 | ~v1_xboole_0(A_189) | ~v4_relat_1(B_188, A_189) | ~v1_relat_1(B_188))), inference(resolution, [status(thm)], [c_140, c_105])).
% 16.19/7.14  tff(c_224, plain, (k1_relat_1('#skF_8')='#skF_5' | ~v1_xboole_0('#skF_5') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_139, c_218])).
% 16.19/7.14  tff(c_229, plain, (k1_relat_1('#skF_8')='#skF_5' | ~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_121, c_224])).
% 16.19/7.14  tff(c_230, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_229])).
% 16.19/7.14  tff(c_1860, plain, (![B_374, C_372, D_375, A_376, E_373]: (r2_hidden('#skF_4'(C_372, E_373, B_374, D_375, A_376), B_374) | ~r2_hidden(E_373, k7_relset_1(C_372, A_376, D_375, B_374)) | ~m1_subset_1(E_373, A_376) | ~m1_subset_1(D_375, k1_zfmisc_1(k2_zfmisc_1(C_372, A_376))) | v1_xboole_0(C_372) | v1_xboole_0(B_374) | v1_xboole_0(A_376))), inference(cnfTransformation, [status(thm)], [f_132])).
% 16.19/7.14  tff(c_1865, plain, (![E_373, B_374]: (r2_hidden('#skF_4'('#skF_5', E_373, B_374, '#skF_8', '#skF_6'), B_374) | ~r2_hidden(E_373, k7_relset_1('#skF_5', '#skF_6', '#skF_8', B_374)) | ~m1_subset_1(E_373, '#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0(B_374) | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_62, c_1860])).
% 16.19/7.14  tff(c_1868, plain, (![E_373, B_374]: (r2_hidden('#skF_4'('#skF_5', E_373, B_374, '#skF_8', '#skF_6'), B_374) | ~r2_hidden(E_373, k9_relat_1('#skF_8', B_374)) | ~m1_subset_1(E_373, '#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0(B_374) | v1_xboole_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_535, c_1865])).
% 16.19/7.14  tff(c_5228, plain, (![E_649, B_650]: (r2_hidden('#skF_4'('#skF_5', E_649, B_650, '#skF_8', '#skF_6'), B_650) | ~r2_hidden(E_649, k9_relat_1('#skF_8', B_650)) | ~m1_subset_1(E_649, '#skF_6') | v1_xboole_0(B_650))), inference(negUnitSimplification, [status(thm)], [c_1469, c_230, c_1868])).
% 16.19/7.14  tff(c_58, plain, (![F_142]: (k1_funct_1('#skF_8', F_142)!='#skF_9' | ~r2_hidden(F_142, '#skF_7') | ~m1_subset_1(F_142, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 16.19/7.14  tff(c_5320, plain, (![E_649]: (k1_funct_1('#skF_8', '#skF_4'('#skF_5', E_649, '#skF_7', '#skF_8', '#skF_6'))!='#skF_9' | ~m1_subset_1('#skF_4'('#skF_5', E_649, '#skF_7', '#skF_8', '#skF_6'), '#skF_5') | ~r2_hidden(E_649, k9_relat_1('#skF_8', '#skF_7')) | ~m1_subset_1(E_649, '#skF_6') | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_5228, c_58])).
% 16.19/7.14  tff(c_6244, plain, (![E_774]: (k1_funct_1('#skF_8', '#skF_4'('#skF_5', E_774, '#skF_7', '#skF_8', '#skF_6'))!='#skF_9' | ~m1_subset_1('#skF_4'('#skF_5', E_774, '#skF_7', '#skF_8', '#skF_6'), '#skF_5') | ~r2_hidden(E_774, k9_relat_1('#skF_8', '#skF_7')) | ~m1_subset_1(E_774, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_558, c_5320])).
% 16.19/7.14  tff(c_6299, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_5', '#skF_9', '#skF_7', '#skF_8', '#skF_6'))!='#skF_9' | ~m1_subset_1('#skF_4'('#skF_5', '#skF_9', '#skF_7', '#skF_8', '#skF_6'), '#skF_5') | ~m1_subset_1('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_538, c_6244])).
% 16.19/7.14  tff(c_6339, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_5', '#skF_9', '#skF_7', '#skF_8', '#skF_6'))!='#skF_9' | ~m1_subset_1('#skF_4'('#skF_5', '#skF_9', '#skF_7', '#skF_8', '#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_659, c_6299])).
% 16.19/7.14  tff(c_15268, plain, (~m1_subset_1('#skF_4'('#skF_5', '#skF_9', '#skF_7', '#skF_8', '#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_6339])).
% 16.19/7.14  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 16.19/7.14  tff(c_30, plain, (![A_17, B_18, C_19]: (r2_hidden('#skF_3'(A_17, B_18, C_19), k1_relat_1(C_19)) | ~r2_hidden(A_17, k9_relat_1(C_19, B_18)) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.19/7.14  tff(c_710, plain, (![A_274, B_275, C_276]: (r2_hidden(k4_tarski('#skF_3'(A_274, B_275, C_276), A_274), C_276) | ~r2_hidden(A_274, k9_relat_1(C_276, B_275)) | ~v1_relat_1(C_276))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.19/7.14  tff(c_36, plain, (![C_29, A_27, B_28]: (k1_funct_1(C_29, A_27)=B_28 | ~r2_hidden(k4_tarski(A_27, B_28), C_29) | ~v1_funct_1(C_29) | ~v1_relat_1(C_29))), inference(cnfTransformation, [status(thm)], [f_88])).
% 16.19/7.14  tff(c_3748, plain, (![C_553, A_554, B_555]: (k1_funct_1(C_553, '#skF_3'(A_554, B_555, C_553))=A_554 | ~v1_funct_1(C_553) | ~r2_hidden(A_554, k9_relat_1(C_553, B_555)) | ~v1_relat_1(C_553))), inference(resolution, [status(thm)], [c_710, c_36])).
% 16.19/7.14  tff(c_3767, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_9', '#skF_7', '#skF_8'))='#skF_9' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_538, c_3748])).
% 16.19/7.14  tff(c_3791, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_9', '#skF_7', '#skF_8'))='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_121, c_66, c_3767])).
% 16.19/7.14  tff(c_32, plain, (![B_24, C_26, A_23]: (r2_hidden(k1_funct_1(B_24, C_26), A_23) | ~r2_hidden(C_26, k1_relat_1(B_24)) | ~v1_funct_1(B_24) | ~v5_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_78])).
% 16.19/7.14  tff(c_3800, plain, (![A_23]: (r2_hidden('#skF_9', A_23) | ~r2_hidden('#skF_3'('#skF_9', '#skF_7', '#skF_8'), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v5_relat_1('#skF_8', A_23) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_3791, c_32])).
% 16.19/7.14  tff(c_3807, plain, (![A_23]: (r2_hidden('#skF_9', A_23) | ~r2_hidden('#skF_3'('#skF_9', '#skF_7', '#skF_8'), k1_relat_1('#skF_8')) | ~v5_relat_1('#skF_8', A_23))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_66, c_3800])).
% 16.19/7.14  tff(c_3811, plain, (~r2_hidden('#skF_3'('#skF_9', '#skF_7', '#skF_8'), k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_3807])).
% 16.19/7.14  tff(c_3817, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_30, c_3811])).
% 16.19/7.14  tff(c_3824, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121, c_538, c_3817])).
% 16.19/7.14  tff(c_3826, plain, (r2_hidden('#skF_3'('#skF_9', '#skF_7', '#skF_8'), k1_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_3807])).
% 16.19/7.14  tff(c_908, plain, (![A_291, C_292]: (r2_hidden(k4_tarski(A_291, k1_funct_1(C_292, A_291)), C_292) | ~r2_hidden(A_291, k1_relat_1(C_292)) | ~v1_funct_1(C_292) | ~v1_relat_1(C_292))), inference(cnfTransformation, [status(thm)], [f_88])).
% 16.19/7.14  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 16.19/7.14  tff(c_4591, plain, (![A_608, C_609, B_610]: (r2_hidden(k4_tarski(A_608, k1_funct_1(C_609, A_608)), B_610) | ~r1_tarski(C_609, B_610) | ~r2_hidden(A_608, k1_relat_1(C_609)) | ~v1_funct_1(C_609) | ~v1_relat_1(C_609))), inference(resolution, [status(thm)], [c_908, c_6])).
% 16.19/7.14  tff(c_4692, plain, (![B_610]: (r2_hidden(k4_tarski('#skF_3'('#skF_9', '#skF_7', '#skF_8'), '#skF_9'), B_610) | ~r1_tarski('#skF_8', B_610) | ~r2_hidden('#skF_3'('#skF_9', '#skF_7', '#skF_8'), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_3791, c_4591])).
% 16.19/7.14  tff(c_4723, plain, (![B_611]: (r2_hidden(k4_tarski('#skF_3'('#skF_9', '#skF_7', '#skF_8'), '#skF_9'), B_611) | ~r1_tarski('#skF_8', B_611))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_66, c_3826, c_4692])).
% 16.19/7.14  tff(c_38, plain, (![A_27, C_29, B_28]: (r2_hidden(A_27, k1_relat_1(C_29)) | ~r2_hidden(k4_tarski(A_27, B_28), C_29) | ~v1_funct_1(C_29) | ~v1_relat_1(C_29))), inference(cnfTransformation, [status(thm)], [f_88])).
% 16.19/7.14  tff(c_4846, plain, (![B_611]: (r2_hidden('#skF_3'('#skF_9', '#skF_7', '#skF_8'), k1_relat_1(B_611)) | ~v1_funct_1(B_611) | ~v1_relat_1(B_611) | ~r1_tarski('#skF_8', B_611))), inference(resolution, [status(thm)], [c_4723, c_38])).
% 16.19/7.14  tff(c_4722, plain, (![B_610]: (r2_hidden(k4_tarski('#skF_3'('#skF_9', '#skF_7', '#skF_8'), '#skF_9'), B_610) | ~r1_tarski('#skF_8', B_610))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_66, c_3826, c_4692])).
% 16.19/7.14  tff(c_26, plain, (![A_17, B_18, C_19]: (r2_hidden('#skF_3'(A_17, B_18, C_19), B_18) | ~r2_hidden(A_17, k9_relat_1(C_19, B_18)) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.19/7.14  tff(c_1395, plain, (![A_327, C_328, B_329, D_330]: (r2_hidden(A_327, k9_relat_1(C_328, B_329)) | ~r2_hidden(D_330, B_329) | ~r2_hidden(k4_tarski(D_330, A_327), C_328) | ~r2_hidden(D_330, k1_relat_1(C_328)) | ~v1_relat_1(C_328))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.19/7.14  tff(c_6401, plain, (![C_785, A_786, B_787, C_784, A_788]: (r2_hidden(A_788, k9_relat_1(C_785, B_787)) | ~r2_hidden(k4_tarski('#skF_3'(A_786, B_787, C_784), A_788), C_785) | ~r2_hidden('#skF_3'(A_786, B_787, C_784), k1_relat_1(C_785)) | ~v1_relat_1(C_785) | ~r2_hidden(A_786, k9_relat_1(C_784, B_787)) | ~v1_relat_1(C_784))), inference(resolution, [status(thm)], [c_26, c_1395])).
% 16.19/7.14  tff(c_6410, plain, (![B_610]: (r2_hidden('#skF_9', k9_relat_1(B_610, '#skF_7')) | ~r2_hidden('#skF_3'('#skF_9', '#skF_7', '#skF_8'), k1_relat_1(B_610)) | ~v1_relat_1(B_610) | ~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7')) | ~v1_relat_1('#skF_8') | ~r1_tarski('#skF_8', B_610))), inference(resolution, [status(thm)], [c_4722, c_6401])).
% 16.19/7.14  tff(c_14079, plain, (![B_1494]: (r2_hidden('#skF_9', k9_relat_1(B_1494, '#skF_7')) | ~r2_hidden('#skF_3'('#skF_9', '#skF_7', '#skF_8'), k1_relat_1(B_1494)) | ~v1_relat_1(B_1494) | ~r1_tarski('#skF_8', B_1494))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_538, c_6410])).
% 16.19/7.14  tff(c_14107, plain, (![B_611]: (r2_hidden('#skF_9', k9_relat_1(B_611, '#skF_7')) | ~v1_funct_1(B_611) | ~v1_relat_1(B_611) | ~r1_tarski('#skF_8', B_611))), inference(resolution, [status(thm)], [c_4846, c_14079])).
% 16.19/7.14  tff(c_1523, plain, (![D_343, E_341, A_344, C_340, B_342]: (m1_subset_1('#skF_4'(C_340, E_341, B_342, D_343, A_344), C_340) | ~r2_hidden(E_341, k7_relset_1(C_340, A_344, D_343, B_342)) | ~m1_subset_1(E_341, A_344) | ~m1_subset_1(D_343, k1_zfmisc_1(k2_zfmisc_1(C_340, A_344))) | v1_xboole_0(C_340) | v1_xboole_0(B_342) | v1_xboole_0(A_344))), inference(cnfTransformation, [status(thm)], [f_132])).
% 16.19/7.14  tff(c_1534, plain, (![E_341, D_258]: (m1_subset_1('#skF_4'('#skF_5', E_341, D_258, '#skF_8', '#skF_6'), '#skF_5') | ~r2_hidden(E_341, k9_relat_1('#skF_8', D_258)) | ~m1_subset_1(E_341, '#skF_6') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | v1_xboole_0('#skF_5') | v1_xboole_0(D_258) | v1_xboole_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_535, c_1523])).
% 16.19/7.14  tff(c_1554, plain, (![E_341, D_258]: (m1_subset_1('#skF_4'('#skF_5', E_341, D_258, '#skF_8', '#skF_6'), '#skF_5') | ~r2_hidden(E_341, k9_relat_1('#skF_8', D_258)) | ~m1_subset_1(E_341, '#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0(D_258) | v1_xboole_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1534])).
% 16.19/7.14  tff(c_18203, plain, (![E_1719, D_1720]: (m1_subset_1('#skF_4'('#skF_5', E_1719, D_1720, '#skF_8', '#skF_6'), '#skF_5') | ~r2_hidden(E_1719, k9_relat_1('#skF_8', D_1720)) | ~m1_subset_1(E_1719, '#skF_6') | v1_xboole_0(D_1720))), inference(negUnitSimplification, [status(thm)], [c_1469, c_230, c_1554])).
% 16.19/7.14  tff(c_18223, plain, (m1_subset_1('#skF_4'('#skF_5', '#skF_9', '#skF_7', '#skF_8', '#skF_6'), '#skF_5') | ~m1_subset_1('#skF_9', '#skF_6') | v1_xboole_0('#skF_7') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski('#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_14107, c_18203])).
% 16.19/7.14  tff(c_18342, plain, (m1_subset_1('#skF_4'('#skF_5', '#skF_9', '#skF_7', '#skF_8', '#skF_6'), '#skF_5') | v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_121, c_66, c_659, c_18223])).
% 16.19/7.14  tff(c_18344, plain, $false, inference(negUnitSimplification, [status(thm)], [c_558, c_15268, c_18342])).
% 16.19/7.14  tff(c_18345, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_5', '#skF_9', '#skF_7', '#skF_8', '#skF_6'))!='#skF_9'), inference(splitRight, [status(thm)], [c_6339])).
% 16.19/7.14  tff(c_2109, plain, (![A_408, D_407, B_406, C_404, E_405]: (r2_hidden(k4_tarski('#skF_4'(C_404, E_405, B_406, D_407, A_408), E_405), D_407) | ~r2_hidden(E_405, k7_relset_1(C_404, A_408, D_407, B_406)) | ~m1_subset_1(E_405, A_408) | ~m1_subset_1(D_407, k1_zfmisc_1(k2_zfmisc_1(C_404, A_408))) | v1_xboole_0(C_404) | v1_xboole_0(B_406) | v1_xboole_0(A_408))), inference(cnfTransformation, [status(thm)], [f_132])).
% 16.19/7.14  tff(c_8172, plain, (![D_966, A_968, C_967, B_970, E_969]: (k1_funct_1(D_966, '#skF_4'(C_967, E_969, B_970, D_966, A_968))=E_969 | ~v1_funct_1(D_966) | ~v1_relat_1(D_966) | ~r2_hidden(E_969, k7_relset_1(C_967, A_968, D_966, B_970)) | ~m1_subset_1(E_969, A_968) | ~m1_subset_1(D_966, k1_zfmisc_1(k2_zfmisc_1(C_967, A_968))) | v1_xboole_0(C_967) | v1_xboole_0(B_970) | v1_xboole_0(A_968))), inference(resolution, [status(thm)], [c_2109, c_36])).
% 16.19/7.14  tff(c_8216, plain, (![E_969, D_258]: (k1_funct_1('#skF_8', '#skF_4'('#skF_5', E_969, D_258, '#skF_8', '#skF_6'))=E_969 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(E_969, k9_relat_1('#skF_8', D_258)) | ~m1_subset_1(E_969, '#skF_6') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | v1_xboole_0('#skF_5') | v1_xboole_0(D_258) | v1_xboole_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_535, c_8172])).
% 16.19/7.14  tff(c_8247, plain, (![E_969, D_258]: (k1_funct_1('#skF_8', '#skF_4'('#skF_5', E_969, D_258, '#skF_8', '#skF_6'))=E_969 | ~r2_hidden(E_969, k9_relat_1('#skF_8', D_258)) | ~m1_subset_1(E_969, '#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0(D_258) | v1_xboole_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_121, c_66, c_8216])).
% 16.19/7.14  tff(c_23012, plain, (![E_2007, D_2008]: (k1_funct_1('#skF_8', '#skF_4'('#skF_5', E_2007, D_2008, '#skF_8', '#skF_6'))=E_2007 | ~r2_hidden(E_2007, k9_relat_1('#skF_8', D_2008)) | ~m1_subset_1(E_2007, '#skF_6') | v1_xboole_0(D_2008))), inference(negUnitSimplification, [status(thm)], [c_1469, c_230, c_8247])).
% 16.19/7.14  tff(c_23044, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_5', '#skF_9', '#skF_7', '#skF_8', '#skF_6'))='#skF_9' | ~m1_subset_1('#skF_9', '#skF_6') | v1_xboole_0('#skF_7') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski('#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_14107, c_23012])).
% 16.19/7.14  tff(c_23168, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_5', '#skF_9', '#skF_7', '#skF_8', '#skF_6'))='#skF_9' | v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_121, c_66, c_659, c_23044])).
% 16.19/7.14  tff(c_23170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_558, c_18345, c_23168])).
% 16.19/7.14  tff(c_23172, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_229])).
% 16.19/7.14  tff(c_23171, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitRight, [status(thm)], [c_229])).
% 16.19/7.14  tff(c_23622, plain, (![A_2068, B_2069, C_2070, D_2071]: (k7_relset_1(A_2068, B_2069, C_2070, D_2071)=k9_relat_1(C_2070, D_2071) | ~m1_subset_1(C_2070, k1_zfmisc_1(k2_zfmisc_1(A_2068, B_2069))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 16.19/7.14  tff(c_23625, plain, (![D_2071]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_2071)=k9_relat_1('#skF_8', D_2071))), inference(resolution, [status(thm)], [c_62, c_23622])).
% 16.19/7.14  tff(c_23670, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_23625, c_60])).
% 16.19/7.14  tff(c_23471, plain, (![A_2052, B_2053, C_2054]: (r2_hidden('#skF_3'(A_2052, B_2053, C_2054), k1_relat_1(C_2054)) | ~r2_hidden(A_2052, k9_relat_1(C_2054, B_2053)) | ~v1_relat_1(C_2054))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.19/7.14  tff(c_24202, plain, (![C_2109, A_2110, B_2111]: (~v1_xboole_0(k1_relat_1(C_2109)) | ~r2_hidden(A_2110, k9_relat_1(C_2109, B_2111)) | ~v1_relat_1(C_2109))), inference(resolution, [status(thm)], [c_23471, c_2])).
% 16.19/7.14  tff(c_24213, plain, (~v1_xboole_0(k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_23670, c_24202])).
% 16.19/7.14  tff(c_24242, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121, c_23172, c_23171, c_24213])).
% 16.19/7.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.19/7.14  
% 16.19/7.14  Inference rules
% 16.19/7.14  ----------------------
% 16.19/7.14  #Ref     : 0
% 16.19/7.14  #Sup     : 5636
% 16.19/7.14  #Fact    : 0
% 16.19/7.14  #Define  : 0
% 16.19/7.14  #Split   : 25
% 16.19/7.14  #Chain   : 0
% 16.19/7.14  #Close   : 0
% 16.19/7.14  
% 16.19/7.14  Ordering : KBO
% 16.19/7.14  
% 16.19/7.14  Simplification rules
% 16.19/7.14  ----------------------
% 16.19/7.14  #Subsume      : 2178
% 16.19/7.14  #Demod        : 905
% 16.19/7.14  #Tautology    : 143
% 16.19/7.14  #SimpNegUnit  : 66
% 16.19/7.14  #BackRed      : 12
% 16.19/7.14  
% 16.19/7.14  #Partial instantiations: 0
% 16.19/7.14  #Strategies tried      : 1
% 16.19/7.14  
% 16.19/7.14  Timing (in seconds)
% 16.19/7.14  ----------------------
% 16.19/7.15  Preprocessing        : 0.36
% 16.19/7.15  Parsing              : 0.19
% 16.19/7.15  CNF conversion       : 0.03
% 16.19/7.15  Main loop            : 5.94
% 16.19/7.15  Inferencing          : 1.19
% 16.19/7.15  Reduction            : 1.18
% 16.19/7.15  Demodulation         : 0.77
% 16.19/7.15  BG Simplification    : 0.10
% 16.19/7.15  Subsumption          : 3.06
% 16.19/7.15  Abstraction          : 0.16
% 16.19/7.15  MUC search           : 0.00
% 16.19/7.15  Cooper               : 0.00
% 16.19/7.15  Total                : 6.35
% 16.19/7.15  Index Insertion      : 0.00
% 16.19/7.15  Index Deletion       : 0.00
% 16.19/7.15  Index Matching       : 0.00
% 16.19/7.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
