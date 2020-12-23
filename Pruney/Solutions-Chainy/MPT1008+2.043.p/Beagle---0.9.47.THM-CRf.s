%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:32 EST 2020

% Result     : Theorem 3.57s
% Output     : CNFRefutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 218 expanded)
%              Number of leaves         :   46 (  92 expanded)
%              Depth                    :   10
%              Number of atoms          :  166 ( 444 expanded)
%              Number of equality atoms :   84 ( 200 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k3_mcart_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_155,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_50,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_143,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_125,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k3_mcart_1(C,D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_mcart_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_72,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_135,plain,(
    ! [C_80,A_81,B_82] :
      ( v1_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_143,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_135])).

tff(c_76,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_30,plain,(
    ! [A_17] :
      ( k1_relat_1(A_17) != k1_xboole_0
      | k1_xboole_0 = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_151,plain,
    ( k1_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_143,c_30])).

tff(c_163,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_287,plain,(
    ! [B_126,A_127] :
      ( k1_tarski(k1_funct_1(B_126,A_127)) = k2_relat_1(B_126)
      | k1_tarski(A_127) != k1_relat_1(B_126)
      | ~ v1_funct_1(B_126)
      | ~ v1_relat_1(B_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_258,plain,(
    ! [A_119,B_120,C_121] :
      ( k2_relset_1(A_119,B_120,C_121) = k2_relat_1(C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_266,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_72,c_258])).

tff(c_68,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') != k1_tarski(k1_funct_1('#skF_6','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_282,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_4')) != k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_68])).

tff(c_293,plain,
    ( k1_tarski('#skF_4') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_282])).

tff(c_312,plain,(
    k1_tarski('#skF_4') != k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_76,c_293])).

tff(c_187,plain,(
    ! [C_91,A_92,B_93] :
      ( v4_relat_1(C_91,A_92)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_195,plain,(
    v4_relat_1('#skF_6',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_72,c_187])).

tff(c_26,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(B_16),A_15)
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_515,plain,(
    ! [B_166,C_167,A_168] :
      ( k2_tarski(B_166,C_167) = A_168
      | k1_tarski(C_167) = A_168
      | k1_tarski(B_166) = A_168
      | k1_xboole_0 = A_168
      | ~ r1_tarski(A_168,k2_tarski(B_166,C_167)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_537,plain,(
    ! [A_2,A_168] :
      ( k2_tarski(A_2,A_2) = A_168
      | k1_tarski(A_2) = A_168
      | k1_tarski(A_2) = A_168
      | k1_xboole_0 = A_168
      | ~ r1_tarski(A_168,k1_tarski(A_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_515])).

tff(c_554,plain,(
    ! [A_169,A_170] :
      ( k1_tarski(A_169) = A_170
      | k1_tarski(A_169) = A_170
      | k1_tarski(A_169) = A_170
      | k1_xboole_0 = A_170
      | ~ r1_tarski(A_170,k1_tarski(A_169)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_537])).

tff(c_578,plain,(
    ! [A_171,B_172] :
      ( k1_tarski(A_171) = k1_relat_1(B_172)
      | k1_relat_1(B_172) = k1_xboole_0
      | ~ v4_relat_1(B_172,k1_tarski(A_171))
      | ~ v1_relat_1(B_172) ) ),
    inference(resolution,[status(thm)],[c_26,c_554])).

tff(c_584,plain,
    ( k1_tarski('#skF_4') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_195,c_578])).

tff(c_591,plain,
    ( k1_tarski('#skF_4') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_584])).

tff(c_593,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_163,c_312,c_591])).

tff(c_594,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_595,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_611,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_594,c_595])).

tff(c_32,plain,(
    ! [B_19,A_18] :
      ( k1_tarski(k1_funct_1(B_19,A_18)) = k2_relat_1(B_19)
      | k1_tarski(A_18) != k1_relat_1(B_19)
      | ~ v1_funct_1(B_19)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_20,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_602,plain,(
    ! [A_11] : m1_subset_1('#skF_6',k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_594,c_20])).

tff(c_731,plain,(
    ! [A_215,B_216,C_217] :
      ( k2_relset_1(A_215,B_216,C_217) = k2_relat_1(C_217)
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1(A_215,B_216))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_736,plain,(
    ! [A_215,B_216] : k2_relset_1(A_215,B_216,'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_602,c_731])).

tff(c_737,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_4')) != k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_736,c_68])).

tff(c_768,plain,
    ( k1_tarski('#skF_4') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_737])).

tff(c_771,plain,(
    k1_tarski('#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_76,c_611,c_768])).

tff(c_70,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_604,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_594,c_70])).

tff(c_74,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_66,plain,(
    ! [B_59,A_58,C_60] :
      ( k1_xboole_0 = B_59
      | k1_relset_1(A_58,B_59,C_60) = A_58
      | ~ v1_funct_2(C_60,A_58,B_59)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_888,plain,(
    ! [B_242,A_243,C_244] :
      ( B_242 = '#skF_6'
      | k1_relset_1(A_243,B_242,C_244) = A_243
      | ~ v1_funct_2(C_244,A_243,B_242)
      | ~ m1_subset_1(C_244,k1_zfmisc_1(k2_zfmisc_1(A_243,B_242))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_594,c_66])).

tff(c_899,plain,(
    ! [B_245,A_246] :
      ( B_245 = '#skF_6'
      | k1_relset_1(A_246,B_245,'#skF_6') = A_246
      | ~ v1_funct_2('#skF_6',A_246,B_245) ) ),
    inference(resolution,[status(thm)],[c_602,c_888])).

tff(c_908,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_899])).

tff(c_914,plain,(
    k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_604,c_908])).

tff(c_50,plain,(
    ! [A_44] :
      ( r2_hidden('#skF_3'(A_44),A_44)
      | k1_xboole_0 = A_44 ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_600,plain,(
    ! [A_44] :
      ( r2_hidden('#skF_3'(A_44),A_44)
      | A_44 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_594,c_50])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_603,plain,(
    ! [A_1] : r1_tarski('#skF_6',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_594,c_2])).

tff(c_1064,plain,(
    ! [D_283,A_284,B_285,C_286] :
      ( r2_hidden(k4_tarski(D_283,'#skF_2'(A_284,B_285,C_286,D_283)),C_286)
      | ~ r2_hidden(D_283,B_285)
      | k1_relset_1(B_285,A_284,C_286) != B_285
      | ~ m1_subset_1(C_286,k1_zfmisc_1(k2_zfmisc_1(B_285,A_284))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_34,plain,(
    ! [B_21,A_20] :
      ( ~ r1_tarski(B_21,A_20)
      | ~ r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1152,plain,(
    ! [C_294,D_295,A_296,B_297] :
      ( ~ r1_tarski(C_294,k4_tarski(D_295,'#skF_2'(A_296,B_297,C_294,D_295)))
      | ~ r2_hidden(D_295,B_297)
      | k1_relset_1(B_297,A_296,C_294) != B_297
      | ~ m1_subset_1(C_294,k1_zfmisc_1(k2_zfmisc_1(B_297,A_296))) ) ),
    inference(resolution,[status(thm)],[c_1064,c_34])).

tff(c_1160,plain,(
    ! [D_295,B_297,A_296] :
      ( ~ r2_hidden(D_295,B_297)
      | k1_relset_1(B_297,A_296,'#skF_6') != B_297
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(B_297,A_296))) ) ),
    inference(resolution,[status(thm)],[c_603,c_1152])).

tff(c_1165,plain,(
    ! [D_298,B_299,A_300] :
      ( ~ r2_hidden(D_298,B_299)
      | k1_relset_1(B_299,A_300,'#skF_6') != B_299 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_602,c_1160])).

tff(c_1175,plain,(
    ! [A_301,A_302] :
      ( k1_relset_1(A_301,A_302,'#skF_6') != A_301
      | A_301 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_600,c_1165])).

tff(c_1181,plain,(
    k1_tarski('#skF_4') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_914,c_1175])).

tff(c_1187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_771,c_1181])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:22:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.57/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.59  
% 3.57/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.60  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k3_mcart_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3
% 3.57/1.60  
% 3.57/1.60  %Foreground sorts:
% 3.57/1.60  
% 3.57/1.60  
% 3.57/1.60  %Background operators:
% 3.57/1.60  
% 3.57/1.60  
% 3.57/1.60  %Foreground operators:
% 3.57/1.60  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.57/1.60  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.57/1.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.57/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.57/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.57/1.60  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.57/1.60  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.57/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.57/1.60  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.57/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.57/1.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.57/1.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.57/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.57/1.60  tff('#skF_5', type, '#skF_5': $i).
% 3.57/1.60  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.57/1.60  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.57/1.60  tff('#skF_6', type, '#skF_6': $i).
% 3.57/1.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.57/1.60  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.57/1.60  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.57/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.57/1.60  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.57/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.57/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.57/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.57/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.57/1.60  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.57/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.57/1.60  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.57/1.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.57/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.57/1.60  
% 3.57/1.62  tff(f_155, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 3.57/1.62  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.57/1.62  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.57/1.62  tff(f_78, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.57/1.62  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.57/1.62  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.57/1.62  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.57/1.62  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.57/1.62  tff(f_48, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.57/1.62  tff(f_50, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.57/1.62  tff(f_143, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.57/1.62  tff(f_125, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 3.57/1.62  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.57/1.62  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 3.57/1.62  tff(f_83, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.57/1.62  tff(c_72, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.57/1.62  tff(c_135, plain, (![C_80, A_81, B_82]: (v1_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.57/1.62  tff(c_143, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_72, c_135])).
% 3.57/1.62  tff(c_76, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.57/1.62  tff(c_30, plain, (![A_17]: (k1_relat_1(A_17)!=k1_xboole_0 | k1_xboole_0=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.57/1.62  tff(c_151, plain, (k1_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_143, c_30])).
% 3.57/1.62  tff(c_163, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_151])).
% 3.57/1.62  tff(c_287, plain, (![B_126, A_127]: (k1_tarski(k1_funct_1(B_126, A_127))=k2_relat_1(B_126) | k1_tarski(A_127)!=k1_relat_1(B_126) | ~v1_funct_1(B_126) | ~v1_relat_1(B_126))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.57/1.62  tff(c_258, plain, (![A_119, B_120, C_121]: (k2_relset_1(A_119, B_120, C_121)=k2_relat_1(C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.57/1.62  tff(c_266, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_72, c_258])).
% 3.57/1.62  tff(c_68, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')!=k1_tarski(k1_funct_1('#skF_6', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.57/1.62  tff(c_282, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_4'))!=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_266, c_68])).
% 3.57/1.62  tff(c_293, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_287, c_282])).
% 3.57/1.62  tff(c_312, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_143, c_76, c_293])).
% 3.57/1.62  tff(c_187, plain, (![C_91, A_92, B_93]: (v4_relat_1(C_91, A_92) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.57/1.62  tff(c_195, plain, (v4_relat_1('#skF_6', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_72, c_187])).
% 3.57/1.62  tff(c_26, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(B_16), A_15) | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.57/1.62  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.57/1.62  tff(c_515, plain, (![B_166, C_167, A_168]: (k2_tarski(B_166, C_167)=A_168 | k1_tarski(C_167)=A_168 | k1_tarski(B_166)=A_168 | k1_xboole_0=A_168 | ~r1_tarski(A_168, k2_tarski(B_166, C_167)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.57/1.62  tff(c_537, plain, (![A_2, A_168]: (k2_tarski(A_2, A_2)=A_168 | k1_tarski(A_2)=A_168 | k1_tarski(A_2)=A_168 | k1_xboole_0=A_168 | ~r1_tarski(A_168, k1_tarski(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_515])).
% 3.57/1.62  tff(c_554, plain, (![A_169, A_170]: (k1_tarski(A_169)=A_170 | k1_tarski(A_169)=A_170 | k1_tarski(A_169)=A_170 | k1_xboole_0=A_170 | ~r1_tarski(A_170, k1_tarski(A_169)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_537])).
% 3.57/1.62  tff(c_578, plain, (![A_171, B_172]: (k1_tarski(A_171)=k1_relat_1(B_172) | k1_relat_1(B_172)=k1_xboole_0 | ~v4_relat_1(B_172, k1_tarski(A_171)) | ~v1_relat_1(B_172))), inference(resolution, [status(thm)], [c_26, c_554])).
% 3.57/1.62  tff(c_584, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_195, c_578])).
% 3.57/1.62  tff(c_591, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_143, c_584])).
% 3.57/1.62  tff(c_593, plain, $false, inference(negUnitSimplification, [status(thm)], [c_163, c_312, c_591])).
% 3.57/1.62  tff(c_594, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_151])).
% 3.57/1.62  tff(c_595, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_151])).
% 3.57/1.62  tff(c_611, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_594, c_595])).
% 3.57/1.62  tff(c_32, plain, (![B_19, A_18]: (k1_tarski(k1_funct_1(B_19, A_18))=k2_relat_1(B_19) | k1_tarski(A_18)!=k1_relat_1(B_19) | ~v1_funct_1(B_19) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.57/1.62  tff(c_20, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.57/1.62  tff(c_602, plain, (![A_11]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_594, c_20])).
% 3.57/1.62  tff(c_731, plain, (![A_215, B_216, C_217]: (k2_relset_1(A_215, B_216, C_217)=k2_relat_1(C_217) | ~m1_subset_1(C_217, k1_zfmisc_1(k2_zfmisc_1(A_215, B_216))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.57/1.62  tff(c_736, plain, (![A_215, B_216]: (k2_relset_1(A_215, B_216, '#skF_6')=k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_602, c_731])).
% 3.57/1.62  tff(c_737, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_4'))!=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_736, c_68])).
% 3.57/1.62  tff(c_768, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_32, c_737])).
% 3.57/1.62  tff(c_771, plain, (k1_tarski('#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_143, c_76, c_611, c_768])).
% 3.57/1.62  tff(c_70, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.57/1.62  tff(c_604, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_594, c_70])).
% 3.57/1.62  tff(c_74, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.57/1.62  tff(c_66, plain, (![B_59, A_58, C_60]: (k1_xboole_0=B_59 | k1_relset_1(A_58, B_59, C_60)=A_58 | ~v1_funct_2(C_60, A_58, B_59) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.57/1.62  tff(c_888, plain, (![B_242, A_243, C_244]: (B_242='#skF_6' | k1_relset_1(A_243, B_242, C_244)=A_243 | ~v1_funct_2(C_244, A_243, B_242) | ~m1_subset_1(C_244, k1_zfmisc_1(k2_zfmisc_1(A_243, B_242))))), inference(demodulation, [status(thm), theory('equality')], [c_594, c_66])).
% 3.57/1.62  tff(c_899, plain, (![B_245, A_246]: (B_245='#skF_6' | k1_relset_1(A_246, B_245, '#skF_6')=A_246 | ~v1_funct_2('#skF_6', A_246, B_245))), inference(resolution, [status(thm)], [c_602, c_888])).
% 3.57/1.62  tff(c_908, plain, ('#skF_5'='#skF_6' | k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_74, c_899])).
% 3.57/1.62  tff(c_914, plain, (k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_604, c_908])).
% 3.57/1.62  tff(c_50, plain, (![A_44]: (r2_hidden('#skF_3'(A_44), A_44) | k1_xboole_0=A_44)), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.57/1.62  tff(c_600, plain, (![A_44]: (r2_hidden('#skF_3'(A_44), A_44) | A_44='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_594, c_50])).
% 3.57/1.62  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.57/1.62  tff(c_603, plain, (![A_1]: (r1_tarski('#skF_6', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_594, c_2])).
% 3.57/1.62  tff(c_1064, plain, (![D_283, A_284, B_285, C_286]: (r2_hidden(k4_tarski(D_283, '#skF_2'(A_284, B_285, C_286, D_283)), C_286) | ~r2_hidden(D_283, B_285) | k1_relset_1(B_285, A_284, C_286)!=B_285 | ~m1_subset_1(C_286, k1_zfmisc_1(k2_zfmisc_1(B_285, A_284))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.57/1.62  tff(c_34, plain, (![B_21, A_20]: (~r1_tarski(B_21, A_20) | ~r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.57/1.62  tff(c_1152, plain, (![C_294, D_295, A_296, B_297]: (~r1_tarski(C_294, k4_tarski(D_295, '#skF_2'(A_296, B_297, C_294, D_295))) | ~r2_hidden(D_295, B_297) | k1_relset_1(B_297, A_296, C_294)!=B_297 | ~m1_subset_1(C_294, k1_zfmisc_1(k2_zfmisc_1(B_297, A_296))))), inference(resolution, [status(thm)], [c_1064, c_34])).
% 3.57/1.62  tff(c_1160, plain, (![D_295, B_297, A_296]: (~r2_hidden(D_295, B_297) | k1_relset_1(B_297, A_296, '#skF_6')!=B_297 | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(B_297, A_296))))), inference(resolution, [status(thm)], [c_603, c_1152])).
% 3.57/1.62  tff(c_1165, plain, (![D_298, B_299, A_300]: (~r2_hidden(D_298, B_299) | k1_relset_1(B_299, A_300, '#skF_6')!=B_299)), inference(demodulation, [status(thm), theory('equality')], [c_602, c_1160])).
% 3.57/1.62  tff(c_1175, plain, (![A_301, A_302]: (k1_relset_1(A_301, A_302, '#skF_6')!=A_301 | A_301='#skF_6')), inference(resolution, [status(thm)], [c_600, c_1165])).
% 3.57/1.62  tff(c_1181, plain, (k1_tarski('#skF_4')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_914, c_1175])).
% 3.57/1.62  tff(c_1187, plain, $false, inference(negUnitSimplification, [status(thm)], [c_771, c_1181])).
% 3.57/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.57/1.62  
% 3.57/1.62  Inference rules
% 3.57/1.62  ----------------------
% 3.57/1.62  #Ref     : 0
% 3.57/1.62  #Sup     : 219
% 3.57/1.62  #Fact    : 0
% 3.57/1.62  #Define  : 0
% 3.57/1.62  #Split   : 2
% 3.57/1.62  #Chain   : 0
% 3.57/1.62  #Close   : 0
% 3.57/1.62  
% 3.57/1.62  Ordering : KBO
% 3.57/1.62  
% 3.57/1.62  Simplification rules
% 3.57/1.62  ----------------------
% 3.57/1.62  #Subsume      : 13
% 3.57/1.62  #Demod        : 111
% 3.57/1.62  #Tautology    : 104
% 3.57/1.62  #SimpNegUnit  : 5
% 3.57/1.62  #BackRed      : 13
% 3.57/1.62  
% 3.57/1.62  #Partial instantiations: 0
% 3.57/1.62  #Strategies tried      : 1
% 3.57/1.62  
% 3.57/1.62  Timing (in seconds)
% 3.57/1.62  ----------------------
% 3.86/1.62  Preprocessing        : 0.36
% 3.86/1.62  Parsing              : 0.19
% 3.86/1.62  CNF conversion       : 0.03
% 3.86/1.62  Main loop            : 0.47
% 3.86/1.62  Inferencing          : 0.18
% 3.86/1.62  Reduction            : 0.14
% 3.86/1.62  Demodulation         : 0.10
% 3.86/1.62  BG Simplification    : 0.03
% 3.86/1.62  Subsumption          : 0.08
% 3.86/1.62  Abstraction          : 0.02
% 3.86/1.62  MUC search           : 0.00
% 3.86/1.62  Cooper               : 0.00
% 3.86/1.62  Total                : 0.87
% 3.86/1.62  Index Insertion      : 0.00
% 3.86/1.62  Index Deletion       : 0.00
% 3.86/1.62  Index Matching       : 0.00
% 3.86/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
