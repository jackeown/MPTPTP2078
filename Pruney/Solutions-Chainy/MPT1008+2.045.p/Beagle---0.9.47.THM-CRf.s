%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:32 EST 2020

% Result     : Theorem 4.11s
% Output     : CNFRefutation 4.11s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 225 expanded)
%              Number of leaves         :   46 (  94 expanded)
%              Depth                    :   10
%              Number of atoms          :  198 ( 480 expanded)
%              Number of equality atoms :  112 ( 232 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3

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

tff(f_167,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

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

tff(f_62,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_155,axiom,(
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

tff(f_137,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_mcart_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_80,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_173,plain,(
    ! [C_92,A_93,B_94] :
      ( v1_relat_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_181,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_173])).

tff(c_84,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_38,plain,(
    ! [A_18] :
      ( k1_relat_1(A_18) != k1_xboole_0
      | k1_xboole_0 = A_18
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_190,plain,
    ( k1_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_181,c_38])).

tff(c_202,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_190])).

tff(c_343,plain,(
    ! [B_140,A_141] :
      ( k1_tarski(k1_funct_1(B_140,A_141)) = k2_relat_1(B_140)
      | k1_tarski(A_141) != k1_relat_1(B_140)
      | ~ v1_funct_1(B_140)
      | ~ v1_relat_1(B_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_286,plain,(
    ! [A_130,B_131,C_132] :
      ( k2_relset_1(A_130,B_131,C_132) = k2_relat_1(C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_294,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_80,c_286])).

tff(c_76,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') != k1_tarski(k1_funct_1('#skF_6','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_303,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_4')) != k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_76])).

tff(c_349,plain,
    ( k1_tarski('#skF_4') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_303])).

tff(c_377,plain,(
    k1_tarski('#skF_4') != k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_84,c_349])).

tff(c_212,plain,(
    ! [C_98,A_99,B_100] :
      ( v4_relat_1(C_98,A_99)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_220,plain,(
    v4_relat_1('#skF_6',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_80,c_212])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_34,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6,plain,(
    ! [A_3,B_4] : k1_enumset1(A_3,A_3,B_4) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_614,plain,(
    ! [A_191,B_192,C_193,D_194] :
      ( k1_enumset1(A_191,B_192,C_193) = D_194
      | k2_tarski(A_191,C_193) = D_194
      | k2_tarski(B_192,C_193) = D_194
      | k2_tarski(A_191,B_192) = D_194
      | k1_tarski(C_193) = D_194
      | k1_tarski(B_192) = D_194
      | k1_tarski(A_191) = D_194
      | k1_xboole_0 = D_194
      | ~ r1_tarski(D_194,k1_enumset1(A_191,B_192,C_193)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_633,plain,(
    ! [A_3,B_4,D_194] :
      ( k1_enumset1(A_3,A_3,B_4) = D_194
      | k2_tarski(A_3,B_4) = D_194
      | k2_tarski(A_3,B_4) = D_194
      | k2_tarski(A_3,A_3) = D_194
      | k1_tarski(B_4) = D_194
      | k1_tarski(A_3) = D_194
      | k1_tarski(A_3) = D_194
      | k1_xboole_0 = D_194
      | ~ r1_tarski(D_194,k2_tarski(A_3,B_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_614])).

tff(c_847,plain,(
    ! [A_257,B_258,D_259] :
      ( k2_tarski(A_257,B_258) = D_259
      | k2_tarski(A_257,B_258) = D_259
      | k2_tarski(A_257,B_258) = D_259
      | k1_tarski(A_257) = D_259
      | k1_tarski(B_258) = D_259
      | k1_tarski(A_257) = D_259
      | k1_tarski(A_257) = D_259
      | k1_xboole_0 = D_259
      | ~ r1_tarski(D_259,k2_tarski(A_257,B_258)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_633])).

tff(c_886,plain,(
    ! [A_260,B_261,B_262] :
      ( k2_tarski(A_260,B_261) = k1_relat_1(B_262)
      | k1_tarski(B_261) = k1_relat_1(B_262)
      | k1_tarski(A_260) = k1_relat_1(B_262)
      | k1_relat_1(B_262) = k1_xboole_0
      | ~ v4_relat_1(B_262,k2_tarski(A_260,B_261))
      | ~ v1_relat_1(B_262) ) ),
    inference(resolution,[status(thm)],[c_34,c_847])).

tff(c_893,plain,(
    ! [A_2,B_262] :
      ( k2_tarski(A_2,A_2) = k1_relat_1(B_262)
      | k1_tarski(A_2) = k1_relat_1(B_262)
      | k1_tarski(A_2) = k1_relat_1(B_262)
      | k1_relat_1(B_262) = k1_xboole_0
      | ~ v4_relat_1(B_262,k1_tarski(A_2))
      | ~ v1_relat_1(B_262) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_886])).

tff(c_898,plain,(
    ! [A_263,B_264] :
      ( k1_tarski(A_263) = k1_relat_1(B_264)
      | k1_tarski(A_263) = k1_relat_1(B_264)
      | k1_tarski(A_263) = k1_relat_1(B_264)
      | k1_relat_1(B_264) = k1_xboole_0
      | ~ v4_relat_1(B_264,k1_tarski(A_263))
      | ~ v1_relat_1(B_264) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_893])).

tff(c_904,plain,
    ( k1_tarski('#skF_4') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_220,c_898])).

tff(c_911,plain,
    ( k1_tarski('#skF_4') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_904])).

tff(c_913,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_202,c_377,c_911])).

tff(c_914,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_915,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_190])).

tff(c_939,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_914,c_915])).

tff(c_1090,plain,(
    ! [B_316,A_317] :
      ( k1_tarski(k1_funct_1(B_316,A_317)) = k2_relat_1(B_316)
      | k1_tarski(A_317) != k1_relat_1(B_316)
      | ~ v1_funct_1(B_316)
      | ~ v1_relat_1(B_316) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_28,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_931,plain,(
    ! [A_12] : m1_subset_1('#skF_6',k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_914,c_28])).

tff(c_1068,plain,(
    ! [A_309,B_310,C_311] :
      ( k2_relset_1(A_309,B_310,C_311) = k2_relat_1(C_311)
      | ~ m1_subset_1(C_311,k1_zfmisc_1(k2_zfmisc_1(A_309,B_310))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1073,plain,(
    ! [A_309,B_310] : k2_relset_1(A_309,B_310,'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_931,c_1068])).

tff(c_1074,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_4')) != k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1073,c_76])).

tff(c_1096,plain,
    ( k1_tarski('#skF_4') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1090,c_1074])).

tff(c_1124,plain,(
    k1_tarski('#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_84,c_939,c_1096])).

tff(c_78,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_933,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_914,c_78])).

tff(c_82,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_74,plain,(
    ! [B_56,A_55,C_57] :
      ( k1_xboole_0 = B_56
      | k1_relset_1(A_55,B_56,C_57) = A_55
      | ~ v1_funct_2(C_57,A_55,B_56)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1234,plain,(
    ! [B_336,A_337,C_338] :
      ( B_336 = '#skF_6'
      | k1_relset_1(A_337,B_336,C_338) = A_337
      | ~ v1_funct_2(C_338,A_337,B_336)
      | ~ m1_subset_1(C_338,k1_zfmisc_1(k2_zfmisc_1(A_337,B_336))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_914,c_74])).

tff(c_1245,plain,(
    ! [B_339,A_340] :
      ( B_339 = '#skF_6'
      | k1_relset_1(A_340,B_339,'#skF_6') = A_340
      | ~ v1_funct_2('#skF_6',A_340,B_339) ) ),
    inference(resolution,[status(thm)],[c_931,c_1234])).

tff(c_1254,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_1245])).

tff(c_1260,plain,(
    k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_933,c_1254])).

tff(c_58,plain,(
    ! [A_45] :
      ( r2_hidden('#skF_3'(A_45),A_45)
      | k1_xboole_0 = A_45 ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_929,plain,(
    ! [A_45] :
      ( r2_hidden('#skF_3'(A_45),A_45)
      | A_45 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_914,c_58])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_932,plain,(
    ! [A_1] : r1_tarski('#skF_6',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_914,c_2])).

tff(c_1322,plain,(
    ! [D_366,A_367,B_368,C_369] :
      ( r2_hidden(k4_tarski(D_366,'#skF_2'(A_367,B_368,C_369,D_366)),C_369)
      | ~ r2_hidden(D_366,B_368)
      | k1_relset_1(B_368,A_367,C_369) != B_368
      | ~ m1_subset_1(C_369,k1_zfmisc_1(k2_zfmisc_1(B_368,A_367))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_42,plain,(
    ! [B_22,A_21] :
      ( ~ r1_tarski(B_22,A_21)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1501,plain,(
    ! [C_395,D_396,A_397,B_398] :
      ( ~ r1_tarski(C_395,k4_tarski(D_396,'#skF_2'(A_397,B_398,C_395,D_396)))
      | ~ r2_hidden(D_396,B_398)
      | k1_relset_1(B_398,A_397,C_395) != B_398
      | ~ m1_subset_1(C_395,k1_zfmisc_1(k2_zfmisc_1(B_398,A_397))) ) ),
    inference(resolution,[status(thm)],[c_1322,c_42])).

tff(c_1509,plain,(
    ! [D_396,B_398,A_397] :
      ( ~ r2_hidden(D_396,B_398)
      | k1_relset_1(B_398,A_397,'#skF_6') != B_398
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(B_398,A_397))) ) ),
    inference(resolution,[status(thm)],[c_932,c_1501])).

tff(c_1514,plain,(
    ! [D_399,B_400,A_401] :
      ( ~ r2_hidden(D_399,B_400)
      | k1_relset_1(B_400,A_401,'#skF_6') != B_400 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_931,c_1509])).

tff(c_1524,plain,(
    ! [A_402,A_403] :
      ( k1_relset_1(A_402,A_403,'#skF_6') != A_402
      | A_402 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_929,c_1514])).

tff(c_1530,plain,(
    k1_tarski('#skF_4') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_1260,c_1524])).

tff(c_1536,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1124,c_1530])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:05:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.11/1.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.11/1.71  
% 4.11/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.11/1.71  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3
% 4.11/1.71  
% 4.11/1.71  %Foreground sorts:
% 4.11/1.71  
% 4.11/1.71  
% 4.11/1.71  %Background operators:
% 4.11/1.71  
% 4.11/1.71  
% 4.11/1.71  %Foreground operators:
% 4.11/1.71  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.11/1.71  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.11/1.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.11/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.11/1.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.11/1.71  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.11/1.71  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.11/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.11/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.11/1.71  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.11/1.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.11/1.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.11/1.71  tff('#skF_5', type, '#skF_5': $i).
% 4.11/1.71  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.11/1.71  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.11/1.71  tff('#skF_6', type, '#skF_6': $i).
% 4.11/1.71  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.11/1.71  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.11/1.71  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.11/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.11/1.71  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.11/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.11/1.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.11/1.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.11/1.71  tff('#skF_4', type, '#skF_4': $i).
% 4.11/1.71  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.11/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.11/1.71  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.11/1.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.11/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.11/1.71  
% 4.11/1.73  tff(f_167, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 4.11/1.73  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.11/1.73  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 4.11/1.73  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 4.11/1.73  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.11/1.73  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.11/1.73  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.11/1.73  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 4.11/1.73  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.11/1.73  tff(f_60, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 4.11/1.73  tff(f_62, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.11/1.73  tff(f_155, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.11/1.73  tff(f_137, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_tarski(C, D)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_mcart_1)).
% 4.11/1.73  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.11/1.73  tff(f_121, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 4.11/1.73  tff(f_95, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.11/1.73  tff(c_80, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.11/1.73  tff(c_173, plain, (![C_92, A_93, B_94]: (v1_relat_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.11/1.73  tff(c_181, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_80, c_173])).
% 4.11/1.73  tff(c_84, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.11/1.73  tff(c_38, plain, (![A_18]: (k1_relat_1(A_18)!=k1_xboole_0 | k1_xboole_0=A_18 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.11/1.73  tff(c_190, plain, (k1_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_181, c_38])).
% 4.11/1.73  tff(c_202, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_190])).
% 4.11/1.73  tff(c_343, plain, (![B_140, A_141]: (k1_tarski(k1_funct_1(B_140, A_141))=k2_relat_1(B_140) | k1_tarski(A_141)!=k1_relat_1(B_140) | ~v1_funct_1(B_140) | ~v1_relat_1(B_140))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.11/1.73  tff(c_286, plain, (![A_130, B_131, C_132]: (k2_relset_1(A_130, B_131, C_132)=k2_relat_1(C_132) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.11/1.73  tff(c_294, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_80, c_286])).
% 4.11/1.73  tff(c_76, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')!=k1_tarski(k1_funct_1('#skF_6', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.11/1.73  tff(c_303, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_4'))!=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_294, c_76])).
% 4.11/1.73  tff(c_349, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_343, c_303])).
% 4.11/1.73  tff(c_377, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_181, c_84, c_349])).
% 4.11/1.73  tff(c_212, plain, (![C_98, A_99, B_100]: (v4_relat_1(C_98, A_99) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.11/1.73  tff(c_220, plain, (v4_relat_1('#skF_6', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_80, c_212])).
% 4.11/1.73  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.11/1.73  tff(c_34, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(B_17), A_16) | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.11/1.73  tff(c_6, plain, (![A_3, B_4]: (k1_enumset1(A_3, A_3, B_4)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.11/1.73  tff(c_614, plain, (![A_191, B_192, C_193, D_194]: (k1_enumset1(A_191, B_192, C_193)=D_194 | k2_tarski(A_191, C_193)=D_194 | k2_tarski(B_192, C_193)=D_194 | k2_tarski(A_191, B_192)=D_194 | k1_tarski(C_193)=D_194 | k1_tarski(B_192)=D_194 | k1_tarski(A_191)=D_194 | k1_xboole_0=D_194 | ~r1_tarski(D_194, k1_enumset1(A_191, B_192, C_193)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.11/1.73  tff(c_633, plain, (![A_3, B_4, D_194]: (k1_enumset1(A_3, A_3, B_4)=D_194 | k2_tarski(A_3, B_4)=D_194 | k2_tarski(A_3, B_4)=D_194 | k2_tarski(A_3, A_3)=D_194 | k1_tarski(B_4)=D_194 | k1_tarski(A_3)=D_194 | k1_tarski(A_3)=D_194 | k1_xboole_0=D_194 | ~r1_tarski(D_194, k2_tarski(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_614])).
% 4.11/1.73  tff(c_847, plain, (![A_257, B_258, D_259]: (k2_tarski(A_257, B_258)=D_259 | k2_tarski(A_257, B_258)=D_259 | k2_tarski(A_257, B_258)=D_259 | k1_tarski(A_257)=D_259 | k1_tarski(B_258)=D_259 | k1_tarski(A_257)=D_259 | k1_tarski(A_257)=D_259 | k1_xboole_0=D_259 | ~r1_tarski(D_259, k2_tarski(A_257, B_258)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6, c_633])).
% 4.11/1.73  tff(c_886, plain, (![A_260, B_261, B_262]: (k2_tarski(A_260, B_261)=k1_relat_1(B_262) | k1_tarski(B_261)=k1_relat_1(B_262) | k1_tarski(A_260)=k1_relat_1(B_262) | k1_relat_1(B_262)=k1_xboole_0 | ~v4_relat_1(B_262, k2_tarski(A_260, B_261)) | ~v1_relat_1(B_262))), inference(resolution, [status(thm)], [c_34, c_847])).
% 4.11/1.73  tff(c_893, plain, (![A_2, B_262]: (k2_tarski(A_2, A_2)=k1_relat_1(B_262) | k1_tarski(A_2)=k1_relat_1(B_262) | k1_tarski(A_2)=k1_relat_1(B_262) | k1_relat_1(B_262)=k1_xboole_0 | ~v4_relat_1(B_262, k1_tarski(A_2)) | ~v1_relat_1(B_262))), inference(superposition, [status(thm), theory('equality')], [c_4, c_886])).
% 4.11/1.73  tff(c_898, plain, (![A_263, B_264]: (k1_tarski(A_263)=k1_relat_1(B_264) | k1_tarski(A_263)=k1_relat_1(B_264) | k1_tarski(A_263)=k1_relat_1(B_264) | k1_relat_1(B_264)=k1_xboole_0 | ~v4_relat_1(B_264, k1_tarski(A_263)) | ~v1_relat_1(B_264))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_893])).
% 4.11/1.73  tff(c_904, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_220, c_898])).
% 4.11/1.73  tff(c_911, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_181, c_904])).
% 4.11/1.73  tff(c_913, plain, $false, inference(negUnitSimplification, [status(thm)], [c_202, c_377, c_911])).
% 4.11/1.73  tff(c_914, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_190])).
% 4.11/1.73  tff(c_915, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_190])).
% 4.11/1.73  tff(c_939, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_914, c_915])).
% 4.11/1.73  tff(c_1090, plain, (![B_316, A_317]: (k1_tarski(k1_funct_1(B_316, A_317))=k2_relat_1(B_316) | k1_tarski(A_317)!=k1_relat_1(B_316) | ~v1_funct_1(B_316) | ~v1_relat_1(B_316))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.11/1.73  tff(c_28, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.11/1.73  tff(c_931, plain, (![A_12]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_914, c_28])).
% 4.11/1.73  tff(c_1068, plain, (![A_309, B_310, C_311]: (k2_relset_1(A_309, B_310, C_311)=k2_relat_1(C_311) | ~m1_subset_1(C_311, k1_zfmisc_1(k2_zfmisc_1(A_309, B_310))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.11/1.73  tff(c_1073, plain, (![A_309, B_310]: (k2_relset_1(A_309, B_310, '#skF_6')=k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_931, c_1068])).
% 4.11/1.73  tff(c_1074, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_4'))!=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1073, c_76])).
% 4.11/1.73  tff(c_1096, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1090, c_1074])).
% 4.11/1.73  tff(c_1124, plain, (k1_tarski('#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_181, c_84, c_939, c_1096])).
% 4.11/1.73  tff(c_78, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.11/1.73  tff(c_933, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_914, c_78])).
% 4.11/1.73  tff(c_82, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.11/1.73  tff(c_74, plain, (![B_56, A_55, C_57]: (k1_xboole_0=B_56 | k1_relset_1(A_55, B_56, C_57)=A_55 | ~v1_funct_2(C_57, A_55, B_56) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.11/1.73  tff(c_1234, plain, (![B_336, A_337, C_338]: (B_336='#skF_6' | k1_relset_1(A_337, B_336, C_338)=A_337 | ~v1_funct_2(C_338, A_337, B_336) | ~m1_subset_1(C_338, k1_zfmisc_1(k2_zfmisc_1(A_337, B_336))))), inference(demodulation, [status(thm), theory('equality')], [c_914, c_74])).
% 4.11/1.73  tff(c_1245, plain, (![B_339, A_340]: (B_339='#skF_6' | k1_relset_1(A_340, B_339, '#skF_6')=A_340 | ~v1_funct_2('#skF_6', A_340, B_339))), inference(resolution, [status(thm)], [c_931, c_1234])).
% 4.11/1.73  tff(c_1254, plain, ('#skF_5'='#skF_6' | k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_82, c_1245])).
% 4.11/1.73  tff(c_1260, plain, (k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_933, c_1254])).
% 4.11/1.73  tff(c_58, plain, (![A_45]: (r2_hidden('#skF_3'(A_45), A_45) | k1_xboole_0=A_45)), inference(cnfTransformation, [status(thm)], [f_137])).
% 4.11/1.73  tff(c_929, plain, (![A_45]: (r2_hidden('#skF_3'(A_45), A_45) | A_45='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_914, c_58])).
% 4.11/1.73  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.11/1.73  tff(c_932, plain, (![A_1]: (r1_tarski('#skF_6', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_914, c_2])).
% 4.11/1.73  tff(c_1322, plain, (![D_366, A_367, B_368, C_369]: (r2_hidden(k4_tarski(D_366, '#skF_2'(A_367, B_368, C_369, D_366)), C_369) | ~r2_hidden(D_366, B_368) | k1_relset_1(B_368, A_367, C_369)!=B_368 | ~m1_subset_1(C_369, k1_zfmisc_1(k2_zfmisc_1(B_368, A_367))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.11/1.73  tff(c_42, plain, (![B_22, A_21]: (~r1_tarski(B_22, A_21) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.11/1.73  tff(c_1501, plain, (![C_395, D_396, A_397, B_398]: (~r1_tarski(C_395, k4_tarski(D_396, '#skF_2'(A_397, B_398, C_395, D_396))) | ~r2_hidden(D_396, B_398) | k1_relset_1(B_398, A_397, C_395)!=B_398 | ~m1_subset_1(C_395, k1_zfmisc_1(k2_zfmisc_1(B_398, A_397))))), inference(resolution, [status(thm)], [c_1322, c_42])).
% 4.11/1.73  tff(c_1509, plain, (![D_396, B_398, A_397]: (~r2_hidden(D_396, B_398) | k1_relset_1(B_398, A_397, '#skF_6')!=B_398 | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(B_398, A_397))))), inference(resolution, [status(thm)], [c_932, c_1501])).
% 4.11/1.73  tff(c_1514, plain, (![D_399, B_400, A_401]: (~r2_hidden(D_399, B_400) | k1_relset_1(B_400, A_401, '#skF_6')!=B_400)), inference(demodulation, [status(thm), theory('equality')], [c_931, c_1509])).
% 4.11/1.73  tff(c_1524, plain, (![A_402, A_403]: (k1_relset_1(A_402, A_403, '#skF_6')!=A_402 | A_402='#skF_6')), inference(resolution, [status(thm)], [c_929, c_1514])).
% 4.11/1.73  tff(c_1530, plain, (k1_tarski('#skF_4')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_1260, c_1524])).
% 4.11/1.73  tff(c_1536, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1124, c_1530])).
% 4.11/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.11/1.73  
% 4.11/1.73  Inference rules
% 4.11/1.73  ----------------------
% 4.11/1.73  #Ref     : 0
% 4.11/1.73  #Sup     : 289
% 4.11/1.73  #Fact    : 0
% 4.11/1.73  #Define  : 0
% 4.11/1.73  #Split   : 2
% 4.11/1.73  #Chain   : 0
% 4.11/1.73  #Close   : 0
% 4.11/1.73  
% 4.11/1.73  Ordering : KBO
% 4.11/1.73  
% 4.11/1.73  Simplification rules
% 4.11/1.73  ----------------------
% 4.11/1.73  #Subsume      : 38
% 4.11/1.73  #Demod        : 167
% 4.11/1.73  #Tautology    : 136
% 4.11/1.73  #SimpNegUnit  : 5
% 4.11/1.73  #BackRed      : 13
% 4.11/1.73  
% 4.11/1.73  #Partial instantiations: 0
% 4.11/1.73  #Strategies tried      : 1
% 4.11/1.73  
% 4.11/1.73  Timing (in seconds)
% 4.11/1.73  ----------------------
% 4.11/1.73  Preprocessing        : 0.37
% 4.11/1.73  Parsing              : 0.19
% 4.11/1.73  CNF conversion       : 0.03
% 4.11/1.73  Main loop            : 0.57
% 4.11/1.73  Inferencing          : 0.22
% 4.11/1.73  Reduction            : 0.17
% 4.11/1.73  Demodulation         : 0.12
% 4.11/1.73  BG Simplification    : 0.03
% 4.11/1.73  Subsumption          : 0.10
% 4.11/1.73  Abstraction          : 0.03
% 4.11/1.73  MUC search           : 0.00
% 4.11/1.73  Cooper               : 0.00
% 4.11/1.73  Total                : 0.98
% 4.11/1.73  Index Insertion      : 0.00
% 4.11/1.73  Index Deletion       : 0.00
% 4.11/1.73  Index Matching       : 0.00
% 4.11/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
