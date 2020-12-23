%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:35 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 423 expanded)
%              Number of leaves         :   44 ( 163 expanded)
%              Depth                    :   13
%              Number of atoms          :  209 ( 956 expanded)
%              Number of equality atoms :  116 ( 436 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k3_mcart_1 > k2_relset_1 > k1_enumset1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_148,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

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

tff(f_69,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_124,axiom,(
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

tff(f_136,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_94,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_152,plain,(
    ! [C_77,A_78,B_79] :
      ( v1_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_156,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_152])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_36,plain,(
    ! [A_14] :
      ( k1_relat_1(A_14) != k1_xboole_0
      | k1_xboole_0 = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_164,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_156,c_36])).

tff(c_175,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_164])).

tff(c_250,plain,(
    ! [B_119,A_120] :
      ( k1_tarski(k1_funct_1(B_119,A_120)) = k2_relat_1(B_119)
      | k1_tarski(A_120) != k1_relat_1(B_119)
      | ~ v1_funct_1(B_119)
      | ~ v1_relat_1(B_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_240,plain,(
    ! [A_116,B_117,C_118] :
      ( k2_relset_1(A_116,B_117,C_118) = k2_relat_1(C_118)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_244,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_240])).

tff(c_60,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') != k1_tarski(k1_funct_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_245,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_60])).

tff(c_256,plain,
    ( k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_245])).

tff(c_284,plain,(
    k1_tarski('#skF_2') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_68,c_256])).

tff(c_201,plain,(
    ! [C_96,A_97,B_98] :
      ( v4_relat_1(C_96,A_97)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_205,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_64,c_201])).

tff(c_28,plain,(
    ! [B_13,A_12] :
      ( k7_relat_1(B_13,A_12) = B_13
      | ~ v4_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_208,plain,
    ( k7_relat_1('#skF_4',k1_tarski('#skF_2')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_205,c_28])).

tff(c_211,plain,(
    k7_relat_1('#skF_4',k1_tarski('#skF_2')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_208])).

tff(c_38,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_16,A_15)),A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_215,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),k1_tarski('#skF_2'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_38])).

tff(c_219,plain,(
    r1_tarski(k1_relat_1('#skF_4'),k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_215])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_3,B_4] : k1_enumset1(A_3,A_3,B_4) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_386,plain,(
    ! [A_157,B_158,C_159,D_160] :
      ( k1_enumset1(A_157,B_158,C_159) = D_160
      | k2_tarski(A_157,C_159) = D_160
      | k2_tarski(B_158,C_159) = D_160
      | k2_tarski(A_157,B_158) = D_160
      | k1_tarski(C_159) = D_160
      | k1_tarski(B_158) = D_160
      | k1_tarski(A_157) = D_160
      | k1_xboole_0 = D_160
      | ~ r1_tarski(D_160,k1_enumset1(A_157,B_158,C_159)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_423,plain,(
    ! [A_3,B_4,D_160] :
      ( k1_enumset1(A_3,A_3,B_4) = D_160
      | k2_tarski(A_3,B_4) = D_160
      | k2_tarski(A_3,B_4) = D_160
      | k2_tarski(A_3,A_3) = D_160
      | k1_tarski(B_4) = D_160
      | k1_tarski(A_3) = D_160
      | k1_tarski(A_3) = D_160
      | k1_xboole_0 = D_160
      | ~ r1_tarski(D_160,k2_tarski(A_3,B_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_386])).

tff(c_456,plain,(
    ! [A_165,B_166,D_167] :
      ( k2_tarski(A_165,B_166) = D_167
      | k2_tarski(A_165,B_166) = D_167
      | k2_tarski(A_165,B_166) = D_167
      | k1_tarski(A_165) = D_167
      | k1_tarski(B_166) = D_167
      | k1_tarski(A_165) = D_167
      | k1_tarski(A_165) = D_167
      | k1_xboole_0 = D_167
      | ~ r1_tarski(D_167,k2_tarski(A_165,B_166)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_423])).

tff(c_478,plain,(
    ! [A_2,D_167] :
      ( k2_tarski(A_2,A_2) = D_167
      | k2_tarski(A_2,A_2) = D_167
      | k2_tarski(A_2,A_2) = D_167
      | k1_tarski(A_2) = D_167
      | k1_tarski(A_2) = D_167
      | k1_tarski(A_2) = D_167
      | k1_tarski(A_2) = D_167
      | k1_xboole_0 = D_167
      | ~ r1_tarski(D_167,k1_tarski(A_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_456])).

tff(c_498,plain,(
    ! [A_171,D_172] :
      ( k1_tarski(A_171) = D_172
      | k1_tarski(A_171) = D_172
      | k1_tarski(A_171) = D_172
      | k1_tarski(A_171) = D_172
      | k1_tarski(A_171) = D_172
      | k1_tarski(A_171) = D_172
      | k1_tarski(A_171) = D_172
      | k1_xboole_0 = D_172
      | ~ r1_tarski(D_172,k1_tarski(A_171)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_4,c_478])).

tff(c_507,plain,
    ( k1_tarski('#skF_2') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_219,c_498])).

tff(c_523,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_175,c_284,c_284,c_284,c_284,c_284,c_284,c_284,c_507])).

tff(c_524,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_30,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_531,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_524,c_30])).

tff(c_34,plain,(
    ! [A_14] :
      ( k2_relat_1(A_14) != k1_xboole_0
      | k1_xboole_0 = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_163,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_156,c_34])).

tff(c_174,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_526,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_174])).

tff(c_559,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_531,c_526])).

tff(c_560,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_32,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_605,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_560,c_32])).

tff(c_561,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_616,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_561])).

tff(c_40,plain,(
    ! [B_18,A_17] :
      ( k1_tarski(k1_funct_1(B_18,A_17)) = k2_relat_1(B_18)
      | k1_tarski(A_17) != k1_relat_1(B_18)
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_718,plain,(
    ! [A_219,B_220,C_221] :
      ( k2_relset_1(A_219,B_220,C_221) = k2_relat_1(C_221)
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(A_219,B_220))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_721,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_718])).

tff(c_723,plain,(
    k2_relset_1(k1_tarski('#skF_2'),'#skF_3','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_616,c_721])).

tff(c_754,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_2')) != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_723,c_60])).

tff(c_761,plain,
    ( k2_relat_1('#skF_4') != '#skF_4'
    | k1_tarski('#skF_2') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_754])).

tff(c_763,plain,(
    k1_tarski('#skF_2') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_68,c_605,c_616,c_761])).

tff(c_52,plain,(
    ! [A_30] :
      ( r2_hidden('#skF_1'(A_30),A_30)
      | k1_xboole_0 = A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_602,plain,(
    ! [A_30] :
      ( r2_hidden('#skF_1'(A_30),A_30)
      | A_30 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_52])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_604,plain,(
    ! [A_1] : r1_tarski('#skF_4',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_2])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_606,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_62])).

tff(c_66,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_58,plain,(
    ! [D_47,C_46,A_44,B_45] :
      ( r2_hidden(k1_funct_1(D_47,C_46),k2_relset_1(A_44,B_45,D_47))
      | k1_xboole_0 = B_45
      | ~ r2_hidden(C_46,A_44)
      | ~ m1_subset_1(D_47,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45)))
      | ~ v1_funct_2(D_47,A_44,B_45)
      | ~ v1_funct_1(D_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_765,plain,(
    ! [D_224,C_225,A_226,B_227] :
      ( r2_hidden(k1_funct_1(D_224,C_225),k2_relset_1(A_226,B_227,D_224))
      | B_227 = '#skF_4'
      | ~ r2_hidden(C_225,A_226)
      | ~ m1_subset_1(D_224,k1_zfmisc_1(k2_zfmisc_1(A_226,B_227)))
      | ~ v1_funct_2(D_224,A_226,B_227)
      | ~ v1_funct_1(D_224) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_58])).

tff(c_775,plain,(
    ! [C_225] :
      ( r2_hidden(k1_funct_1('#skF_4',C_225),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_225,k1_tarski('#skF_2'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_3')))
      | ~ v1_funct_2('#skF_4',k1_tarski('#skF_2'),'#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_723,c_765])).

tff(c_780,plain,(
    ! [C_225] :
      ( r2_hidden(k1_funct_1('#skF_4',C_225),'#skF_4')
      | '#skF_3' = '#skF_4'
      | ~ r2_hidden(C_225,k1_tarski('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_775])).

tff(c_782,plain,(
    ! [C_228] :
      ( r2_hidden(k1_funct_1('#skF_4',C_228),'#skF_4')
      | ~ r2_hidden(C_228,k1_tarski('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_606,c_780])).

tff(c_42,plain,(
    ! [B_20,A_19] :
      ( ~ r1_tarski(B_20,A_19)
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_789,plain,(
    ! [C_228] :
      ( ~ r1_tarski('#skF_4',k1_funct_1('#skF_4',C_228))
      | ~ r2_hidden(C_228,k1_tarski('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_782,c_42])).

tff(c_797,plain,(
    ! [C_229] : ~ r2_hidden(C_229,k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_604,c_789])).

tff(c_801,plain,(
    k1_tarski('#skF_2') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_602,c_797])).

tff(c_805,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_763,c_801])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:46:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.29/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.59  
% 3.29/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.59  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k3_mcart_1 > k2_relset_1 > k1_enumset1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.29/1.59  
% 3.29/1.59  %Foreground sorts:
% 3.29/1.59  
% 3.29/1.59  
% 3.29/1.59  %Background operators:
% 3.29/1.59  
% 3.29/1.59  
% 3.29/1.59  %Foreground operators:
% 3.29/1.59  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.29/1.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.29/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.29/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.29/1.59  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.29/1.59  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.29/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.29/1.59  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.29/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.29/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.29/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.29/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.29/1.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.29/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.29/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.29/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.29/1.59  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.29/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.29/1.59  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.29/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.29/1.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.29/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.29/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/1.59  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.29/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.29/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.29/1.59  
% 3.29/1.61  tff(f_148, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 3.29/1.61  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.29/1.61  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.29/1.61  tff(f_89, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.29/1.61  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.29/1.61  tff(f_104, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.29/1.61  tff(f_66, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.29/1.61  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 3.29/1.61  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.29/1.61  tff(f_31, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.29/1.61  tff(f_60, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 3.29/1.61  tff(f_69, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.29/1.61  tff(f_124, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 3.29/1.61  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.29/1.61  tff(f_136, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 3.29/1.61  tff(f_94, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.29/1.61  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.29/1.61  tff(c_152, plain, (![C_77, A_78, B_79]: (v1_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.29/1.61  tff(c_156, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_152])).
% 3.29/1.61  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.29/1.61  tff(c_36, plain, (![A_14]: (k1_relat_1(A_14)!=k1_xboole_0 | k1_xboole_0=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.29/1.61  tff(c_164, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_156, c_36])).
% 3.29/1.61  tff(c_175, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_164])).
% 3.29/1.61  tff(c_250, plain, (![B_119, A_120]: (k1_tarski(k1_funct_1(B_119, A_120))=k2_relat_1(B_119) | k1_tarski(A_120)!=k1_relat_1(B_119) | ~v1_funct_1(B_119) | ~v1_relat_1(B_119))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.29/1.61  tff(c_240, plain, (![A_116, B_117, C_118]: (k2_relset_1(A_116, B_117, C_118)=k2_relat_1(C_118) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.29/1.61  tff(c_244, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_240])).
% 3.29/1.61  tff(c_60, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')!=k1_tarski(k1_funct_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.29/1.61  tff(c_245, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_244, c_60])).
% 3.29/1.61  tff(c_256, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_250, c_245])).
% 3.29/1.61  tff(c_284, plain, (k1_tarski('#skF_2')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_68, c_256])).
% 3.29/1.61  tff(c_201, plain, (![C_96, A_97, B_98]: (v4_relat_1(C_96, A_97) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.29/1.61  tff(c_205, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_64, c_201])).
% 3.29/1.61  tff(c_28, plain, (![B_13, A_12]: (k7_relat_1(B_13, A_12)=B_13 | ~v4_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.29/1.61  tff(c_208, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_2'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_205, c_28])).
% 3.29/1.61  tff(c_211, plain, (k7_relat_1('#skF_4', k1_tarski('#skF_2'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_156, c_208])).
% 3.29/1.61  tff(c_38, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(k7_relat_1(B_16, A_15)), A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.29/1.61  tff(c_215, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_tarski('#skF_2')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_211, c_38])).
% 3.29/1.61  tff(c_219, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_215])).
% 3.29/1.61  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.29/1.61  tff(c_6, plain, (![A_3, B_4]: (k1_enumset1(A_3, A_3, B_4)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.29/1.61  tff(c_386, plain, (![A_157, B_158, C_159, D_160]: (k1_enumset1(A_157, B_158, C_159)=D_160 | k2_tarski(A_157, C_159)=D_160 | k2_tarski(B_158, C_159)=D_160 | k2_tarski(A_157, B_158)=D_160 | k1_tarski(C_159)=D_160 | k1_tarski(B_158)=D_160 | k1_tarski(A_157)=D_160 | k1_xboole_0=D_160 | ~r1_tarski(D_160, k1_enumset1(A_157, B_158, C_159)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.29/1.61  tff(c_423, plain, (![A_3, B_4, D_160]: (k1_enumset1(A_3, A_3, B_4)=D_160 | k2_tarski(A_3, B_4)=D_160 | k2_tarski(A_3, B_4)=D_160 | k2_tarski(A_3, A_3)=D_160 | k1_tarski(B_4)=D_160 | k1_tarski(A_3)=D_160 | k1_tarski(A_3)=D_160 | k1_xboole_0=D_160 | ~r1_tarski(D_160, k2_tarski(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_386])).
% 3.29/1.61  tff(c_456, plain, (![A_165, B_166, D_167]: (k2_tarski(A_165, B_166)=D_167 | k2_tarski(A_165, B_166)=D_167 | k2_tarski(A_165, B_166)=D_167 | k1_tarski(A_165)=D_167 | k1_tarski(B_166)=D_167 | k1_tarski(A_165)=D_167 | k1_tarski(A_165)=D_167 | k1_xboole_0=D_167 | ~r1_tarski(D_167, k2_tarski(A_165, B_166)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6, c_423])).
% 3.29/1.61  tff(c_478, plain, (![A_2, D_167]: (k2_tarski(A_2, A_2)=D_167 | k2_tarski(A_2, A_2)=D_167 | k2_tarski(A_2, A_2)=D_167 | k1_tarski(A_2)=D_167 | k1_tarski(A_2)=D_167 | k1_tarski(A_2)=D_167 | k1_tarski(A_2)=D_167 | k1_xboole_0=D_167 | ~r1_tarski(D_167, k1_tarski(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_456])).
% 3.29/1.61  tff(c_498, plain, (![A_171, D_172]: (k1_tarski(A_171)=D_172 | k1_tarski(A_171)=D_172 | k1_tarski(A_171)=D_172 | k1_tarski(A_171)=D_172 | k1_tarski(A_171)=D_172 | k1_tarski(A_171)=D_172 | k1_tarski(A_171)=D_172 | k1_xboole_0=D_172 | ~r1_tarski(D_172, k1_tarski(A_171)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_4, c_478])).
% 3.29/1.61  tff(c_507, plain, (k1_tarski('#skF_2')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_219, c_498])).
% 3.29/1.61  tff(c_523, plain, $false, inference(negUnitSimplification, [status(thm)], [c_175, c_284, c_284, c_284, c_284, c_284, c_284, c_284, c_507])).
% 3.29/1.61  tff(c_524, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_164])).
% 3.29/1.61  tff(c_30, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.29/1.61  tff(c_531, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_524, c_524, c_30])).
% 3.29/1.61  tff(c_34, plain, (![A_14]: (k2_relat_1(A_14)!=k1_xboole_0 | k1_xboole_0=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.29/1.61  tff(c_163, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_156, c_34])).
% 3.29/1.61  tff(c_174, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_163])).
% 3.29/1.61  tff(c_526, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_524, c_174])).
% 3.29/1.61  tff(c_559, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_531, c_526])).
% 3.29/1.61  tff(c_560, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_163])).
% 3.29/1.61  tff(c_32, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.29/1.61  tff(c_605, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_560, c_560, c_32])).
% 3.29/1.61  tff(c_561, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_163])).
% 3.29/1.61  tff(c_616, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_560, c_561])).
% 3.29/1.61  tff(c_40, plain, (![B_18, A_17]: (k1_tarski(k1_funct_1(B_18, A_17))=k2_relat_1(B_18) | k1_tarski(A_17)!=k1_relat_1(B_18) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.29/1.61  tff(c_718, plain, (![A_219, B_220, C_221]: (k2_relset_1(A_219, B_220, C_221)=k2_relat_1(C_221) | ~m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(A_219, B_220))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.29/1.61  tff(c_721, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_718])).
% 3.29/1.61  tff(c_723, plain, (k2_relset_1(k1_tarski('#skF_2'), '#skF_3', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_616, c_721])).
% 3.29/1.61  tff(c_754, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_2'))!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_723, c_60])).
% 3.29/1.61  tff(c_761, plain, (k2_relat_1('#skF_4')!='#skF_4' | k1_tarski('#skF_2')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_40, c_754])).
% 3.29/1.61  tff(c_763, plain, (k1_tarski('#skF_2')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_156, c_68, c_605, c_616, c_761])).
% 3.29/1.61  tff(c_52, plain, (![A_30]: (r2_hidden('#skF_1'(A_30), A_30) | k1_xboole_0=A_30)), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.29/1.61  tff(c_602, plain, (![A_30]: (r2_hidden('#skF_1'(A_30), A_30) | A_30='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_560, c_52])).
% 3.29/1.61  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.29/1.61  tff(c_604, plain, (![A_1]: (r1_tarski('#skF_4', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_560, c_2])).
% 3.29/1.61  tff(c_62, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.29/1.61  tff(c_606, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_560, c_62])).
% 3.29/1.61  tff(c_66, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_148])).
% 3.29/1.61  tff(c_58, plain, (![D_47, C_46, A_44, B_45]: (r2_hidden(k1_funct_1(D_47, C_46), k2_relset_1(A_44, B_45, D_47)) | k1_xboole_0=B_45 | ~r2_hidden(C_46, A_44) | ~m1_subset_1(D_47, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))) | ~v1_funct_2(D_47, A_44, B_45) | ~v1_funct_1(D_47))), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.29/1.61  tff(c_765, plain, (![D_224, C_225, A_226, B_227]: (r2_hidden(k1_funct_1(D_224, C_225), k2_relset_1(A_226, B_227, D_224)) | B_227='#skF_4' | ~r2_hidden(C_225, A_226) | ~m1_subset_1(D_224, k1_zfmisc_1(k2_zfmisc_1(A_226, B_227))) | ~v1_funct_2(D_224, A_226, B_227) | ~v1_funct_1(D_224))), inference(demodulation, [status(thm), theory('equality')], [c_560, c_58])).
% 3.29/1.61  tff(c_775, plain, (![C_225]: (r2_hidden(k1_funct_1('#skF_4', C_225), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_225, k1_tarski('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_tarski('#skF_2'), '#skF_3') | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_723, c_765])).
% 3.29/1.61  tff(c_780, plain, (![C_225]: (r2_hidden(k1_funct_1('#skF_4', C_225), '#skF_4') | '#skF_3'='#skF_4' | ~r2_hidden(C_225, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_775])).
% 3.29/1.61  tff(c_782, plain, (![C_228]: (r2_hidden(k1_funct_1('#skF_4', C_228), '#skF_4') | ~r2_hidden(C_228, k1_tarski('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_606, c_780])).
% 3.29/1.61  tff(c_42, plain, (![B_20, A_19]: (~r1_tarski(B_20, A_19) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.29/1.61  tff(c_789, plain, (![C_228]: (~r1_tarski('#skF_4', k1_funct_1('#skF_4', C_228)) | ~r2_hidden(C_228, k1_tarski('#skF_2')))), inference(resolution, [status(thm)], [c_782, c_42])).
% 3.29/1.61  tff(c_797, plain, (![C_229]: (~r2_hidden(C_229, k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_604, c_789])).
% 3.29/1.61  tff(c_801, plain, (k1_tarski('#skF_2')='#skF_4'), inference(resolution, [status(thm)], [c_602, c_797])).
% 3.29/1.61  tff(c_805, plain, $false, inference(negUnitSimplification, [status(thm)], [c_763, c_801])).
% 3.29/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.29/1.61  
% 3.29/1.61  Inference rules
% 3.29/1.61  ----------------------
% 3.29/1.61  #Ref     : 0
% 3.29/1.61  #Sup     : 163
% 3.29/1.61  #Fact    : 0
% 3.29/1.61  #Define  : 0
% 3.29/1.61  #Split   : 4
% 3.29/1.61  #Chain   : 0
% 3.29/1.61  #Close   : 0
% 3.29/1.61  
% 3.29/1.61  Ordering : KBO
% 3.29/1.61  
% 3.29/1.61  Simplification rules
% 3.29/1.61  ----------------------
% 3.29/1.61  #Subsume      : 20
% 3.29/1.61  #Demod        : 127
% 3.29/1.61  #Tautology    : 87
% 3.29/1.61  #SimpNegUnit  : 7
% 3.29/1.61  #BackRed      : 27
% 3.29/1.61  
% 3.29/1.61  #Partial instantiations: 0
% 3.29/1.61  #Strategies tried      : 1
% 3.29/1.61  
% 3.29/1.61  Timing (in seconds)
% 3.29/1.61  ----------------------
% 3.29/1.61  Preprocessing        : 0.36
% 3.29/1.61  Parsing              : 0.19
% 3.29/1.61  CNF conversion       : 0.02
% 3.29/1.61  Main loop            : 0.40
% 3.29/1.61  Inferencing          : 0.15
% 3.29/1.61  Reduction            : 0.13
% 3.29/1.61  Demodulation         : 0.09
% 3.29/1.61  BG Simplification    : 0.03
% 3.29/1.61  Subsumption          : 0.07
% 3.29/1.61  Abstraction          : 0.02
% 3.29/1.61  MUC search           : 0.00
% 3.29/1.61  Cooper               : 0.00
% 3.29/1.61  Total                : 0.81
% 3.29/1.61  Index Insertion      : 0.00
% 3.29/1.61  Index Deletion       : 0.00
% 3.29/1.61  Index Matching       : 0.00
% 3.29/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
