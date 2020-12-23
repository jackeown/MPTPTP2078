%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:22 EST 2020

% Result     : Theorem 15.80s
% Output     : CNFRefutation 15.86s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 362 expanded)
%              Number of leaves         :   54 ( 143 expanded)
%              Depth                    :   14
%              Number of atoms          :  164 ( 799 expanded)
%              Number of equality atoms :   80 ( 266 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_153,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_129,axiom,(
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

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_82,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_95,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_84,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_86,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_45,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_141,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(c_88,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_86,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_94,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_92,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_90,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_734,plain,(
    ! [A_144,B_145,C_146] :
      ( k1_relset_1(A_144,B_145,C_146) = k1_relat_1(C_146)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_745,plain,(
    k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_90,c_734])).

tff(c_2213,plain,(
    ! [B_325,A_326,C_327] :
      ( k1_xboole_0 = B_325
      | k1_relset_1(A_326,B_325,C_327) = A_326
      | ~ v1_funct_2(C_327,A_326,B_325)
      | ~ m1_subset_1(C_327,k1_zfmisc_1(k2_zfmisc_1(A_326,B_325))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2225,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4')
    | ~ v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_90,c_2213])).

tff(c_2233,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_tarski('#skF_4') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_745,c_2225])).

tff(c_2234,plain,(
    k1_tarski('#skF_4') = k1_relat_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_2233])).

tff(c_2252,plain,(
    v1_funct_2('#skF_6',k1_relat_1('#skF_6'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2234,c_92])).

tff(c_2251,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),'#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2234,c_90])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_36,plain,(
    ! [C_45,A_41] :
      ( r2_hidden(C_45,k1_zfmisc_1(A_41))
      | ~ r1_tarski(C_45,A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4,plain,(
    ! [A_3] :
      ( r2_hidden('#skF_1'(A_3),A_3)
      | k1_xboole_0 = A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_637,plain,(
    ! [C_131,A_132,B_133] :
      ( r2_hidden(C_131,A_132)
      | ~ r2_hidden(C_131,B_133)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(A_132)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_644,plain,(
    ! [A_134,A_135] :
      ( r2_hidden('#skF_1'(A_134),A_135)
      | ~ m1_subset_1(A_134,k1_zfmisc_1(A_135))
      | k1_xboole_0 = A_134 ) ),
    inference(resolution,[status(thm)],[c_4,c_637])).

tff(c_66,plain,(
    ! [A_61,B_62,C_63] :
      ( r2_hidden(k1_mcart_1(A_61),B_62)
      | ~ r2_hidden(A_61,k2_zfmisc_1(B_62,C_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_938,plain,(
    ! [A_179,B_180,C_181] :
      ( r2_hidden(k1_mcart_1('#skF_1'(A_179)),B_180)
      | ~ m1_subset_1(A_179,k1_zfmisc_1(k2_zfmisc_1(B_180,C_181)))
      | k1_xboole_0 = A_179 ) ),
    inference(resolution,[status(thm)],[c_644,c_66])).

tff(c_949,plain,
    ( r2_hidden(k1_mcart_1('#skF_1'('#skF_6')),k1_tarski('#skF_4'))
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_90,c_938])).

tff(c_952,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_949])).

tff(c_981,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_952,c_88])).

tff(c_60,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_52,plain,(
    ! [A_52] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_52)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_744,plain,(
    ! [A_144,B_145] : k1_relset_1(A_144,B_145,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_52,c_734])).

tff(c_747,plain,(
    ! [A_144,B_145] : k1_relset_1(A_144,B_145,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_744])).

tff(c_963,plain,(
    ! [A_144,B_145] : k1_relset_1(A_144,B_145,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_952,c_952,c_747])).

tff(c_976,plain,(
    ! [A_52] : m1_subset_1('#skF_6',k1_zfmisc_1(A_52)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_952,c_52])).

tff(c_82,plain,(
    ! [B_68,A_67,C_69] :
      ( k1_xboole_0 = B_68
      | k1_relset_1(A_67,B_68,C_69) = A_67
      | ~ v1_funct_2(C_69,A_67,B_68)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1302,plain,(
    ! [B_206,A_207,C_208] :
      ( B_206 = '#skF_6'
      | k1_relset_1(A_207,B_206,C_208) = A_207
      | ~ v1_funct_2(C_208,A_207,B_206)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(A_207,B_206))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_952,c_82])).

tff(c_1306,plain,(
    ! [B_206,A_207] :
      ( B_206 = '#skF_6'
      | k1_relset_1(A_207,B_206,'#skF_6') = A_207
      | ~ v1_funct_2('#skF_6',A_207,B_206) ) ),
    inference(resolution,[status(thm)],[c_976,c_1302])).

tff(c_1383,plain,(
    ! [B_217,A_218] :
      ( B_217 = '#skF_6'
      | A_218 = '#skF_6'
      | ~ v1_funct_2('#skF_6',A_218,B_217) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_963,c_1306])).

tff(c_1389,plain,
    ( '#skF_5' = '#skF_6'
    | k1_tarski('#skF_4') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_92,c_1383])).

tff(c_1394,plain,(
    k1_tarski('#skF_4') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_981,c_1389])).

tff(c_18,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_255,plain,(
    ! [A_86,B_87] : k1_setfam_1(k2_tarski(A_86,B_87)) = k3_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_317,plain,(
    ! [B_97,A_98] : k1_setfam_1(k2_tarski(B_97,A_98)) = k3_xboole_0(A_98,B_97) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_255])).

tff(c_54,plain,(
    ! [A_53,B_54] : k1_setfam_1(k2_tarski(A_53,B_54)) = k3_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_343,plain,(
    ! [B_99,A_100] : k3_xboole_0(B_99,A_100) = k3_xboole_0(A_100,B_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_54])).

tff(c_14,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_359,plain,(
    ! [A_100] : k3_xboole_0(k1_xboole_0,A_100) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_14])).

tff(c_133,plain,(
    ! [B_79,A_80] : k5_xboole_0(B_79,A_80) = k5_xboole_0(A_80,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_149,plain,(
    ! [A_80] : k5_xboole_0(k1_xboole_0,A_80) = A_80 ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_16])).

tff(c_423,plain,(
    ! [A_102,B_103] : k5_xboole_0(A_102,k3_xboole_0(A_102,B_103)) = k4_xboole_0(A_102,B_103) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_449,plain,(
    ! [B_103] : k4_xboole_0(k1_xboole_0,B_103) = k3_xboole_0(k1_xboole_0,B_103) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_423])).

tff(c_457,plain,(
    ! [B_103] : k4_xboole_0(k1_xboole_0,B_103) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_449])).

tff(c_970,plain,(
    ! [B_103] : k4_xboole_0('#skF_6',B_103) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_952,c_952,c_457])).

tff(c_46,plain,(
    ! [A_46,B_47] :
      ( ~ r2_hidden(A_46,B_47)
      | k4_xboole_0(k1_tarski(A_46),B_47) != k1_tarski(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1399,plain,(
    ! [B_47] :
      ( ~ r2_hidden('#skF_4',B_47)
      | k4_xboole_0('#skF_6',B_47) != k1_tarski('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1394,c_46])).

tff(c_1419,plain,(
    ! [B_219] : ~ r2_hidden('#skF_4',B_219) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1394,c_970,c_1399])).

tff(c_1425,plain,(
    ! [A_220] : ~ r1_tarski('#skF_4',A_220) ),
    inference(resolution,[status(thm)],[c_36,c_1419])).

tff(c_1430,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_10,c_1425])).

tff(c_1432,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_949])).

tff(c_70,plain,(
    ! [A_64,B_65,C_66] :
      ( k1_mcart_1(A_64) = B_65
      | ~ r2_hidden(A_64,k2_zfmisc_1(k1_tarski(B_65),C_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1571,plain,(
    ! [A_246,B_247,C_248] :
      ( k1_mcart_1('#skF_1'(A_246)) = B_247
      | ~ m1_subset_1(A_246,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(B_247),C_248)))
      | k1_xboole_0 = A_246 ) ),
    inference(resolution,[status(thm)],[c_644,c_70])).

tff(c_1577,plain,
    ( k1_mcart_1('#skF_1'('#skF_6')) = '#skF_4'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_90,c_1571])).

tff(c_1584,plain,(
    k1_mcart_1('#skF_1'('#skF_6')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_1432,c_1577])).

tff(c_1431,plain,(
    r2_hidden(k1_mcart_1('#skF_1'('#skF_6')),k1_tarski('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_949])).

tff(c_1591,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1584,c_1431])).

tff(c_2247,plain,(
    r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2234,c_1591])).

tff(c_2341,plain,(
    ! [D_328,C_329,B_330,A_331] :
      ( r2_hidden(k1_funct_1(D_328,C_329),B_330)
      | k1_xboole_0 = B_330
      | ~ r2_hidden(C_329,A_331)
      | ~ m1_subset_1(D_328,k1_zfmisc_1(k2_zfmisc_1(A_331,B_330)))
      | ~ v1_funct_2(D_328,A_331,B_330)
      | ~ v1_funct_1(D_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_45106,plain,(
    ! [D_1087,B_1088] :
      ( r2_hidden(k1_funct_1(D_1087,'#skF_4'),B_1088)
      | k1_xboole_0 = B_1088
      | ~ m1_subset_1(D_1087,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),B_1088)))
      | ~ v1_funct_2(D_1087,k1_relat_1('#skF_6'),B_1088)
      | ~ v1_funct_1(D_1087) ) ),
    inference(resolution,[status(thm)],[c_2247,c_2341])).

tff(c_45181,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5')
    | k1_xboole_0 = '#skF_5'
    | ~ v1_funct_2('#skF_6',k1_relat_1('#skF_6'),'#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2251,c_45106])).

tff(c_45192,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_2252,c_45181])).

tff(c_45194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_86,c_45192])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:46:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.80/8.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.86/8.16  
% 15.86/8.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.86/8.17  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 15.86/8.17  
% 15.86/8.17  %Foreground sorts:
% 15.86/8.17  
% 15.86/8.17  
% 15.86/8.17  %Background operators:
% 15.86/8.17  
% 15.86/8.17  
% 15.86/8.17  %Foreground operators:
% 15.86/8.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 15.86/8.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.86/8.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 15.86/8.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 15.86/8.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 15.86/8.17  tff('#skF_1', type, '#skF_1': $i > $i).
% 15.86/8.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.86/8.17  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 15.86/8.17  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 15.86/8.17  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 15.86/8.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.86/8.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 15.86/8.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 15.86/8.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 15.86/8.17  tff('#skF_5', type, '#skF_5': $i).
% 15.86/8.17  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 15.86/8.17  tff('#skF_6', type, '#skF_6': $i).
% 15.86/8.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 15.86/8.17  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 15.86/8.17  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 15.86/8.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.86/8.17  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 15.86/8.17  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 15.86/8.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.86/8.17  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 15.86/8.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 15.86/8.17  tff('#skF_4', type, '#skF_4': $i).
% 15.86/8.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.86/8.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 15.86/8.17  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 15.86/8.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 15.86/8.17  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 15.86/8.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 15.86/8.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.86/8.17  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 15.86/8.17  
% 15.86/8.18  tff(f_153, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 15.86/8.18  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 15.86/8.18  tff(f_129, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 15.86/8.18  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.86/8.18  tff(f_70, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 15.86/8.18  tff(f_35, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 15.86/8.18  tff(f_82, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 15.86/8.18  tff(f_105, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 15.86/8.18  tff(f_95, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 15.86/8.18  tff(f_84, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 15.86/8.18  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 15.86/8.18  tff(f_86, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 15.86/8.18  tff(f_45, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 15.86/8.18  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 15.86/8.18  tff(f_47, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 15.86/8.18  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 15.86/8.18  tff(f_75, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 15.86/8.18  tff(f_111, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_mcart_1)).
% 15.86/8.18  tff(f_141, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 15.86/8.18  tff(c_88, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_153])).
% 15.86/8.18  tff(c_86, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_153])).
% 15.86/8.18  tff(c_94, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_153])).
% 15.86/8.18  tff(c_92, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_153])).
% 15.86/8.18  tff(c_90, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 15.86/8.18  tff(c_734, plain, (![A_144, B_145, C_146]: (k1_relset_1(A_144, B_145, C_146)=k1_relat_1(C_146) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 15.86/8.18  tff(c_745, plain, (k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_90, c_734])).
% 15.86/8.18  tff(c_2213, plain, (![B_325, A_326, C_327]: (k1_xboole_0=B_325 | k1_relset_1(A_326, B_325, C_327)=A_326 | ~v1_funct_2(C_327, A_326, B_325) | ~m1_subset_1(C_327, k1_zfmisc_1(k2_zfmisc_1(A_326, B_325))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 15.86/8.18  tff(c_2225, plain, (k1_xboole_0='#skF_5' | k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4') | ~v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_90, c_2213])).
% 15.86/8.18  tff(c_2233, plain, (k1_xboole_0='#skF_5' | k1_tarski('#skF_4')=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_745, c_2225])).
% 15.86/8.18  tff(c_2234, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_88, c_2233])).
% 15.86/8.18  tff(c_2252, plain, (v1_funct_2('#skF_6', k1_relat_1('#skF_6'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2234, c_92])).
% 15.86/8.18  tff(c_2251, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_2234, c_90])).
% 15.86/8.18  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 15.86/8.18  tff(c_36, plain, (![C_45, A_41]: (r2_hidden(C_45, k1_zfmisc_1(A_41)) | ~r1_tarski(C_45, A_41))), inference(cnfTransformation, [status(thm)], [f_70])).
% 15.86/8.18  tff(c_4, plain, (![A_3]: (r2_hidden('#skF_1'(A_3), A_3) | k1_xboole_0=A_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 15.86/8.18  tff(c_637, plain, (![C_131, A_132, B_133]: (r2_hidden(C_131, A_132) | ~r2_hidden(C_131, B_133) | ~m1_subset_1(B_133, k1_zfmisc_1(A_132)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 15.86/8.18  tff(c_644, plain, (![A_134, A_135]: (r2_hidden('#skF_1'(A_134), A_135) | ~m1_subset_1(A_134, k1_zfmisc_1(A_135)) | k1_xboole_0=A_134)), inference(resolution, [status(thm)], [c_4, c_637])).
% 15.86/8.18  tff(c_66, plain, (![A_61, B_62, C_63]: (r2_hidden(k1_mcart_1(A_61), B_62) | ~r2_hidden(A_61, k2_zfmisc_1(B_62, C_63)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 15.86/8.18  tff(c_938, plain, (![A_179, B_180, C_181]: (r2_hidden(k1_mcart_1('#skF_1'(A_179)), B_180) | ~m1_subset_1(A_179, k1_zfmisc_1(k2_zfmisc_1(B_180, C_181))) | k1_xboole_0=A_179)), inference(resolution, [status(thm)], [c_644, c_66])).
% 15.86/8.18  tff(c_949, plain, (r2_hidden(k1_mcart_1('#skF_1'('#skF_6')), k1_tarski('#skF_4')) | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_90, c_938])).
% 15.86/8.18  tff(c_952, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_949])).
% 15.86/8.18  tff(c_981, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_952, c_88])).
% 15.86/8.18  tff(c_60, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_95])).
% 15.86/8.18  tff(c_52, plain, (![A_52]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 15.86/8.18  tff(c_744, plain, (![A_144, B_145]: (k1_relset_1(A_144, B_145, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_52, c_734])).
% 15.86/8.18  tff(c_747, plain, (![A_144, B_145]: (k1_relset_1(A_144, B_145, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_744])).
% 15.86/8.18  tff(c_963, plain, (![A_144, B_145]: (k1_relset_1(A_144, B_145, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_952, c_952, c_747])).
% 15.86/8.18  tff(c_976, plain, (![A_52]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_52)))), inference(demodulation, [status(thm), theory('equality')], [c_952, c_52])).
% 15.86/8.18  tff(c_82, plain, (![B_68, A_67, C_69]: (k1_xboole_0=B_68 | k1_relset_1(A_67, B_68, C_69)=A_67 | ~v1_funct_2(C_69, A_67, B_68) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 15.86/8.18  tff(c_1302, plain, (![B_206, A_207, C_208]: (B_206='#skF_6' | k1_relset_1(A_207, B_206, C_208)=A_207 | ~v1_funct_2(C_208, A_207, B_206) | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(A_207, B_206))))), inference(demodulation, [status(thm), theory('equality')], [c_952, c_82])).
% 15.86/8.18  tff(c_1306, plain, (![B_206, A_207]: (B_206='#skF_6' | k1_relset_1(A_207, B_206, '#skF_6')=A_207 | ~v1_funct_2('#skF_6', A_207, B_206))), inference(resolution, [status(thm)], [c_976, c_1302])).
% 15.86/8.18  tff(c_1383, plain, (![B_217, A_218]: (B_217='#skF_6' | A_218='#skF_6' | ~v1_funct_2('#skF_6', A_218, B_217))), inference(demodulation, [status(thm), theory('equality')], [c_963, c_1306])).
% 15.86/8.18  tff(c_1389, plain, ('#skF_5'='#skF_6' | k1_tarski('#skF_4')='#skF_6'), inference(resolution, [status(thm)], [c_92, c_1383])).
% 15.86/8.18  tff(c_1394, plain, (k1_tarski('#skF_4')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_981, c_1389])).
% 15.86/8.18  tff(c_18, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 15.86/8.18  tff(c_255, plain, (![A_86, B_87]: (k1_setfam_1(k2_tarski(A_86, B_87))=k3_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_86])).
% 15.86/8.18  tff(c_317, plain, (![B_97, A_98]: (k1_setfam_1(k2_tarski(B_97, A_98))=k3_xboole_0(A_98, B_97))), inference(superposition, [status(thm), theory('equality')], [c_18, c_255])).
% 15.86/8.18  tff(c_54, plain, (![A_53, B_54]: (k1_setfam_1(k2_tarski(A_53, B_54))=k3_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_86])).
% 15.86/8.18  tff(c_343, plain, (![B_99, A_100]: (k3_xboole_0(B_99, A_100)=k3_xboole_0(A_100, B_99))), inference(superposition, [status(thm), theory('equality')], [c_317, c_54])).
% 15.86/8.18  tff(c_14, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 15.86/8.18  tff(c_359, plain, (![A_100]: (k3_xboole_0(k1_xboole_0, A_100)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_343, c_14])).
% 15.86/8.18  tff(c_133, plain, (![B_79, A_80]: (k5_xboole_0(B_79, A_80)=k5_xboole_0(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_27])).
% 15.86/8.18  tff(c_16, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_47])).
% 15.86/8.18  tff(c_149, plain, (![A_80]: (k5_xboole_0(k1_xboole_0, A_80)=A_80)), inference(superposition, [status(thm), theory('equality')], [c_133, c_16])).
% 15.86/8.18  tff(c_423, plain, (![A_102, B_103]: (k5_xboole_0(A_102, k3_xboole_0(A_102, B_103))=k4_xboole_0(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_43])).
% 15.86/8.18  tff(c_449, plain, (![B_103]: (k4_xboole_0(k1_xboole_0, B_103)=k3_xboole_0(k1_xboole_0, B_103))), inference(superposition, [status(thm), theory('equality')], [c_149, c_423])).
% 15.86/8.18  tff(c_457, plain, (![B_103]: (k4_xboole_0(k1_xboole_0, B_103)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_359, c_449])).
% 15.86/8.18  tff(c_970, plain, (![B_103]: (k4_xboole_0('#skF_6', B_103)='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_952, c_952, c_457])).
% 15.86/8.18  tff(c_46, plain, (![A_46, B_47]: (~r2_hidden(A_46, B_47) | k4_xboole_0(k1_tarski(A_46), B_47)!=k1_tarski(A_46))), inference(cnfTransformation, [status(thm)], [f_75])).
% 15.86/8.18  tff(c_1399, plain, (![B_47]: (~r2_hidden('#skF_4', B_47) | k4_xboole_0('#skF_6', B_47)!=k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1394, c_46])).
% 15.86/8.18  tff(c_1419, plain, (![B_219]: (~r2_hidden('#skF_4', B_219))), inference(demodulation, [status(thm), theory('equality')], [c_1394, c_970, c_1399])).
% 15.86/8.18  tff(c_1425, plain, (![A_220]: (~r1_tarski('#skF_4', A_220))), inference(resolution, [status(thm)], [c_36, c_1419])).
% 15.86/8.18  tff(c_1430, plain, $false, inference(resolution, [status(thm)], [c_10, c_1425])).
% 15.86/8.18  tff(c_1432, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_949])).
% 15.86/8.18  tff(c_70, plain, (![A_64, B_65, C_66]: (k1_mcart_1(A_64)=B_65 | ~r2_hidden(A_64, k2_zfmisc_1(k1_tarski(B_65), C_66)))), inference(cnfTransformation, [status(thm)], [f_111])).
% 15.86/8.18  tff(c_1571, plain, (![A_246, B_247, C_248]: (k1_mcart_1('#skF_1'(A_246))=B_247 | ~m1_subset_1(A_246, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(B_247), C_248))) | k1_xboole_0=A_246)), inference(resolution, [status(thm)], [c_644, c_70])).
% 15.86/8.18  tff(c_1577, plain, (k1_mcart_1('#skF_1'('#skF_6'))='#skF_4' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_90, c_1571])).
% 15.86/8.18  tff(c_1584, plain, (k1_mcart_1('#skF_1'('#skF_6'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_1432, c_1577])).
% 15.86/8.18  tff(c_1431, plain, (r2_hidden(k1_mcart_1('#skF_1'('#skF_6')), k1_tarski('#skF_4'))), inference(splitRight, [status(thm)], [c_949])).
% 15.86/8.18  tff(c_1591, plain, (r2_hidden('#skF_4', k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1584, c_1431])).
% 15.86/8.18  tff(c_2247, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2234, c_1591])).
% 15.86/8.18  tff(c_2341, plain, (![D_328, C_329, B_330, A_331]: (r2_hidden(k1_funct_1(D_328, C_329), B_330) | k1_xboole_0=B_330 | ~r2_hidden(C_329, A_331) | ~m1_subset_1(D_328, k1_zfmisc_1(k2_zfmisc_1(A_331, B_330))) | ~v1_funct_2(D_328, A_331, B_330) | ~v1_funct_1(D_328))), inference(cnfTransformation, [status(thm)], [f_141])).
% 15.86/8.18  tff(c_45106, plain, (![D_1087, B_1088]: (r2_hidden(k1_funct_1(D_1087, '#skF_4'), B_1088) | k1_xboole_0=B_1088 | ~m1_subset_1(D_1087, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), B_1088))) | ~v1_funct_2(D_1087, k1_relat_1('#skF_6'), B_1088) | ~v1_funct_1(D_1087))), inference(resolution, [status(thm)], [c_2247, c_2341])).
% 15.86/8.18  tff(c_45181, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5') | k1_xboole_0='#skF_5' | ~v1_funct_2('#skF_6', k1_relat_1('#skF_6'), '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_2251, c_45106])).
% 15.86/8.18  tff(c_45192, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_2252, c_45181])).
% 15.86/8.18  tff(c_45194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_86, c_45192])).
% 15.86/8.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.86/8.18  
% 15.86/8.18  Inference rules
% 15.86/8.18  ----------------------
% 15.86/8.18  #Ref     : 0
% 15.86/8.18  #Sup     : 11730
% 15.86/8.18  #Fact    : 8
% 15.86/8.18  #Define  : 0
% 15.86/8.18  #Split   : 13
% 15.86/8.18  #Chain   : 0
% 15.86/8.18  #Close   : 0
% 15.86/8.18  
% 15.86/8.18  Ordering : KBO
% 15.86/8.18  
% 15.86/8.18  Simplification rules
% 15.86/8.18  ----------------------
% 15.86/8.18  #Subsume      : 4598
% 15.86/8.18  #Demod        : 8265
% 15.86/8.18  #Tautology    : 4224
% 15.86/8.18  #SimpNegUnit  : 106
% 15.86/8.18  #BackRed      : 56
% 15.86/8.18  
% 15.86/8.18  #Partial instantiations: 0
% 15.86/8.18  #Strategies tried      : 1
% 15.86/8.18  
% 15.86/8.18  Timing (in seconds)
% 15.86/8.18  ----------------------
% 15.86/8.19  Preprocessing        : 0.37
% 15.86/8.19  Parsing              : 0.20
% 15.86/8.19  CNF conversion       : 0.03
% 15.86/8.19  Main loop            : 7.02
% 15.86/8.19  Inferencing          : 1.52
% 15.86/8.19  Reduction            : 2.59
% 15.86/8.19  Demodulation         : 1.89
% 15.86/8.19  BG Simplification    : 0.14
% 15.86/8.19  Subsumption          : 2.48
% 15.86/8.19  Abstraction          : 0.26
% 15.86/8.19  MUC search           : 0.00
% 15.86/8.19  Cooper               : 0.00
% 15.86/8.19  Total                : 7.43
% 15.86/8.19  Index Insertion      : 0.00
% 15.86/8.19  Index Deletion       : 0.00
% 15.86/8.19  Index Matching       : 0.00
% 15.86/8.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
