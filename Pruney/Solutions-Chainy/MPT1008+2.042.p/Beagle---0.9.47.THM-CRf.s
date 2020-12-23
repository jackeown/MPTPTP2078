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
% DateTime   : Thu Dec  3 10:14:31 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 212 expanded)
%              Number of leaves         :   45 (  90 expanded)
%              Depth                    :   10
%              Number of atoms          :  150 ( 426 expanded)
%              Number of equality atoms :   70 ( 184 expanded)
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

tff(f_146,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_134,axiom,(
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

tff(f_116,axiom,(
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

tff(f_100,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_68,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_113,plain,(
    ! [C_73,A_74,B_75] :
      ( v1_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_121,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_113])).

tff(c_72,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_26,plain,(
    ! [A_16] :
      ( k1_relat_1(A_16) != k1_xboole_0
      | k1_xboole_0 = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_129,plain,
    ( k1_relat_1('#skF_6') != k1_xboole_0
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_121,c_26])).

tff(c_141,plain,(
    k1_relat_1('#skF_6') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_129])).

tff(c_169,plain,(
    ! [C_85,A_86,B_87] :
      ( v4_relat_1(C_85,A_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_177,plain,(
    v4_relat_1('#skF_6',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_68,c_169])).

tff(c_22,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k1_relat_1(B_15),A_14)
      | ~ v4_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_185,plain,(
    ! [B_91,A_92] :
      ( k1_tarski(B_91) = A_92
      | k1_xboole_0 = A_92
      | ~ r1_tarski(A_92,k1_tarski(B_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_282,plain,(
    ! [B_121,B_122] :
      ( k1_tarski(B_121) = k1_relat_1(B_122)
      | k1_relat_1(B_122) = k1_xboole_0
      | ~ v4_relat_1(B_122,k1_tarski(B_121))
      | ~ v1_relat_1(B_122) ) ),
    inference(resolution,[status(thm)],[c_22,c_185])).

tff(c_289,plain,
    ( k1_tarski('#skF_4') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_177,c_282])).

tff(c_295,plain,
    ( k1_tarski('#skF_4') = k1_relat_1('#skF_6')
    | k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_289])).

tff(c_296,plain,(
    k1_tarski('#skF_4') = k1_relat_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_295])).

tff(c_356,plain,(
    ! [B_123,A_124] :
      ( k1_tarski(k1_funct_1(B_123,A_124)) = k2_relat_1(B_123)
      | k1_tarski(A_124) != k1_relat_1(B_123)
      | ~ v1_funct_1(B_123)
      | ~ v1_relat_1(B_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_253,plain,(
    ! [A_114,B_115,C_116] :
      ( k2_relset_1(A_114,B_115,C_116) = k2_relat_1(C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_261,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_253])).

tff(c_64,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') != k1_tarski(k1_funct_1('#skF_6','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_270,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_4')) != k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_64])).

tff(c_365,plain,
    ( k1_tarski('#skF_4') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_356,c_270])).

tff(c_382,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_72,c_296,c_365])).

tff(c_383,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_384,plain,(
    k1_relat_1('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_129])).

tff(c_399,plain,(
    k1_relat_1('#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_384])).

tff(c_28,plain,(
    ! [B_18,A_17] :
      ( k1_tarski(k1_funct_1(B_18,A_17)) = k2_relat_1(B_18)
      | k1_tarski(A_17) != k1_relat_1(B_18)
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_16,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_391,plain,(
    ! [A_10] : m1_subset_1('#skF_6',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_16])).

tff(c_539,plain,(
    ! [A_169,B_170,C_171] :
      ( k2_relset_1(A_169,B_170,C_171) = k2_relat_1(C_171)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_544,plain,(
    ! [A_169,B_170] : k2_relset_1(A_169,B_170,'#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_391,c_539])).

tff(c_545,plain,(
    k1_tarski(k1_funct_1('#skF_6','#skF_4')) != k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_544,c_64])).

tff(c_573,plain,
    ( k1_tarski('#skF_4') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_545])).

tff(c_576,plain,(
    k1_tarski('#skF_4') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_72,c_399,c_573])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_393,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_66])).

tff(c_70,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_62,plain,(
    ! [B_58,A_57,C_59] :
      ( k1_xboole_0 = B_58
      | k1_relset_1(A_57,B_58,C_59) = A_57
      | ~ v1_funct_2(C_59,A_57,B_58)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_631,plain,(
    ! [B_188,A_189,C_190] :
      ( B_188 = '#skF_6'
      | k1_relset_1(A_189,B_188,C_190) = A_189
      | ~ v1_funct_2(C_190,A_189,B_188)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_189,B_188))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_62])).

tff(c_637,plain,(
    ! [B_191,A_192] :
      ( B_191 = '#skF_6'
      | k1_relset_1(A_192,B_191,'#skF_6') = A_192
      | ~ v1_funct_2('#skF_6',A_192,B_191) ) ),
    inference(resolution,[status(thm)],[c_391,c_631])).

tff(c_646,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_637])).

tff(c_652,plain,(
    k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_393,c_646])).

tff(c_46,plain,(
    ! [A_43] :
      ( r2_hidden('#skF_3'(A_43),A_43)
      | k1_xboole_0 = A_43 ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_390,plain,(
    ! [A_43] :
      ( r2_hidden('#skF_3'(A_43),A_43)
      | A_43 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_46])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_392,plain,(
    ! [A_1] : r1_tarski('#skF_6',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_2])).

tff(c_791,plain,(
    ! [D_216,A_217,B_218,C_219] :
      ( r2_hidden(k4_tarski(D_216,'#skF_2'(A_217,B_218,C_219,D_216)),C_219)
      | ~ r2_hidden(D_216,B_218)
      | k1_relset_1(B_218,A_217,C_219) != B_218
      | ~ m1_subset_1(C_219,k1_zfmisc_1(k2_zfmisc_1(B_218,A_217))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_30,plain,(
    ! [B_20,A_19] :
      ( ~ r1_tarski(B_20,A_19)
      | ~ r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_818,plain,(
    ! [C_228,D_229,A_230,B_231] :
      ( ~ r1_tarski(C_228,k4_tarski(D_229,'#skF_2'(A_230,B_231,C_228,D_229)))
      | ~ r2_hidden(D_229,B_231)
      | k1_relset_1(B_231,A_230,C_228) != B_231
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1(B_231,A_230))) ) ),
    inference(resolution,[status(thm)],[c_791,c_30])).

tff(c_826,plain,(
    ! [D_229,B_231,A_230] :
      ( ~ r2_hidden(D_229,B_231)
      | k1_relset_1(B_231,A_230,'#skF_6') != B_231
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(B_231,A_230))) ) ),
    inference(resolution,[status(thm)],[c_392,c_818])).

tff(c_831,plain,(
    ! [D_232,B_233,A_234] :
      ( ~ r2_hidden(D_232,B_233)
      | k1_relset_1(B_233,A_234,'#skF_6') != B_233 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_391,c_826])).

tff(c_841,plain,(
    ! [A_235,A_236] :
      ( k1_relset_1(A_235,A_236,'#skF_6') != A_235
      | A_235 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_390,c_831])).

tff(c_847,plain,(
    k1_tarski('#skF_4') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_652,c_841])).

tff(c_853,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_576,c_847])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:14:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.44  
% 3.15/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.44  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k3_mcart_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3
% 3.15/1.44  
% 3.15/1.44  %Foreground sorts:
% 3.15/1.44  
% 3.15/1.44  
% 3.15/1.44  %Background operators:
% 3.15/1.44  
% 3.15/1.44  
% 3.15/1.44  %Foreground operators:
% 3.15/1.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.15/1.44  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.15/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.15/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.15/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.15/1.44  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.15/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.15/1.44  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.15/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.15/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.15/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.15/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.15/1.44  tff('#skF_5', type, '#skF_5': $i).
% 3.15/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.15/1.44  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.15/1.44  tff('#skF_6', type, '#skF_6': $i).
% 3.15/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.15/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.15/1.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.15/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.15/1.44  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.15/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.15/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.15/1.44  tff('#skF_4', type, '#skF_4': $i).
% 3.15/1.44  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.15/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.15/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.15/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.15/1.44  
% 3.15/1.46  tff(f_146, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 3.15/1.46  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.15/1.46  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.15/1.46  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.15/1.46  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.15/1.46  tff(f_39, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.15/1.46  tff(f_69, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.15/1.46  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.15/1.46  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.15/1.46  tff(f_134, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.15/1.46  tff(f_116, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k3_mcart_1(C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_mcart_1)).
% 3.15/1.46  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.15/1.46  tff(f_100, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 3.15/1.46  tff(f_74, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.15/1.46  tff(c_68, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.15/1.46  tff(c_113, plain, (![C_73, A_74, B_75]: (v1_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.15/1.46  tff(c_121, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_68, c_113])).
% 3.15/1.46  tff(c_72, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.15/1.46  tff(c_26, plain, (![A_16]: (k1_relat_1(A_16)!=k1_xboole_0 | k1_xboole_0=A_16 | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.15/1.46  tff(c_129, plain, (k1_relat_1('#skF_6')!=k1_xboole_0 | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_121, c_26])).
% 3.15/1.46  tff(c_141, plain, (k1_relat_1('#skF_6')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_129])).
% 3.15/1.46  tff(c_169, plain, (![C_85, A_86, B_87]: (v4_relat_1(C_85, A_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.15/1.46  tff(c_177, plain, (v4_relat_1('#skF_6', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_68, c_169])).
% 3.15/1.46  tff(c_22, plain, (![B_15, A_14]: (r1_tarski(k1_relat_1(B_15), A_14) | ~v4_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.15/1.46  tff(c_185, plain, (![B_91, A_92]: (k1_tarski(B_91)=A_92 | k1_xboole_0=A_92 | ~r1_tarski(A_92, k1_tarski(B_91)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.15/1.46  tff(c_282, plain, (![B_121, B_122]: (k1_tarski(B_121)=k1_relat_1(B_122) | k1_relat_1(B_122)=k1_xboole_0 | ~v4_relat_1(B_122, k1_tarski(B_121)) | ~v1_relat_1(B_122))), inference(resolution, [status(thm)], [c_22, c_185])).
% 3.15/1.46  tff(c_289, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0 | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_177, c_282])).
% 3.15/1.46  tff(c_295, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6') | k1_relat_1('#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_121, c_289])).
% 3.15/1.46  tff(c_296, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_141, c_295])).
% 3.15/1.46  tff(c_356, plain, (![B_123, A_124]: (k1_tarski(k1_funct_1(B_123, A_124))=k2_relat_1(B_123) | k1_tarski(A_124)!=k1_relat_1(B_123) | ~v1_funct_1(B_123) | ~v1_relat_1(B_123))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.15/1.46  tff(c_253, plain, (![A_114, B_115, C_116]: (k2_relset_1(A_114, B_115, C_116)=k2_relat_1(C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.15/1.46  tff(c_261, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_68, c_253])).
% 3.15/1.46  tff(c_64, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')!=k1_tarski(k1_funct_1('#skF_6', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.15/1.46  tff(c_270, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_4'))!=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_261, c_64])).
% 3.15/1.46  tff(c_365, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_356, c_270])).
% 3.15/1.46  tff(c_382, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_121, c_72, c_296, c_365])).
% 3.15/1.46  tff(c_383, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_129])).
% 3.15/1.46  tff(c_384, plain, (k1_relat_1('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_129])).
% 3.15/1.46  tff(c_399, plain, (k1_relat_1('#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_383, c_384])).
% 3.15/1.46  tff(c_28, plain, (![B_18, A_17]: (k1_tarski(k1_funct_1(B_18, A_17))=k2_relat_1(B_18) | k1_tarski(A_17)!=k1_relat_1(B_18) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.15/1.46  tff(c_16, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.15/1.46  tff(c_391, plain, (![A_10]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_383, c_16])).
% 3.15/1.46  tff(c_539, plain, (![A_169, B_170, C_171]: (k2_relset_1(A_169, B_170, C_171)=k2_relat_1(C_171) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.15/1.46  tff(c_544, plain, (![A_169, B_170]: (k2_relset_1(A_169, B_170, '#skF_6')=k2_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_391, c_539])).
% 3.15/1.46  tff(c_545, plain, (k1_tarski(k1_funct_1('#skF_6', '#skF_4'))!=k2_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_544, c_64])).
% 3.15/1.46  tff(c_573, plain, (k1_tarski('#skF_4')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_28, c_545])).
% 3.15/1.46  tff(c_576, plain, (k1_tarski('#skF_4')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_121, c_72, c_399, c_573])).
% 3.15/1.46  tff(c_66, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.15/1.46  tff(c_393, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_383, c_66])).
% 3.15/1.46  tff(c_70, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.15/1.46  tff(c_62, plain, (![B_58, A_57, C_59]: (k1_xboole_0=B_58 | k1_relset_1(A_57, B_58, C_59)=A_57 | ~v1_funct_2(C_59, A_57, B_58) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.15/1.46  tff(c_631, plain, (![B_188, A_189, C_190]: (B_188='#skF_6' | k1_relset_1(A_189, B_188, C_190)=A_189 | ~v1_funct_2(C_190, A_189, B_188) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(A_189, B_188))))), inference(demodulation, [status(thm), theory('equality')], [c_383, c_62])).
% 3.15/1.46  tff(c_637, plain, (![B_191, A_192]: (B_191='#skF_6' | k1_relset_1(A_192, B_191, '#skF_6')=A_192 | ~v1_funct_2('#skF_6', A_192, B_191))), inference(resolution, [status(thm)], [c_391, c_631])).
% 3.15/1.46  tff(c_646, plain, ('#skF_5'='#skF_6' | k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(resolution, [status(thm)], [c_70, c_637])).
% 3.15/1.46  tff(c_652, plain, (k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_393, c_646])).
% 3.15/1.46  tff(c_46, plain, (![A_43]: (r2_hidden('#skF_3'(A_43), A_43) | k1_xboole_0=A_43)), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.15/1.46  tff(c_390, plain, (![A_43]: (r2_hidden('#skF_3'(A_43), A_43) | A_43='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_383, c_46])).
% 3.15/1.46  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.15/1.46  tff(c_392, plain, (![A_1]: (r1_tarski('#skF_6', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_383, c_2])).
% 3.15/1.46  tff(c_791, plain, (![D_216, A_217, B_218, C_219]: (r2_hidden(k4_tarski(D_216, '#skF_2'(A_217, B_218, C_219, D_216)), C_219) | ~r2_hidden(D_216, B_218) | k1_relset_1(B_218, A_217, C_219)!=B_218 | ~m1_subset_1(C_219, k1_zfmisc_1(k2_zfmisc_1(B_218, A_217))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.15/1.46  tff(c_30, plain, (![B_20, A_19]: (~r1_tarski(B_20, A_19) | ~r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.15/1.46  tff(c_818, plain, (![C_228, D_229, A_230, B_231]: (~r1_tarski(C_228, k4_tarski(D_229, '#skF_2'(A_230, B_231, C_228, D_229))) | ~r2_hidden(D_229, B_231) | k1_relset_1(B_231, A_230, C_228)!=B_231 | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1(B_231, A_230))))), inference(resolution, [status(thm)], [c_791, c_30])).
% 3.15/1.46  tff(c_826, plain, (![D_229, B_231, A_230]: (~r2_hidden(D_229, B_231) | k1_relset_1(B_231, A_230, '#skF_6')!=B_231 | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(B_231, A_230))))), inference(resolution, [status(thm)], [c_392, c_818])).
% 3.15/1.46  tff(c_831, plain, (![D_232, B_233, A_234]: (~r2_hidden(D_232, B_233) | k1_relset_1(B_233, A_234, '#skF_6')!=B_233)), inference(demodulation, [status(thm), theory('equality')], [c_391, c_826])).
% 3.15/1.46  tff(c_841, plain, (![A_235, A_236]: (k1_relset_1(A_235, A_236, '#skF_6')!=A_235 | A_235='#skF_6')), inference(resolution, [status(thm)], [c_390, c_831])).
% 3.15/1.46  tff(c_847, plain, (k1_tarski('#skF_4')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_652, c_841])).
% 3.15/1.46  tff(c_853, plain, $false, inference(negUnitSimplification, [status(thm)], [c_576, c_847])).
% 3.15/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.46  
% 3.15/1.46  Inference rules
% 3.15/1.46  ----------------------
% 3.15/1.46  #Ref     : 0
% 3.15/1.46  #Sup     : 153
% 3.15/1.46  #Fact    : 0
% 3.15/1.46  #Define  : 0
% 3.15/1.46  #Split   : 2
% 3.15/1.46  #Chain   : 0
% 3.15/1.46  #Close   : 0
% 3.15/1.46  
% 3.15/1.46  Ordering : KBO
% 3.15/1.46  
% 3.15/1.46  Simplification rules
% 3.15/1.46  ----------------------
% 3.15/1.46  #Subsume      : 2
% 3.15/1.46  #Demod        : 100
% 3.15/1.46  #Tautology    : 81
% 3.15/1.46  #SimpNegUnit  : 3
% 3.15/1.46  #BackRed      : 17
% 3.15/1.46  
% 3.15/1.46  #Partial instantiations: 0
% 3.15/1.46  #Strategies tried      : 1
% 3.15/1.46  
% 3.15/1.46  Timing (in seconds)
% 3.15/1.46  ----------------------
% 3.29/1.46  Preprocessing        : 0.35
% 3.29/1.46  Parsing              : 0.19
% 3.29/1.46  CNF conversion       : 0.02
% 3.29/1.46  Main loop            : 0.35
% 3.29/1.46  Inferencing          : 0.13
% 3.29/1.46  Reduction            : 0.11
% 3.29/1.46  Demodulation         : 0.07
% 3.29/1.46  BG Simplification    : 0.02
% 3.29/1.46  Subsumption          : 0.06
% 3.29/1.46  Abstraction          : 0.02
% 3.29/1.46  MUC search           : 0.00
% 3.29/1.46  Cooper               : 0.00
% 3.29/1.46  Total                : 0.74
% 3.29/1.46  Index Insertion      : 0.00
% 3.29/1.46  Index Deletion       : 0.00
% 3.29/1.46  Index Matching       : 0.00
% 3.29/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
