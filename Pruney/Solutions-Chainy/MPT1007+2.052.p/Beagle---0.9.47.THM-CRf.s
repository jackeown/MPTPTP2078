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
% DateTime   : Thu Dec  3 10:14:18 EST 2020

% Result     : Theorem 6.10s
% Output     : CNFRefutation 6.10s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 184 expanded)
%              Number of leaves         :   49 (  83 expanded)
%              Depth                    :   13
%              Number of atoms          :  161 ( 391 expanded)
%              Number of equality atoms :   44 ( 100 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_8 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff(f_45,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_36,axiom,(
    ! [A,B] : ~ v1_xboole_0(k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_xboole_0)).

tff(f_150,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] : ~ r2_hidden(k4_tarski(D,E),C) )
      <=> k1_relset_1(B,A,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),D))
    <=> ( A = C
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t128_zfmisc_1)).

tff(f_54,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_138,axiom,(
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

tff(c_18,plain,(
    ! [A_14] : m1_subset_1('#skF_1'(A_14),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_77,plain,(
    ! [A_65] : k2_tarski(A_65,A_65) = k1_tarski(A_65) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_8,B_9] : ~ v1_xboole_0(k2_tarski(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_82,plain,(
    ! [A_65] : ~ v1_xboole_0(k1_tarski(A_65)) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_10])).

tff(c_66,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_6'),'#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_534,plain,(
    ! [A_168,B_169,C_170] :
      ( r2_hidden('#skF_4'(A_168,B_169,C_170),B_169)
      | k1_relset_1(B_169,A_168,C_170) = B_169
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(B_169,A_168))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_547,plain,
    ( r2_hidden('#skF_4'('#skF_7',k1_tarski('#skF_6'),'#skF_8'),k1_tarski('#skF_6'))
    | k1_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_534])).

tff(c_626,plain,(
    k1_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_547])).

tff(c_24,plain,(
    ! [A_21,B_22] :
      ( r2_hidden(A_21,B_22)
      | v1_xboole_0(B_22)
      | ~ m1_subset_1(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_100,plain,(
    ! [C_72,A_73,B_74] :
      ( v1_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_112,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_66,c_100])).

tff(c_226,plain,(
    ! [A_119] :
      ( k1_xboole_0 = A_119
      | r2_hidden(k4_tarski('#skF_2'(A_119),'#skF_3'(A_119)),A_119)
      | ~ v1_relat_1(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_20,plain,(
    ! [C_19,A_16,B_17] :
      ( r2_hidden(C_19,A_16)
      | ~ r2_hidden(C_19,B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_930,plain,(
    ! [A_211,A_212] :
      ( r2_hidden(k4_tarski('#skF_2'(A_211),'#skF_3'(A_211)),A_212)
      | ~ m1_subset_1(A_211,k1_zfmisc_1(A_212))
      | k1_xboole_0 = A_211
      | ~ v1_relat_1(A_211) ) ),
    inference(resolution,[status(thm)],[c_226,c_20])).

tff(c_16,plain,(
    ! [C_12,A_10,B_11,D_13] :
      ( C_12 = A_10
      | ~ r2_hidden(k4_tarski(A_10,B_11),k2_zfmisc_1(k1_tarski(C_12),D_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_968,plain,(
    ! [C_213,A_214,D_215] :
      ( C_213 = '#skF_2'(A_214)
      | ~ m1_subset_1(A_214,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_213),D_215)))
      | k1_xboole_0 = A_214
      | ~ v1_relat_1(A_214) ) ),
    inference(resolution,[status(thm)],[c_930,c_16])).

tff(c_979,plain,
    ( '#skF_2'('#skF_8') = '#skF_6'
    | k1_xboole_0 = '#skF_8'
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_66,c_968])).

tff(c_992,plain,
    ( '#skF_2'('#skF_8') = '#skF_6'
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_979])).

tff(c_1000,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_992])).

tff(c_22,plain,(
    ! [A_20] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1030,plain,(
    ! [A_20] : m1_subset_1('#skF_8',k1_zfmisc_1(A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1000,c_22])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1031,plain,(
    ! [A_1] : r1_tarski('#skF_8',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1000,c_2])).

tff(c_885,plain,(
    ! [D_207,A_208,B_209,C_210] :
      ( r2_hidden(k4_tarski(D_207,'#skF_5'(A_208,B_209,C_210,D_207)),C_210)
      | ~ r2_hidden(D_207,B_209)
      | k1_relset_1(B_209,A_208,C_210) != B_209
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(B_209,A_208))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_36,plain,(
    ! [B_37,A_36] :
      ( ~ r1_tarski(B_37,A_36)
      | ~ r2_hidden(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3625,plain,(
    ! [C_459,D_460,A_461,B_462] :
      ( ~ r1_tarski(C_459,k4_tarski(D_460,'#skF_5'(A_461,B_462,C_459,D_460)))
      | ~ r2_hidden(D_460,B_462)
      | k1_relset_1(B_462,A_461,C_459) != B_462
      | ~ m1_subset_1(C_459,k1_zfmisc_1(k2_zfmisc_1(B_462,A_461))) ) ),
    inference(resolution,[status(thm)],[c_885,c_36])).

tff(c_3629,plain,(
    ! [D_460,B_462,A_461] :
      ( ~ r2_hidden(D_460,B_462)
      | k1_relset_1(B_462,A_461,'#skF_8') != B_462
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1(B_462,A_461))) ) ),
    inference(resolution,[status(thm)],[c_1031,c_3625])).

tff(c_3838,plain,(
    ! [D_473,B_474,A_475] :
      ( ~ r2_hidden(D_473,B_474)
      | k1_relset_1(B_474,A_475,'#skF_8') != B_474 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1030,c_3629])).

tff(c_4227,plain,(
    ! [B_488,A_489,A_490] :
      ( k1_relset_1(B_488,A_489,'#skF_8') != B_488
      | v1_xboole_0(B_488)
      | ~ m1_subset_1(A_490,B_488) ) ),
    inference(resolution,[status(thm)],[c_24,c_3838])).

tff(c_4239,plain,(
    ! [A_490] :
      ( v1_xboole_0(k1_tarski('#skF_6'))
      | ~ m1_subset_1(A_490,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_626,c_4227])).

tff(c_4251,plain,(
    ! [A_491] : ~ m1_subset_1(A_491,k1_tarski('#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_4239])).

tff(c_4283,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_18,c_4251])).

tff(c_4285,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_992])).

tff(c_148,plain,(
    ! [C_85,B_86,A_87] :
      ( v5_relat_1(C_85,B_86)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_87,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_160,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_148])).

tff(c_70,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_418,plain,(
    ! [B_151,C_152,A_153] :
      ( r2_hidden(k1_funct_1(B_151,C_152),A_153)
      | ~ r2_hidden(C_152,k1_relat_1(B_151))
      | ~ v1_funct_1(B_151)
      | ~ v5_relat_1(B_151,A_153)
      | ~ v1_relat_1(B_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_62,plain,(
    ~ r2_hidden(k1_funct_1('#skF_8','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_433,plain,
    ( ~ r2_hidden('#skF_6',k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v5_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_418,c_62])).

tff(c_440,plain,(
    ~ r2_hidden('#skF_6',k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_160,c_70,c_433])).

tff(c_4284,plain,(
    '#skF_2'('#skF_8') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_992])).

tff(c_32,plain,(
    ! [A_29] :
      ( k1_xboole_0 = A_29
      | r2_hidden(k4_tarski('#skF_2'(A_29),'#skF_3'(A_29)),A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_269,plain,(
    ! [A_122,C_123,B_124] :
      ( r2_hidden(A_122,k1_relat_1(C_123))
      | ~ r2_hidden(k4_tarski(A_122,B_124),C_123)
      | ~ v1_relat_1(C_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_277,plain,(
    ! [A_29] :
      ( r2_hidden('#skF_2'(A_29),k1_relat_1(A_29))
      | k1_xboole_0 = A_29
      | ~ v1_relat_1(A_29) ) ),
    inference(resolution,[status(thm)],[c_32,c_269])).

tff(c_4298,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_4284,c_277])).

tff(c_4314,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_8'))
    | k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_4298])).

tff(c_4316,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4285,c_440,c_4314])).

tff(c_4318,plain,(
    k1_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_8') != k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_547])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_68,plain,(
    v1_funct_2('#skF_8',k1_tarski('#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_4332,plain,(
    ! [B_494,A_495,C_496] :
      ( k1_xboole_0 = B_494
      | k1_relset_1(A_495,B_494,C_496) = A_495
      | ~ v1_funct_2(C_496,A_495,B_494)
      | ~ m1_subset_1(C_496,k1_zfmisc_1(k2_zfmisc_1(A_495,B_494))) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_4343,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_8') = k1_tarski('#skF_6')
    | ~ v1_funct_2('#skF_8',k1_tarski('#skF_6'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_4332])).

tff(c_4356,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1(k1_tarski('#skF_6'),'#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_4343])).

tff(c_4358,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4318,c_64,c_4356])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:28:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.10/2.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.10/2.19  
% 6.10/2.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.10/2.19  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_8 > #skF_5 > #skF_3
% 6.10/2.19  
% 6.10/2.19  %Foreground sorts:
% 6.10/2.19  
% 6.10/2.19  
% 6.10/2.19  %Background operators:
% 6.10/2.19  
% 6.10/2.19  
% 6.10/2.19  %Foreground operators:
% 6.10/2.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.10/2.19  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.10/2.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.10/2.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.10/2.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.10/2.19  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.10/2.19  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.10/2.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.10/2.19  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.10/2.19  tff('#skF_7', type, '#skF_7': $i).
% 6.10/2.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.10/2.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.10/2.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.10/2.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.10/2.19  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.10/2.19  tff('#skF_6', type, '#skF_6': $i).
% 6.10/2.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.10/2.19  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.10/2.19  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.10/2.19  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.10/2.19  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.10/2.19  tff('#skF_8', type, '#skF_8': $i).
% 6.10/2.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.10/2.19  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 6.10/2.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.10/2.19  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.10/2.19  tff('#skF_3', type, '#skF_3': $i > $i).
% 6.10/2.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.10/2.19  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.10/2.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.10/2.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.10/2.19  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.10/2.19  
% 6.10/2.21  tff(f_45, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 6.10/2.21  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.10/2.21  tff(f_36, axiom, (![A, B]: ~v1_xboole_0(k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_xboole_0)).
% 6.10/2.21  tff(f_150, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 6.10/2.21  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~r2_hidden(k4_tarski(D, E), C)))) <=> (k1_relset_1(B, A, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relset_1)).
% 6.10/2.21  tff(f_60, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 6.10/2.21  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.10/2.21  tff(f_82, axiom, (![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t56_relat_1)).
% 6.10/2.21  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 6.10/2.21  tff(f_42, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), D)) <=> ((A = C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t128_zfmisc_1)).
% 6.10/2.21  tff(f_54, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 6.10/2.21  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.10/2.21  tff(f_98, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.10/2.21  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.10/2.21  tff(f_93, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 6.10/2.21  tff(f_74, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_relat_1)).
% 6.10/2.21  tff(f_138, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.10/2.21  tff(c_18, plain, (![A_14]: (m1_subset_1('#skF_1'(A_14), A_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.10/2.21  tff(c_77, plain, (![A_65]: (k2_tarski(A_65, A_65)=k1_tarski(A_65))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.10/2.21  tff(c_10, plain, (![A_8, B_9]: (~v1_xboole_0(k2_tarski(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.10/2.21  tff(c_82, plain, (![A_65]: (~v1_xboole_0(k1_tarski(A_65)))), inference(superposition, [status(thm), theory('equality')], [c_77, c_10])).
% 6.10/2.21  tff(c_66, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_6'), '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 6.10/2.21  tff(c_534, plain, (![A_168, B_169, C_170]: (r2_hidden('#skF_4'(A_168, B_169, C_170), B_169) | k1_relset_1(B_169, A_168, C_170)=B_169 | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(B_169, A_168))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.10/2.21  tff(c_547, plain, (r2_hidden('#skF_4'('#skF_7', k1_tarski('#skF_6'), '#skF_8'), k1_tarski('#skF_6')) | k1_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(resolution, [status(thm)], [c_66, c_534])).
% 6.10/2.21  tff(c_626, plain, (k1_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(splitLeft, [status(thm)], [c_547])).
% 6.10/2.21  tff(c_24, plain, (![A_21, B_22]: (r2_hidden(A_21, B_22) | v1_xboole_0(B_22) | ~m1_subset_1(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.10/2.21  tff(c_100, plain, (![C_72, A_73, B_74]: (v1_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.10/2.21  tff(c_112, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_66, c_100])).
% 6.10/2.21  tff(c_226, plain, (![A_119]: (k1_xboole_0=A_119 | r2_hidden(k4_tarski('#skF_2'(A_119), '#skF_3'(A_119)), A_119) | ~v1_relat_1(A_119))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.10/2.21  tff(c_20, plain, (![C_19, A_16, B_17]: (r2_hidden(C_19, A_16) | ~r2_hidden(C_19, B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.10/2.21  tff(c_930, plain, (![A_211, A_212]: (r2_hidden(k4_tarski('#skF_2'(A_211), '#skF_3'(A_211)), A_212) | ~m1_subset_1(A_211, k1_zfmisc_1(A_212)) | k1_xboole_0=A_211 | ~v1_relat_1(A_211))), inference(resolution, [status(thm)], [c_226, c_20])).
% 6.10/2.21  tff(c_16, plain, (![C_12, A_10, B_11, D_13]: (C_12=A_10 | ~r2_hidden(k4_tarski(A_10, B_11), k2_zfmisc_1(k1_tarski(C_12), D_13)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.10/2.21  tff(c_968, plain, (![C_213, A_214, D_215]: (C_213='#skF_2'(A_214) | ~m1_subset_1(A_214, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(C_213), D_215))) | k1_xboole_0=A_214 | ~v1_relat_1(A_214))), inference(resolution, [status(thm)], [c_930, c_16])).
% 6.10/2.21  tff(c_979, plain, ('#skF_2'('#skF_8')='#skF_6' | k1_xboole_0='#skF_8' | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_66, c_968])).
% 6.10/2.21  tff(c_992, plain, ('#skF_2'('#skF_8')='#skF_6' | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_979])).
% 6.10/2.21  tff(c_1000, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_992])).
% 6.10/2.21  tff(c_22, plain, (![A_20]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.10/2.21  tff(c_1030, plain, (![A_20]: (m1_subset_1('#skF_8', k1_zfmisc_1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_1000, c_22])).
% 6.10/2.21  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.10/2.21  tff(c_1031, plain, (![A_1]: (r1_tarski('#skF_8', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_1000, c_2])).
% 6.10/2.21  tff(c_885, plain, (![D_207, A_208, B_209, C_210]: (r2_hidden(k4_tarski(D_207, '#skF_5'(A_208, B_209, C_210, D_207)), C_210) | ~r2_hidden(D_207, B_209) | k1_relset_1(B_209, A_208, C_210)!=B_209 | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(B_209, A_208))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.10/2.21  tff(c_36, plain, (![B_37, A_36]: (~r1_tarski(B_37, A_36) | ~r2_hidden(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.10/2.21  tff(c_3625, plain, (![C_459, D_460, A_461, B_462]: (~r1_tarski(C_459, k4_tarski(D_460, '#skF_5'(A_461, B_462, C_459, D_460))) | ~r2_hidden(D_460, B_462) | k1_relset_1(B_462, A_461, C_459)!=B_462 | ~m1_subset_1(C_459, k1_zfmisc_1(k2_zfmisc_1(B_462, A_461))))), inference(resolution, [status(thm)], [c_885, c_36])).
% 6.10/2.21  tff(c_3629, plain, (![D_460, B_462, A_461]: (~r2_hidden(D_460, B_462) | k1_relset_1(B_462, A_461, '#skF_8')!=B_462 | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1(B_462, A_461))))), inference(resolution, [status(thm)], [c_1031, c_3625])).
% 6.10/2.21  tff(c_3838, plain, (![D_473, B_474, A_475]: (~r2_hidden(D_473, B_474) | k1_relset_1(B_474, A_475, '#skF_8')!=B_474)), inference(demodulation, [status(thm), theory('equality')], [c_1030, c_3629])).
% 6.10/2.21  tff(c_4227, plain, (![B_488, A_489, A_490]: (k1_relset_1(B_488, A_489, '#skF_8')!=B_488 | v1_xboole_0(B_488) | ~m1_subset_1(A_490, B_488))), inference(resolution, [status(thm)], [c_24, c_3838])).
% 6.10/2.21  tff(c_4239, plain, (![A_490]: (v1_xboole_0(k1_tarski('#skF_6')) | ~m1_subset_1(A_490, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_626, c_4227])).
% 6.10/2.21  tff(c_4251, plain, (![A_491]: (~m1_subset_1(A_491, k1_tarski('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_82, c_4239])).
% 6.10/2.21  tff(c_4283, plain, $false, inference(resolution, [status(thm)], [c_18, c_4251])).
% 6.10/2.21  tff(c_4285, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_992])).
% 6.10/2.21  tff(c_148, plain, (![C_85, B_86, A_87]: (v5_relat_1(C_85, B_86) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_87, B_86))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 6.10/2.21  tff(c_160, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_66, c_148])).
% 6.10/2.21  tff(c_70, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_150])).
% 6.10/2.21  tff(c_418, plain, (![B_151, C_152, A_153]: (r2_hidden(k1_funct_1(B_151, C_152), A_153) | ~r2_hidden(C_152, k1_relat_1(B_151)) | ~v1_funct_1(B_151) | ~v5_relat_1(B_151, A_153) | ~v1_relat_1(B_151))), inference(cnfTransformation, [status(thm)], [f_93])).
% 6.10/2.21  tff(c_62, plain, (~r2_hidden(k1_funct_1('#skF_8', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_150])).
% 6.10/2.21  tff(c_433, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v5_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_418, c_62])).
% 6.10/2.21  tff(c_440, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_160, c_70, c_433])).
% 6.10/2.21  tff(c_4284, plain, ('#skF_2'('#skF_8')='#skF_6'), inference(splitRight, [status(thm)], [c_992])).
% 6.10/2.21  tff(c_32, plain, (![A_29]: (k1_xboole_0=A_29 | r2_hidden(k4_tarski('#skF_2'(A_29), '#skF_3'(A_29)), A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.10/2.21  tff(c_269, plain, (![A_122, C_123, B_124]: (r2_hidden(A_122, k1_relat_1(C_123)) | ~r2_hidden(k4_tarski(A_122, B_124), C_123) | ~v1_relat_1(C_123))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.10/2.21  tff(c_277, plain, (![A_29]: (r2_hidden('#skF_2'(A_29), k1_relat_1(A_29)) | k1_xboole_0=A_29 | ~v1_relat_1(A_29))), inference(resolution, [status(thm)], [c_32, c_269])).
% 6.10/2.21  tff(c_4298, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_8')) | k1_xboole_0='#skF_8' | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_4284, c_277])).
% 6.10/2.21  tff(c_4314, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_8')) | k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_112, c_4298])).
% 6.10/2.21  tff(c_4316, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4285, c_440, c_4314])).
% 6.10/2.21  tff(c_4318, plain, (k1_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_8')!=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_547])).
% 6.10/2.21  tff(c_64, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_150])).
% 6.10/2.21  tff(c_68, plain, (v1_funct_2('#skF_8', k1_tarski('#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_150])).
% 6.10/2.21  tff(c_4332, plain, (![B_494, A_495, C_496]: (k1_xboole_0=B_494 | k1_relset_1(A_495, B_494, C_496)=A_495 | ~v1_funct_2(C_496, A_495, B_494) | ~m1_subset_1(C_496, k1_zfmisc_1(k2_zfmisc_1(A_495, B_494))))), inference(cnfTransformation, [status(thm)], [f_138])).
% 6.10/2.21  tff(c_4343, plain, (k1_xboole_0='#skF_7' | k1_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_8')=k1_tarski('#skF_6') | ~v1_funct_2('#skF_8', k1_tarski('#skF_6'), '#skF_7')), inference(resolution, [status(thm)], [c_66, c_4332])).
% 6.10/2.21  tff(c_4356, plain, (k1_xboole_0='#skF_7' | k1_relset_1(k1_tarski('#skF_6'), '#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_4343])).
% 6.10/2.21  tff(c_4358, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4318, c_64, c_4356])).
% 6.10/2.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.10/2.21  
% 6.10/2.21  Inference rules
% 6.10/2.21  ----------------------
% 6.10/2.21  #Ref     : 0
% 6.10/2.21  #Sup     : 943
% 6.10/2.21  #Fact    : 0
% 6.10/2.21  #Define  : 0
% 6.10/2.21  #Split   : 15
% 6.10/2.21  #Chain   : 0
% 6.10/2.21  #Close   : 0
% 6.10/2.21  
% 6.10/2.21  Ordering : KBO
% 6.10/2.21  
% 6.10/2.21  Simplification rules
% 6.10/2.21  ----------------------
% 6.10/2.21  #Subsume      : 118
% 6.10/2.21  #Demod        : 299
% 6.10/2.21  #Tautology    : 178
% 6.10/2.21  #SimpNegUnit  : 12
% 6.10/2.21  #BackRed      : 33
% 6.10/2.21  
% 6.10/2.21  #Partial instantiations: 0
% 6.10/2.21  #Strategies tried      : 1
% 6.10/2.21  
% 6.10/2.21  Timing (in seconds)
% 6.10/2.21  ----------------------
% 6.10/2.21  Preprocessing        : 0.34
% 6.10/2.21  Parsing              : 0.18
% 6.10/2.21  CNF conversion       : 0.02
% 6.10/2.21  Main loop            : 1.11
% 6.10/2.21  Inferencing          : 0.35
% 6.10/2.21  Reduction            : 0.36
% 6.10/2.21  Demodulation         : 0.25
% 6.10/2.21  BG Simplification    : 0.05
% 6.10/2.21  Subsumption          : 0.24
% 6.10/2.21  Abstraction          : 0.06
% 6.10/2.21  MUC search           : 0.00
% 6.10/2.21  Cooper               : 0.00
% 6.10/2.21  Total                : 1.49
% 6.10/2.21  Index Insertion      : 0.00
% 6.10/2.21  Index Deletion       : 0.00
% 6.10/2.21  Index Matching       : 0.00
% 6.10/2.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
