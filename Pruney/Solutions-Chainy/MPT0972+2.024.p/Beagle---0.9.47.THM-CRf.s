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
% DateTime   : Thu Dec  3 10:11:38 EST 2020

% Result     : Theorem 6.71s
% Output     : CNFRefutation 7.20s
% Verified   : 
% Statistics : Number of formulae       :  243 (3728 expanded)
%              Number of leaves         :   38 (1212 expanded)
%              Depth                    :   15
%              Number of atoms          :  435 (9819 expanded)
%              Number of equality atoms :  162 (2135 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_136,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( r2_hidden(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_115,axiom,(
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

tff(f_83,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_47,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(c_66,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_60,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1391,plain,(
    ! [A_232,B_233,C_234,D_235] :
      ( r2_relset_1(A_232,B_233,C_234,C_234)
      | ~ m1_subset_1(D_235,k1_zfmisc_1(k2_zfmisc_1(A_232,B_233)))
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1(A_232,B_233))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1408,plain,(
    ! [C_236] :
      ( r2_relset_1('#skF_4','#skF_5',C_236,C_236)
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ) ),
    inference(resolution,[status(thm)],[c_60,c_1391])).

tff(c_1418,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_1408])).

tff(c_137,plain,(
    ! [C_60,A_61,B_62] :
      ( v1_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_153,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_137])).

tff(c_64,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_62,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1118,plain,(
    ! [A_191,B_192,C_193] :
      ( k1_relset_1(A_191,B_192,C_193) = k1_relat_1(C_193)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(A_191,B_192))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1136,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_1118])).

tff(c_1196,plain,(
    ! [B_205,A_206,C_207] :
      ( k1_xboole_0 = B_205
      | k1_relset_1(A_206,B_205,C_207) = A_206
      | ~ v1_funct_2(C_207,A_206,B_205)
      | ~ m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(A_206,B_205))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1203,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_1196])).

tff(c_1216,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1136,c_1203])).

tff(c_1221,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1216])).

tff(c_154,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_137])).

tff(c_70,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_68,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1137,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_1118])).

tff(c_1206,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_1196])).

tff(c_1219,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1137,c_1206])).

tff(c_1227,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1219])).

tff(c_1440,plain,(
    ! [A_238,B_239] :
      ( r2_hidden('#skF_3'(A_238,B_239),k1_relat_1(A_238))
      | B_239 = A_238
      | k1_relat_1(B_239) != k1_relat_1(A_238)
      | ~ v1_funct_1(B_239)
      | ~ v1_relat_1(B_239)
      | ~ v1_funct_1(A_238)
      | ~ v1_relat_1(A_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1448,plain,(
    ! [B_239] :
      ( r2_hidden('#skF_3'('#skF_6',B_239),'#skF_4')
      | B_239 = '#skF_6'
      | k1_relat_1(B_239) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_239)
      | ~ v1_relat_1(B_239)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1227,c_1440])).

tff(c_1866,plain,(
    ! [B_290] :
      ( r2_hidden('#skF_3'('#skF_6',B_290),'#skF_4')
      | B_290 = '#skF_6'
      | k1_relat_1(B_290) != '#skF_4'
      | ~ v1_funct_1(B_290)
      | ~ v1_relat_1(B_290) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_70,c_1227,c_1448])).

tff(c_58,plain,(
    ! [E_42] :
      ( k1_funct_1('#skF_7',E_42) = k1_funct_1('#skF_6',E_42)
      | ~ r2_hidden(E_42,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_2663,plain,(
    ! [B_343] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_6',B_343)) = k1_funct_1('#skF_6','#skF_3'('#skF_6',B_343))
      | B_343 = '#skF_6'
      | k1_relat_1(B_343) != '#skF_4'
      | ~ v1_funct_1(B_343)
      | ~ v1_relat_1(B_343) ) ),
    inference(resolution,[status(thm)],[c_1866,c_58])).

tff(c_34,plain,(
    ! [B_23,A_19] :
      ( k1_funct_1(B_23,'#skF_3'(A_19,B_23)) != k1_funct_1(A_19,'#skF_3'(A_19,B_23))
      | B_23 = A_19
      | k1_relat_1(B_23) != k1_relat_1(A_19)
      | ~ v1_funct_1(B_23)
      | ~ v1_relat_1(B_23)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_2670,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_7') != '#skF_4'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2663,c_34])).

tff(c_2677,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_64,c_1221,c_154,c_70,c_1221,c_1227,c_2670])).

tff(c_56,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_2705,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2677,c_56])).

tff(c_2716,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1418,c_2705])).

tff(c_2717,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1219])).

tff(c_20,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2736,plain,(
    ! [A_12] : r1_tarski('#skF_5',A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2717,c_20])).

tff(c_26,plain,(
    ! [A_15] : k2_zfmisc_1(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2735,plain,(
    ! [A_15] : k2_zfmisc_1(A_15,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2717,c_2717,c_26])).

tff(c_117,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(A_55,B_56)
      | ~ m1_subset_1(A_55,k1_zfmisc_1(B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_129,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_66,c_117])).

tff(c_852,plain,(
    ! [B_162,A_163] :
      ( B_162 = A_163
      | ~ r1_tarski(B_162,A_163)
      | ~ r1_tarski(A_163,B_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_864,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6'
    | ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_129,c_852])).

tff(c_1035,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_864])).

tff(c_2800,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2735,c_1035])).

tff(c_2809,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2736,c_2800])).

tff(c_2810,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1216])).

tff(c_2829,plain,(
    ! [A_12] : r1_tarski('#skF_5',A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2810,c_20])).

tff(c_2828,plain,(
    ! [A_15] : k2_zfmisc_1(A_15,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2810,c_2810,c_26])).

tff(c_2890,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2828,c_1035])).

tff(c_2899,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2829,c_2890])).

tff(c_2900,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_864])).

tff(c_128,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_60,c_117])).

tff(c_155,plain,(
    ! [A_63,B_64] :
      ( r2_hidden('#skF_2'(A_63,B_64),A_63)
      | r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_170,plain,(
    ! [A_63,B_64] :
      ( ~ v1_xboole_0(A_63)
      | r1_tarski(A_63,B_64) ) ),
    inference(resolution,[status(thm)],[c_155,c_2])).

tff(c_931,plain,(
    ! [B_170,A_171] :
      ( B_170 = A_171
      | ~ r1_tarski(B_170,A_171)
      | ~ v1_xboole_0(A_171) ) ),
    inference(resolution,[status(thm)],[c_170,c_852])).

tff(c_949,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = '#skF_7'
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_128,c_931])).

tff(c_964,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_949])).

tff(c_2903,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2900,c_964])).

tff(c_18,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2906,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2900,c_60])).

tff(c_2994,plain,(
    ! [A_354,B_355,C_356] :
      ( k1_relset_1(A_354,B_355,C_356) = k1_relat_1(C_356)
      | ~ m1_subset_1(C_356,k1_zfmisc_1(k2_zfmisc_1(A_354,B_355))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3033,plain,(
    ! [C_360] :
      ( k1_relset_1('#skF_4','#skF_5',C_360) = k1_relat_1(C_360)
      | ~ m1_subset_1(C_360,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2900,c_2994])).

tff(c_3045,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_2906,c_3033])).

tff(c_3121,plain,(
    ! [B_370,A_371,C_372] :
      ( k1_xboole_0 = B_370
      | k1_relset_1(A_371,B_370,C_372) = A_371
      | ~ v1_funct_2(C_372,A_371,B_370)
      | ~ m1_subset_1(C_372,k1_zfmisc_1(k2_zfmisc_1(A_371,B_370))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_3124,plain,(
    ! [C_372] :
      ( k1_xboole_0 = '#skF_5'
      | k1_relset_1('#skF_4','#skF_5',C_372) = '#skF_4'
      | ~ v1_funct_2(C_372,'#skF_4','#skF_5')
      | ~ m1_subset_1(C_372,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2900,c_3121])).

tff(c_3249,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_3124])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( k1_xboole_0 = B_16
      | k1_xboole_0 = A_15
      | k2_zfmisc_1(A_15,B_16) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2912,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 != '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_2900,c_24])).

tff(c_2993,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2912])).

tff(c_3258,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3249,c_2993])).

tff(c_3341,plain,(
    ! [A_396] : k2_zfmisc_1(A_396,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3249,c_3249,c_26])).

tff(c_3354,plain,(
    '#skF_5' = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_3341,c_2900])).

tff(c_3368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3258,c_3354])).

tff(c_3554,plain,(
    ! [C_421] :
      ( k1_relset_1('#skF_4','#skF_5',C_421) = '#skF_4'
      | ~ v1_funct_2(C_421,'#skF_4','#skF_5')
      | ~ m1_subset_1(C_421,k1_zfmisc_1('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_3124])).

tff(c_3560,plain,
    ( k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_2906,c_3554])).

tff(c_3570,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_3045,c_3560])).

tff(c_2907,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2900,c_66])).

tff(c_3044,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_2907,c_3033])).

tff(c_3557,plain,
    ( k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_2907,c_3554])).

tff(c_3567,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3044,c_3557])).

tff(c_3680,plain,(
    ! [A_436,B_437] :
      ( r2_hidden('#skF_3'(A_436,B_437),k1_relat_1(A_436))
      | B_437 = A_436
      | k1_relat_1(B_437) != k1_relat_1(A_436)
      | ~ v1_funct_1(B_437)
      | ~ v1_relat_1(B_437)
      | ~ v1_funct_1(A_436)
      | ~ v1_relat_1(A_436) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_3691,plain,(
    ! [B_437] :
      ( r2_hidden('#skF_3'('#skF_6',B_437),'#skF_4')
      | B_437 = '#skF_6'
      | k1_relat_1(B_437) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_437)
      | ~ v1_relat_1(B_437)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3567,c_3680])).

tff(c_3840,plain,(
    ! [B_464] :
      ( r2_hidden('#skF_3'('#skF_6',B_464),'#skF_4')
      | B_464 = '#skF_6'
      | k1_relat_1(B_464) != '#skF_4'
      | ~ v1_funct_1(B_464)
      | ~ v1_relat_1(B_464) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_70,c_3567,c_3691])).

tff(c_4023,plain,(
    ! [B_484] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_6',B_484)) = k1_funct_1('#skF_6','#skF_3'('#skF_6',B_484))
      | B_484 = '#skF_6'
      | k1_relat_1(B_484) != '#skF_4'
      | ~ v1_funct_1(B_484)
      | ~ v1_relat_1(B_484) ) ),
    inference(resolution,[status(thm)],[c_3840,c_58])).

tff(c_4030,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_7') != '#skF_4'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_4023,c_34])).

tff(c_4037,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_64,c_3570,c_154,c_70,c_3567,c_3570,c_4030])).

tff(c_865,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = '#skF_7'
    | ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_128,c_852])).

tff(c_1007,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_865])).

tff(c_2902,plain,(
    ~ r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2900,c_1007])).

tff(c_4053,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4037,c_2902])).

tff(c_4069,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_4053])).

tff(c_4071,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2912])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4083,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4071,c_12])).

tff(c_4087,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2903,c_4083])).

tff(c_4088,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_865])).

tff(c_4090,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4088,c_964])).

tff(c_4093,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4088,c_60])).

tff(c_4261,plain,(
    ! [A_497,B_498,C_499] :
      ( k1_relset_1(A_497,B_498,C_499) = k1_relat_1(C_499)
      | ~ m1_subset_1(C_499,k1_zfmisc_1(k2_zfmisc_1(A_497,B_498))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4384,plain,(
    ! [C_518] :
      ( k1_relset_1('#skF_4','#skF_5',C_518) = k1_relat_1(C_518)
      | ~ m1_subset_1(C_518,k1_zfmisc_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4088,c_4261])).

tff(c_4396,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_4093,c_4384])).

tff(c_4483,plain,(
    ! [B_528,A_529,C_530] :
      ( k1_xboole_0 = B_528
      | k1_relset_1(A_529,B_528,C_530) = A_529
      | ~ v1_funct_2(C_530,A_529,B_528)
      | ~ m1_subset_1(C_530,k1_zfmisc_1(k2_zfmisc_1(A_529,B_528))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_4486,plain,(
    ! [C_530] :
      ( k1_xboole_0 = '#skF_5'
      | k1_relset_1('#skF_4','#skF_5',C_530) = '#skF_4'
      | ~ v1_funct_2(C_530,'#skF_4','#skF_5')
      | ~ m1_subset_1(C_530,k1_zfmisc_1('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4088,c_4483])).

tff(c_4533,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_4486])).

tff(c_4099,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 != '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_4088,c_24])).

tff(c_4204,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_4099])).

tff(c_4544,plain,(
    '#skF_7' != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4533,c_4204])).

tff(c_4555,plain,(
    ! [A_15] : k2_zfmisc_1(A_15,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4533,c_4533,c_26])).

tff(c_4653,plain,(
    '#skF_7' = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4555,c_4088])).

tff(c_4655,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4544,c_4653])).

tff(c_4759,plain,(
    ! [C_558] :
      ( k1_relset_1('#skF_4','#skF_5',C_558) = '#skF_4'
      | ~ v1_funct_2(C_558,'#skF_4','#skF_5')
      | ~ m1_subset_1(C_558,k1_zfmisc_1('#skF_7')) ) ),
    inference(splitRight,[status(thm)],[c_4486])).

tff(c_4765,plain,
    ( k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_4093,c_4759])).

tff(c_4775,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4396,c_4765])).

tff(c_4094,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4088,c_66])).

tff(c_4395,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_4094,c_4384])).

tff(c_4762,plain,
    ( k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_4094,c_4759])).

tff(c_4772,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_4395,c_4762])).

tff(c_4962,plain,(
    ! [A_590,B_591] :
      ( r2_hidden('#skF_3'(A_590,B_591),k1_relat_1(A_590))
      | B_591 = A_590
      | k1_relat_1(B_591) != k1_relat_1(A_590)
      | ~ v1_funct_1(B_591)
      | ~ v1_relat_1(B_591)
      | ~ v1_funct_1(A_590)
      | ~ v1_relat_1(A_590) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_4973,plain,(
    ! [B_591] :
      ( r2_hidden('#skF_3'('#skF_6',B_591),'#skF_4')
      | B_591 = '#skF_6'
      | k1_relat_1(B_591) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_591)
      | ~ v1_relat_1(B_591)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4772,c_4962])).

tff(c_5174,plain,(
    ! [B_613] :
      ( r2_hidden('#skF_3'('#skF_6',B_613),'#skF_4')
      | B_613 = '#skF_6'
      | k1_relat_1(B_613) != '#skF_4'
      | ~ v1_funct_1(B_613)
      | ~ v1_relat_1(B_613) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_70,c_4772,c_4973])).

tff(c_5592,plain,(
    ! [B_654] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_6',B_654)) = k1_funct_1('#skF_6','#skF_3'('#skF_6',B_654))
      | B_654 = '#skF_6'
      | k1_relat_1(B_654) != '#skF_4'
      | ~ v1_funct_1(B_654)
      | ~ v1_relat_1(B_654) ) ),
    inference(resolution,[status(thm)],[c_5174,c_58])).

tff(c_5599,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_7') != '#skF_4'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_5592,c_34])).

tff(c_5606,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_64,c_4775,c_154,c_70,c_4772,c_4775,c_5599])).

tff(c_4091,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4088,c_129])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4120,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_4091,c_14])).

tff(c_4175,plain,(
    ~ r1_tarski('#skF_7','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_4120])).

tff(c_5639,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5606,c_4175])).

tff(c_5658,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_5639])).

tff(c_5660,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_4099])).

tff(c_5673,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5660,c_12])).

tff(c_5677,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4090,c_5673])).

tff(c_5678,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_4120])).

tff(c_5690,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5678,c_56])).

tff(c_5681,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5678,c_4094])).

tff(c_5685,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5678,c_4088])).

tff(c_6110,plain,(
    ! [A_720,B_721,C_722,D_723] :
      ( r2_relset_1(A_720,B_721,C_722,C_722)
      | ~ m1_subset_1(D_723,k1_zfmisc_1(k2_zfmisc_1(A_720,B_721)))
      | ~ m1_subset_1(C_722,k1_zfmisc_1(k2_zfmisc_1(A_720,B_721))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6112,plain,(
    ! [C_722,D_723] :
      ( r2_relset_1('#skF_4','#skF_5',C_722,C_722)
      | ~ m1_subset_1(D_723,k1_zfmisc_1('#skF_6'))
      | ~ m1_subset_1(C_722,k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5685,c_6110])).

tff(c_6120,plain,(
    ! [C_722,D_723] :
      ( r2_relset_1('#skF_4','#skF_5',C_722,C_722)
      | ~ m1_subset_1(D_723,k1_zfmisc_1('#skF_6'))
      | ~ m1_subset_1(C_722,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5685,c_6112])).

tff(c_6346,plain,(
    ! [D_723] : ~ m1_subset_1(D_723,k1_zfmisc_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_6120])).

tff(c_6348,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6346,c_5681])).

tff(c_6352,plain,(
    ! [C_744] :
      ( r2_relset_1('#skF_4','#skF_5',C_744,C_744)
      | ~ m1_subset_1(C_744,k1_zfmisc_1('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_6120])).

tff(c_6354,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_5681,c_6352])).

tff(c_6361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5690,c_6354])).

tff(c_6362,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_949])).

tff(c_948,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6'
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_129,c_931])).

tff(c_6407,plain,
    ( '#skF_7' = '#skF_6'
    | ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6362,c_6362,c_948])).

tff(c_6408,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_6407])).

tff(c_6363,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_949])).

tff(c_6409,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6362,c_6363])).

tff(c_6410,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6408,c_6409])).

tff(c_6411,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_6407])).

tff(c_6366,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6362,c_60])).

tff(c_6413,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6411,c_6411,c_6366])).

tff(c_6412,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_6407])).

tff(c_6432,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6411,c_6412])).

tff(c_106,plain,(
    ! [B_50,A_51] :
      ( ~ v1_xboole_0(B_50)
      | B_50 = A_51
      | ~ v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_109,plain,(
    ! [A_51] :
      ( k1_xboole_0 = A_51
      | ~ v1_xboole_0(A_51) ) ),
    inference(resolution,[status(thm)],[c_12,c_106])).

tff(c_6443,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_6432,c_109])).

tff(c_6452,plain,(
    ! [A_15] : k2_zfmisc_1(A_15,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6443,c_6443,c_26])).

tff(c_6975,plain,(
    ! [A_803,B_804,C_805,D_806] :
      ( r2_relset_1(A_803,B_804,C_805,C_805)
      | ~ m1_subset_1(D_806,k1_zfmisc_1(k2_zfmisc_1(A_803,B_804)))
      | ~ m1_subset_1(C_805,k1_zfmisc_1(k2_zfmisc_1(A_803,B_804))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_6979,plain,(
    ! [A_15,C_805,D_806] :
      ( r2_relset_1(A_15,'#skF_6',C_805,C_805)
      | ~ m1_subset_1(D_806,k1_zfmisc_1('#skF_6'))
      | ~ m1_subset_1(C_805,k1_zfmisc_1(k2_zfmisc_1(A_15,'#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6452,c_6975])).

tff(c_6984,plain,(
    ! [A_15,C_805,D_806] :
      ( r2_relset_1(A_15,'#skF_6',C_805,C_805)
      | ~ m1_subset_1(D_806,k1_zfmisc_1('#skF_6'))
      | ~ m1_subset_1(C_805,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6452,c_6979])).

tff(c_7130,plain,(
    ! [D_806] : ~ m1_subset_1(D_806,k1_zfmisc_1('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_6984])).

tff(c_7143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7130,c_6413])).

tff(c_7145,plain,(
    ! [A_839,C_840] :
      ( r2_relset_1(A_839,'#skF_6',C_840,C_840)
      | ~ m1_subset_1(C_840,k1_zfmisc_1('#skF_6')) ) ),
    inference(splitRight,[status(thm)],[c_6984])).

tff(c_7151,plain,(
    ! [A_839] : r2_relset_1(A_839,'#skF_6','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_6413,c_7145])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_130,plain,(
    ! [E_57] :
      ( k1_funct_1('#skF_7',E_57) = k1_funct_1('#skF_6',E_57)
      | ~ r2_hidden(E_57,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_135,plain,
    ( k1_funct_1('#skF_7','#skF_1'('#skF_4')) = k1_funct_1('#skF_6','#skF_1'('#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_130])).

tff(c_194,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_200,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_194,c_109])).

tff(c_207,plain,(
    ! [A_12] : r1_tarski('#skF_4',A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_20])).

tff(c_28,plain,(
    ! [B_16] : k2_zfmisc_1(k1_xboole_0,B_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_205,plain,(
    ! [B_16] : k2_zfmisc_1('#skF_4',B_16) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_200,c_200,c_28])).

tff(c_240,plain,(
    r1_tarski('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_128])).

tff(c_275,plain,(
    ! [B_75,A_76] :
      ( B_75 = A_76
      | ~ r1_tarski(B_75,A_76)
      | ~ r1_tarski(A_76,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_277,plain,
    ( '#skF_7' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_7') ),
    inference(resolution,[status(thm)],[c_240,c_275])).

tff(c_288,plain,(
    '#skF_7' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_277])).

tff(c_241,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_60])).

tff(c_299,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_241])).

tff(c_538,plain,(
    ! [A_112,B_113,C_114,D_115] :
      ( r2_relset_1(A_112,B_113,C_114,C_114)
      | ~ m1_subset_1(D_115,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113)))
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_540,plain,(
    ! [B_16,C_114,D_115] :
      ( r2_relset_1('#skF_4',B_16,C_114,C_114)
      | ~ m1_subset_1(D_115,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_16))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_538])).

tff(c_546,plain,(
    ! [B_16,C_114,D_115] :
      ( r2_relset_1('#skF_4',B_16,C_114,C_114)
      | ~ m1_subset_1(D_115,k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1(C_114,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_540])).

tff(c_806,plain,(
    ! [D_115] : ~ m1_subset_1(D_115,k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_546])).

tff(c_821,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_806,c_299])).

tff(c_823,plain,(
    ! [B_158,C_159] :
      ( r2_relset_1('#skF_4',B_158,C_159,C_159)
      | ~ m1_subset_1(C_159,k1_zfmisc_1('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_546])).

tff(c_829,plain,(
    ! [B_158] : r2_relset_1('#skF_4',B_158,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_299,c_823])).

tff(c_239,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_129])).

tff(c_279,plain,
    ( '#skF_6' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_239,c_275])).

tff(c_291,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_279])).

tff(c_302,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_56])).

tff(c_379,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_302])).

tff(c_833,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_829,c_379])).

tff(c_835,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_6372,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 != '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_6362,c_24])).

tff(c_6717,plain,
    ( '#skF_5' = '#skF_6'
    | '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6411,c_6443,c_6443,c_6443,c_6372])).

tff(c_6718,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_6717])).

tff(c_6741,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6718,c_6432])).

tff(c_6747,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_835,c_6741])).

tff(c_6748,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_6717])).

tff(c_6421,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6411,c_56])).

tff(c_6751,plain,(
    ~ r2_relset_1('#skF_4','#skF_6','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6748,c_6421])).

tff(c_7155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7151,c_6751])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:44:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.71/2.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.13/2.41  
% 7.13/2.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.20/2.41  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 7.20/2.41  
% 7.20/2.41  %Foreground sorts:
% 7.20/2.41  
% 7.20/2.41  
% 7.20/2.41  %Background operators:
% 7.20/2.41  
% 7.20/2.41  
% 7.20/2.41  %Foreground operators:
% 7.20/2.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.20/2.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.20/2.41  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.20/2.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.20/2.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.20/2.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.20/2.41  tff('#skF_7', type, '#skF_7': $i).
% 7.20/2.41  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.20/2.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.20/2.41  tff('#skF_5', type, '#skF_5': $i).
% 7.20/2.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.20/2.41  tff('#skF_6', type, '#skF_6': $i).
% 7.20/2.41  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.20/2.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.20/2.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.20/2.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.20/2.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.20/2.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.20/2.41  tff('#skF_4', type, '#skF_4': $i).
% 7.20/2.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.20/2.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.20/2.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.20/2.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.20/2.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.20/2.41  
% 7.20/2.44  tff(f_136, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 7.20/2.44  tff(f_97, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 7.20/2.44  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.20/2.44  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.20/2.44  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.20/2.44  tff(f_83, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 7.20/2.44  tff(f_47, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.20/2.44  tff(f_61, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.20/2.44  tff(f_65, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.20/2.44  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.20/2.44  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.20/2.44  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.20/2.44  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.20/2.44  tff(f_55, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 7.20/2.44  tff(c_66, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.20/2.44  tff(c_60, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.20/2.44  tff(c_1391, plain, (![A_232, B_233, C_234, D_235]: (r2_relset_1(A_232, B_233, C_234, C_234) | ~m1_subset_1(D_235, k1_zfmisc_1(k2_zfmisc_1(A_232, B_233))) | ~m1_subset_1(C_234, k1_zfmisc_1(k2_zfmisc_1(A_232, B_233))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.20/2.44  tff(c_1408, plain, (![C_236]: (r2_relset_1('#skF_4', '#skF_5', C_236, C_236) | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))))), inference(resolution, [status(thm)], [c_60, c_1391])).
% 7.20/2.44  tff(c_1418, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_66, c_1408])).
% 7.20/2.44  tff(c_137, plain, (![C_60, A_61, B_62]: (v1_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.20/2.44  tff(c_153, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_60, c_137])).
% 7.20/2.44  tff(c_64, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.20/2.44  tff(c_62, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.20/2.44  tff(c_1118, plain, (![A_191, B_192, C_193]: (k1_relset_1(A_191, B_192, C_193)=k1_relat_1(C_193) | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(A_191, B_192))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.20/2.44  tff(c_1136, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_60, c_1118])).
% 7.20/2.44  tff(c_1196, plain, (![B_205, A_206, C_207]: (k1_xboole_0=B_205 | k1_relset_1(A_206, B_205, C_207)=A_206 | ~v1_funct_2(C_207, A_206, B_205) | ~m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(A_206, B_205))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.20/2.44  tff(c_1203, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_60, c_1196])).
% 7.20/2.44  tff(c_1216, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1136, c_1203])).
% 7.20/2.44  tff(c_1221, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_1216])).
% 7.20/2.44  tff(c_154, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_137])).
% 7.20/2.44  tff(c_70, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.20/2.44  tff(c_68, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.20/2.44  tff(c_1137, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_1118])).
% 7.20/2.44  tff(c_1206, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_66, c_1196])).
% 7.20/2.44  tff(c_1219, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1137, c_1206])).
% 7.20/2.44  tff(c_1227, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_1219])).
% 7.20/2.44  tff(c_1440, plain, (![A_238, B_239]: (r2_hidden('#skF_3'(A_238, B_239), k1_relat_1(A_238)) | B_239=A_238 | k1_relat_1(B_239)!=k1_relat_1(A_238) | ~v1_funct_1(B_239) | ~v1_relat_1(B_239) | ~v1_funct_1(A_238) | ~v1_relat_1(A_238))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.20/2.44  tff(c_1448, plain, (![B_239]: (r2_hidden('#skF_3'('#skF_6', B_239), '#skF_4') | B_239='#skF_6' | k1_relat_1(B_239)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_239) | ~v1_relat_1(B_239) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1227, c_1440])).
% 7.20/2.44  tff(c_1866, plain, (![B_290]: (r2_hidden('#skF_3'('#skF_6', B_290), '#skF_4') | B_290='#skF_6' | k1_relat_1(B_290)!='#skF_4' | ~v1_funct_1(B_290) | ~v1_relat_1(B_290))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_70, c_1227, c_1448])).
% 7.20/2.44  tff(c_58, plain, (![E_42]: (k1_funct_1('#skF_7', E_42)=k1_funct_1('#skF_6', E_42) | ~r2_hidden(E_42, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.20/2.44  tff(c_2663, plain, (![B_343]: (k1_funct_1('#skF_7', '#skF_3'('#skF_6', B_343))=k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_343)) | B_343='#skF_6' | k1_relat_1(B_343)!='#skF_4' | ~v1_funct_1(B_343) | ~v1_relat_1(B_343))), inference(resolution, [status(thm)], [c_1866, c_58])).
% 7.20/2.44  tff(c_34, plain, (![B_23, A_19]: (k1_funct_1(B_23, '#skF_3'(A_19, B_23))!=k1_funct_1(A_19, '#skF_3'(A_19, B_23)) | B_23=A_19 | k1_relat_1(B_23)!=k1_relat_1(A_19) | ~v1_funct_1(B_23) | ~v1_relat_1(B_23) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.20/2.44  tff(c_2670, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_7'='#skF_6' | k1_relat_1('#skF_7')!='#skF_4' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2663, c_34])).
% 7.20/2.44  tff(c_2677, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_153, c_64, c_1221, c_154, c_70, c_1221, c_1227, c_2670])).
% 7.20/2.44  tff(c_56, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.20/2.44  tff(c_2705, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2677, c_56])).
% 7.20/2.44  tff(c_2716, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1418, c_2705])).
% 7.20/2.44  tff(c_2717, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1219])).
% 7.20/2.44  tff(c_20, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.20/2.44  tff(c_2736, plain, (![A_12]: (r1_tarski('#skF_5', A_12))), inference(demodulation, [status(thm), theory('equality')], [c_2717, c_20])).
% 7.20/2.44  tff(c_26, plain, (![A_15]: (k2_zfmisc_1(A_15, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.20/2.44  tff(c_2735, plain, (![A_15]: (k2_zfmisc_1(A_15, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2717, c_2717, c_26])).
% 7.20/2.44  tff(c_117, plain, (![A_55, B_56]: (r1_tarski(A_55, B_56) | ~m1_subset_1(A_55, k1_zfmisc_1(B_56)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.20/2.44  tff(c_129, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_66, c_117])).
% 7.20/2.44  tff(c_852, plain, (![B_162, A_163]: (B_162=A_163 | ~r1_tarski(B_162, A_163) | ~r1_tarski(A_163, B_162))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.20/2.44  tff(c_864, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6' | ~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_129, c_852])).
% 7.20/2.44  tff(c_1035, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_864])).
% 7.20/2.44  tff(c_2800, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2735, c_1035])).
% 7.20/2.44  tff(c_2809, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2736, c_2800])).
% 7.20/2.44  tff(c_2810, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1216])).
% 7.20/2.44  tff(c_2829, plain, (![A_12]: (r1_tarski('#skF_5', A_12))), inference(demodulation, [status(thm), theory('equality')], [c_2810, c_20])).
% 7.20/2.44  tff(c_2828, plain, (![A_15]: (k2_zfmisc_1(A_15, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2810, c_2810, c_26])).
% 7.20/2.44  tff(c_2890, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2828, c_1035])).
% 7.20/2.44  tff(c_2899, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2829, c_2890])).
% 7.20/2.44  tff(c_2900, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_864])).
% 7.20/2.44  tff(c_128, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_60, c_117])).
% 7.20/2.44  tff(c_155, plain, (![A_63, B_64]: (r2_hidden('#skF_2'(A_63, B_64), A_63) | r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.20/2.44  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.20/2.44  tff(c_170, plain, (![A_63, B_64]: (~v1_xboole_0(A_63) | r1_tarski(A_63, B_64))), inference(resolution, [status(thm)], [c_155, c_2])).
% 7.20/2.44  tff(c_931, plain, (![B_170, A_171]: (B_170=A_171 | ~r1_tarski(B_170, A_171) | ~v1_xboole_0(A_171))), inference(resolution, [status(thm)], [c_170, c_852])).
% 7.20/2.44  tff(c_949, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_7' | ~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_128, c_931])).
% 7.20/2.44  tff(c_964, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_949])).
% 7.20/2.44  tff(c_2903, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2900, c_964])).
% 7.20/2.44  tff(c_18, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.20/2.44  tff(c_2906, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2900, c_60])).
% 7.20/2.44  tff(c_2994, plain, (![A_354, B_355, C_356]: (k1_relset_1(A_354, B_355, C_356)=k1_relat_1(C_356) | ~m1_subset_1(C_356, k1_zfmisc_1(k2_zfmisc_1(A_354, B_355))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.20/2.44  tff(c_3033, plain, (![C_360]: (k1_relset_1('#skF_4', '#skF_5', C_360)=k1_relat_1(C_360) | ~m1_subset_1(C_360, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_2900, c_2994])).
% 7.20/2.44  tff(c_3045, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_2906, c_3033])).
% 7.20/2.44  tff(c_3121, plain, (![B_370, A_371, C_372]: (k1_xboole_0=B_370 | k1_relset_1(A_371, B_370, C_372)=A_371 | ~v1_funct_2(C_372, A_371, B_370) | ~m1_subset_1(C_372, k1_zfmisc_1(k2_zfmisc_1(A_371, B_370))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.20/2.44  tff(c_3124, plain, (![C_372]: (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', C_372)='#skF_4' | ~v1_funct_2(C_372, '#skF_4', '#skF_5') | ~m1_subset_1(C_372, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_2900, c_3121])).
% 7.20/2.44  tff(c_3249, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_3124])).
% 7.20/2.44  tff(c_24, plain, (![B_16, A_15]: (k1_xboole_0=B_16 | k1_xboole_0=A_15 | k2_zfmisc_1(A_15, B_16)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.20/2.44  tff(c_2912, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0!='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_2900, c_24])).
% 7.20/2.44  tff(c_2993, plain, (k1_xboole_0!='#skF_6'), inference(splitLeft, [status(thm)], [c_2912])).
% 7.20/2.44  tff(c_3258, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_3249, c_2993])).
% 7.20/2.44  tff(c_3341, plain, (![A_396]: (k2_zfmisc_1(A_396, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3249, c_3249, c_26])).
% 7.20/2.44  tff(c_3354, plain, ('#skF_5'='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_3341, c_2900])).
% 7.20/2.44  tff(c_3368, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3258, c_3354])).
% 7.20/2.44  tff(c_3554, plain, (![C_421]: (k1_relset_1('#skF_4', '#skF_5', C_421)='#skF_4' | ~v1_funct_2(C_421, '#skF_4', '#skF_5') | ~m1_subset_1(C_421, k1_zfmisc_1('#skF_6')))), inference(splitRight, [status(thm)], [c_3124])).
% 7.20/2.44  tff(c_3560, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_2906, c_3554])).
% 7.20/2.44  tff(c_3570, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_3045, c_3560])).
% 7.20/2.44  tff(c_2907, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2900, c_66])).
% 7.20/2.44  tff(c_3044, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_2907, c_3033])).
% 7.20/2.44  tff(c_3557, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_2907, c_3554])).
% 7.20/2.44  tff(c_3567, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_3044, c_3557])).
% 7.20/2.44  tff(c_3680, plain, (![A_436, B_437]: (r2_hidden('#skF_3'(A_436, B_437), k1_relat_1(A_436)) | B_437=A_436 | k1_relat_1(B_437)!=k1_relat_1(A_436) | ~v1_funct_1(B_437) | ~v1_relat_1(B_437) | ~v1_funct_1(A_436) | ~v1_relat_1(A_436))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.20/2.44  tff(c_3691, plain, (![B_437]: (r2_hidden('#skF_3'('#skF_6', B_437), '#skF_4') | B_437='#skF_6' | k1_relat_1(B_437)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_437) | ~v1_relat_1(B_437) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3567, c_3680])).
% 7.20/2.44  tff(c_3840, plain, (![B_464]: (r2_hidden('#skF_3'('#skF_6', B_464), '#skF_4') | B_464='#skF_6' | k1_relat_1(B_464)!='#skF_4' | ~v1_funct_1(B_464) | ~v1_relat_1(B_464))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_70, c_3567, c_3691])).
% 7.20/2.44  tff(c_4023, plain, (![B_484]: (k1_funct_1('#skF_7', '#skF_3'('#skF_6', B_484))=k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_484)) | B_484='#skF_6' | k1_relat_1(B_484)!='#skF_4' | ~v1_funct_1(B_484) | ~v1_relat_1(B_484))), inference(resolution, [status(thm)], [c_3840, c_58])).
% 7.20/2.44  tff(c_4030, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_7'='#skF_6' | k1_relat_1('#skF_7')!='#skF_4' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_4023, c_34])).
% 7.20/2.44  tff(c_4037, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_153, c_64, c_3570, c_154, c_70, c_3567, c_3570, c_4030])).
% 7.20/2.44  tff(c_865, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_7' | ~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_7')), inference(resolution, [status(thm)], [c_128, c_852])).
% 7.20/2.44  tff(c_1007, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_7')), inference(splitLeft, [status(thm)], [c_865])).
% 7.20/2.44  tff(c_2902, plain, (~r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2900, c_1007])).
% 7.20/2.44  tff(c_4053, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4037, c_2902])).
% 7.20/2.44  tff(c_4069, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_4053])).
% 7.20/2.44  tff(c_4071, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_2912])).
% 7.20/2.44  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.20/2.44  tff(c_4083, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4071, c_12])).
% 7.20/2.44  tff(c_4087, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2903, c_4083])).
% 7.20/2.44  tff(c_4088, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_7'), inference(splitRight, [status(thm)], [c_865])).
% 7.20/2.44  tff(c_4090, plain, (~v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_4088, c_964])).
% 7.20/2.44  tff(c_4093, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_4088, c_60])).
% 7.20/2.44  tff(c_4261, plain, (![A_497, B_498, C_499]: (k1_relset_1(A_497, B_498, C_499)=k1_relat_1(C_499) | ~m1_subset_1(C_499, k1_zfmisc_1(k2_zfmisc_1(A_497, B_498))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.20/2.44  tff(c_4384, plain, (![C_518]: (k1_relset_1('#skF_4', '#skF_5', C_518)=k1_relat_1(C_518) | ~m1_subset_1(C_518, k1_zfmisc_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_4088, c_4261])).
% 7.20/2.44  tff(c_4396, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_4093, c_4384])).
% 7.20/2.44  tff(c_4483, plain, (![B_528, A_529, C_530]: (k1_xboole_0=B_528 | k1_relset_1(A_529, B_528, C_530)=A_529 | ~v1_funct_2(C_530, A_529, B_528) | ~m1_subset_1(C_530, k1_zfmisc_1(k2_zfmisc_1(A_529, B_528))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 7.20/2.44  tff(c_4486, plain, (![C_530]: (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', C_530)='#skF_4' | ~v1_funct_2(C_530, '#skF_4', '#skF_5') | ~m1_subset_1(C_530, k1_zfmisc_1('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_4088, c_4483])).
% 7.20/2.44  tff(c_4533, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_4486])).
% 7.20/2.44  tff(c_4099, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0!='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_4088, c_24])).
% 7.20/2.44  tff(c_4204, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_4099])).
% 7.20/2.44  tff(c_4544, plain, ('#skF_7'!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4533, c_4204])).
% 7.20/2.44  tff(c_4555, plain, (![A_15]: (k2_zfmisc_1(A_15, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4533, c_4533, c_26])).
% 7.20/2.44  tff(c_4653, plain, ('#skF_7'='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_4555, c_4088])).
% 7.20/2.44  tff(c_4655, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4544, c_4653])).
% 7.20/2.44  tff(c_4759, plain, (![C_558]: (k1_relset_1('#skF_4', '#skF_5', C_558)='#skF_4' | ~v1_funct_2(C_558, '#skF_4', '#skF_5') | ~m1_subset_1(C_558, k1_zfmisc_1('#skF_7')))), inference(splitRight, [status(thm)], [c_4486])).
% 7.20/2.44  tff(c_4765, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_4093, c_4759])).
% 7.20/2.44  tff(c_4775, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_4396, c_4765])).
% 7.20/2.44  tff(c_4094, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_4088, c_66])).
% 7.20/2.44  tff(c_4395, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_4094, c_4384])).
% 7.20/2.44  tff(c_4762, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_4094, c_4759])).
% 7.20/2.44  tff(c_4772, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_4395, c_4762])).
% 7.20/2.44  tff(c_4962, plain, (![A_590, B_591]: (r2_hidden('#skF_3'(A_590, B_591), k1_relat_1(A_590)) | B_591=A_590 | k1_relat_1(B_591)!=k1_relat_1(A_590) | ~v1_funct_1(B_591) | ~v1_relat_1(B_591) | ~v1_funct_1(A_590) | ~v1_relat_1(A_590))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.20/2.44  tff(c_4973, plain, (![B_591]: (r2_hidden('#skF_3'('#skF_6', B_591), '#skF_4') | B_591='#skF_6' | k1_relat_1(B_591)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_591) | ~v1_relat_1(B_591) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_4772, c_4962])).
% 7.20/2.44  tff(c_5174, plain, (![B_613]: (r2_hidden('#skF_3'('#skF_6', B_613), '#skF_4') | B_613='#skF_6' | k1_relat_1(B_613)!='#skF_4' | ~v1_funct_1(B_613) | ~v1_relat_1(B_613))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_70, c_4772, c_4973])).
% 7.20/2.44  tff(c_5592, plain, (![B_654]: (k1_funct_1('#skF_7', '#skF_3'('#skF_6', B_654))=k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_654)) | B_654='#skF_6' | k1_relat_1(B_654)!='#skF_4' | ~v1_funct_1(B_654) | ~v1_relat_1(B_654))), inference(resolution, [status(thm)], [c_5174, c_58])).
% 7.20/2.44  tff(c_5599, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_7'='#skF_6' | k1_relat_1('#skF_7')!='#skF_4' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_5592, c_34])).
% 7.20/2.44  tff(c_5606, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_153, c_64, c_4775, c_154, c_70, c_4772, c_4775, c_5599])).
% 7.20/2.44  tff(c_4091, plain, (r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_4088, c_129])).
% 7.20/2.44  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.20/2.44  tff(c_4120, plain, ('#skF_7'='#skF_6' | ~r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_4091, c_14])).
% 7.20/2.44  tff(c_4175, plain, (~r1_tarski('#skF_7', '#skF_6')), inference(splitLeft, [status(thm)], [c_4120])).
% 7.20/2.44  tff(c_5639, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5606, c_4175])).
% 7.20/2.44  tff(c_5658, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_5639])).
% 7.20/2.44  tff(c_5660, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_4099])).
% 7.20/2.44  tff(c_5673, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_5660, c_12])).
% 7.20/2.44  tff(c_5677, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4090, c_5673])).
% 7.20/2.44  tff(c_5678, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_4120])).
% 7.20/2.44  tff(c_5690, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_5678, c_56])).
% 7.20/2.44  tff(c_5681, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_5678, c_4094])).
% 7.20/2.44  tff(c_5685, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_5678, c_4088])).
% 7.20/2.44  tff(c_6110, plain, (![A_720, B_721, C_722, D_723]: (r2_relset_1(A_720, B_721, C_722, C_722) | ~m1_subset_1(D_723, k1_zfmisc_1(k2_zfmisc_1(A_720, B_721))) | ~m1_subset_1(C_722, k1_zfmisc_1(k2_zfmisc_1(A_720, B_721))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.20/2.44  tff(c_6112, plain, (![C_722, D_723]: (r2_relset_1('#skF_4', '#skF_5', C_722, C_722) | ~m1_subset_1(D_723, k1_zfmisc_1('#skF_6')) | ~m1_subset_1(C_722, k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_5685, c_6110])).
% 7.20/2.44  tff(c_6120, plain, (![C_722, D_723]: (r2_relset_1('#skF_4', '#skF_5', C_722, C_722) | ~m1_subset_1(D_723, k1_zfmisc_1('#skF_6')) | ~m1_subset_1(C_722, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_5685, c_6112])).
% 7.20/2.44  tff(c_6346, plain, (![D_723]: (~m1_subset_1(D_723, k1_zfmisc_1('#skF_6')))), inference(splitLeft, [status(thm)], [c_6120])).
% 7.20/2.44  tff(c_6348, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6346, c_5681])).
% 7.20/2.44  tff(c_6352, plain, (![C_744]: (r2_relset_1('#skF_4', '#skF_5', C_744, C_744) | ~m1_subset_1(C_744, k1_zfmisc_1('#skF_6')))), inference(splitRight, [status(thm)], [c_6120])).
% 7.20/2.44  tff(c_6354, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_5681, c_6352])).
% 7.20/2.44  tff(c_6361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5690, c_6354])).
% 7.20/2.44  tff(c_6362, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_7'), inference(splitRight, [status(thm)], [c_949])).
% 7.20/2.44  tff(c_948, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6' | ~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_129, c_931])).
% 7.20/2.44  tff(c_6407, plain, ('#skF_7'='#skF_6' | ~v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6362, c_6362, c_948])).
% 7.20/2.44  tff(c_6408, plain, (~v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_6407])).
% 7.20/2.44  tff(c_6363, plain, (v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_949])).
% 7.20/2.44  tff(c_6409, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6362, c_6363])).
% 7.20/2.44  tff(c_6410, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6408, c_6409])).
% 7.20/2.44  tff(c_6411, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_6407])).
% 7.20/2.44  tff(c_6366, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_6362, c_60])).
% 7.20/2.44  tff(c_6413, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_6411, c_6411, c_6366])).
% 7.20/2.44  tff(c_6412, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_6407])).
% 7.20/2.44  tff(c_6432, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6411, c_6412])).
% 7.20/2.44  tff(c_106, plain, (![B_50, A_51]: (~v1_xboole_0(B_50) | B_50=A_51 | ~v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.20/2.44  tff(c_109, plain, (![A_51]: (k1_xboole_0=A_51 | ~v1_xboole_0(A_51))), inference(resolution, [status(thm)], [c_12, c_106])).
% 7.20/2.44  tff(c_6443, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_6432, c_109])).
% 7.20/2.44  tff(c_6452, plain, (![A_15]: (k2_zfmisc_1(A_15, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6443, c_6443, c_26])).
% 7.20/2.44  tff(c_6975, plain, (![A_803, B_804, C_805, D_806]: (r2_relset_1(A_803, B_804, C_805, C_805) | ~m1_subset_1(D_806, k1_zfmisc_1(k2_zfmisc_1(A_803, B_804))) | ~m1_subset_1(C_805, k1_zfmisc_1(k2_zfmisc_1(A_803, B_804))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.20/2.44  tff(c_6979, plain, (![A_15, C_805, D_806]: (r2_relset_1(A_15, '#skF_6', C_805, C_805) | ~m1_subset_1(D_806, k1_zfmisc_1('#skF_6')) | ~m1_subset_1(C_805, k1_zfmisc_1(k2_zfmisc_1(A_15, '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_6452, c_6975])).
% 7.20/2.44  tff(c_6984, plain, (![A_15, C_805, D_806]: (r2_relset_1(A_15, '#skF_6', C_805, C_805) | ~m1_subset_1(D_806, k1_zfmisc_1('#skF_6')) | ~m1_subset_1(C_805, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_6452, c_6979])).
% 7.20/2.44  tff(c_7130, plain, (![D_806]: (~m1_subset_1(D_806, k1_zfmisc_1('#skF_6')))), inference(splitLeft, [status(thm)], [c_6984])).
% 7.20/2.44  tff(c_7143, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7130, c_6413])).
% 7.20/2.44  tff(c_7145, plain, (![A_839, C_840]: (r2_relset_1(A_839, '#skF_6', C_840, C_840) | ~m1_subset_1(C_840, k1_zfmisc_1('#skF_6')))), inference(splitRight, [status(thm)], [c_6984])).
% 7.20/2.44  tff(c_7151, plain, (![A_839]: (r2_relset_1(A_839, '#skF_6', '#skF_6', '#skF_6'))), inference(resolution, [status(thm)], [c_6413, c_7145])).
% 7.20/2.44  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.20/2.44  tff(c_130, plain, (![E_57]: (k1_funct_1('#skF_7', E_57)=k1_funct_1('#skF_6', E_57) | ~r2_hidden(E_57, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.20/2.44  tff(c_135, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_4'))=k1_funct_1('#skF_6', '#skF_1'('#skF_4')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_130])).
% 7.20/2.44  tff(c_194, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_135])).
% 7.20/2.44  tff(c_200, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_194, c_109])).
% 7.20/2.44  tff(c_207, plain, (![A_12]: (r1_tarski('#skF_4', A_12))), inference(demodulation, [status(thm), theory('equality')], [c_200, c_20])).
% 7.20/2.44  tff(c_28, plain, (![B_16]: (k2_zfmisc_1(k1_xboole_0, B_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.20/2.44  tff(c_205, plain, (![B_16]: (k2_zfmisc_1('#skF_4', B_16)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_200, c_200, c_28])).
% 7.20/2.44  tff(c_240, plain, (r1_tarski('#skF_7', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_205, c_128])).
% 7.20/2.44  tff(c_275, plain, (![B_75, A_76]: (B_75=A_76 | ~r1_tarski(B_75, A_76) | ~r1_tarski(A_76, B_75))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.20/2.44  tff(c_277, plain, ('#skF_7'='#skF_4' | ~r1_tarski('#skF_4', '#skF_7')), inference(resolution, [status(thm)], [c_240, c_275])).
% 7.20/2.44  tff(c_288, plain, ('#skF_7'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_207, c_277])).
% 7.20/2.44  tff(c_241, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_60])).
% 7.20/2.44  tff(c_299, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_288, c_241])).
% 7.20/2.44  tff(c_538, plain, (![A_112, B_113, C_114, D_115]: (r2_relset_1(A_112, B_113, C_114, C_114) | ~m1_subset_1(D_115, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.20/2.44  tff(c_540, plain, (![B_16, C_114, D_115]: (r2_relset_1('#skF_4', B_16, C_114, C_114) | ~m1_subset_1(D_115, k1_zfmisc_1('#skF_4')) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_16))))), inference(superposition, [status(thm), theory('equality')], [c_205, c_538])).
% 7.20/2.44  tff(c_546, plain, (![B_16, C_114, D_115]: (r2_relset_1('#skF_4', B_16, C_114, C_114) | ~m1_subset_1(D_115, k1_zfmisc_1('#skF_4')) | ~m1_subset_1(C_114, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_540])).
% 7.20/2.44  tff(c_806, plain, (![D_115]: (~m1_subset_1(D_115, k1_zfmisc_1('#skF_4')))), inference(splitLeft, [status(thm)], [c_546])).
% 7.20/2.44  tff(c_821, plain, $false, inference(negUnitSimplification, [status(thm)], [c_806, c_299])).
% 7.20/2.44  tff(c_823, plain, (![B_158, C_159]: (r2_relset_1('#skF_4', B_158, C_159, C_159) | ~m1_subset_1(C_159, k1_zfmisc_1('#skF_4')))), inference(splitRight, [status(thm)], [c_546])).
% 7.20/2.44  tff(c_829, plain, (![B_158]: (r2_relset_1('#skF_4', B_158, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_299, c_823])).
% 7.20/2.44  tff(c_239, plain, (r1_tarski('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_205, c_129])).
% 7.20/2.44  tff(c_279, plain, ('#skF_6'='#skF_4' | ~r1_tarski('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_239, c_275])).
% 7.20/2.44  tff(c_291, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_207, c_279])).
% 7.20/2.44  tff(c_302, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_288, c_56])).
% 7.20/2.44  tff(c_379, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_291, c_302])).
% 7.20/2.44  tff(c_833, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_829, c_379])).
% 7.20/2.44  tff(c_835, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_135])).
% 7.20/2.44  tff(c_6372, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0!='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_6362, c_24])).
% 7.20/2.44  tff(c_6717, plain, ('#skF_5'='#skF_6' | '#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6411, c_6443, c_6443, c_6443, c_6372])).
% 7.20/2.44  tff(c_6718, plain, ('#skF_6'='#skF_4'), inference(splitLeft, [status(thm)], [c_6717])).
% 7.20/2.44  tff(c_6741, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6718, c_6432])).
% 7.20/2.44  tff(c_6747, plain, $false, inference(negUnitSimplification, [status(thm)], [c_835, c_6741])).
% 7.20/2.44  tff(c_6748, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_6717])).
% 7.20/2.44  tff(c_6421, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6411, c_56])).
% 7.20/2.44  tff(c_6751, plain, (~r2_relset_1('#skF_4', '#skF_6', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6748, c_6421])).
% 7.20/2.44  tff(c_7155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7151, c_6751])).
% 7.20/2.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.20/2.44  
% 7.20/2.44  Inference rules
% 7.20/2.44  ----------------------
% 7.20/2.44  #Ref     : 4
% 7.20/2.44  #Sup     : 1449
% 7.20/2.44  #Fact    : 0
% 7.20/2.44  #Define  : 0
% 7.20/2.44  #Split   : 56
% 7.20/2.44  #Chain   : 0
% 7.20/2.44  #Close   : 0
% 7.20/2.44  
% 7.20/2.44  Ordering : KBO
% 7.20/2.44  
% 7.20/2.44  Simplification rules
% 7.20/2.44  ----------------------
% 7.20/2.44  #Subsume      : 507
% 7.20/2.44  #Demod        : 1406
% 7.20/2.44  #Tautology    : 745
% 7.20/2.44  #SimpNegUnit  : 132
% 7.20/2.44  #BackRed      : 433
% 7.20/2.44  
% 7.20/2.44  #Partial instantiations: 0
% 7.20/2.44  #Strategies tried      : 1
% 7.20/2.44  
% 7.20/2.44  Timing (in seconds)
% 7.20/2.44  ----------------------
% 7.20/2.45  Preprocessing        : 0.35
% 7.20/2.45  Parsing              : 0.17
% 7.20/2.45  CNF conversion       : 0.03
% 7.20/2.45  Main loop            : 1.29
% 7.20/2.45  Inferencing          : 0.43
% 7.20/2.45  Reduction            : 0.43
% 7.20/2.45  Demodulation         : 0.29
% 7.20/2.45  BG Simplification    : 0.05
% 7.20/2.45  Subsumption          : 0.27
% 7.20/2.45  Abstraction          : 0.06
% 7.20/2.45  MUC search           : 0.00
% 7.20/2.45  Cooper               : 0.00
% 7.20/2.45  Total                : 1.72
% 7.20/2.45  Index Insertion      : 0.00
% 7.20/2.45  Index Deletion       : 0.00
% 7.20/2.45  Index Matching       : 0.00
% 7.20/2.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
