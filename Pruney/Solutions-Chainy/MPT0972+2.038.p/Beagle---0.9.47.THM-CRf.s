%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:40 EST 2020

% Result     : Theorem 4.63s
% Output     : CNFRefutation 4.90s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 926 expanded)
%              Number of leaves         :   32 ( 336 expanded)
%              Depth                    :   11
%              Number of atoms          :  273 (3275 expanded)
%              Number of equality atoms :  104 (1075 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_129,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_108,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_69,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_38,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1101,plain,(
    ! [A_207,B_208,D_209] :
      ( r2_relset_1(A_207,B_208,D_209,D_209)
      | ~ m1_subset_1(D_209,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1111,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_1101])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_96,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_107,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_96])).

tff(c_60,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_58,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1124,plain,(
    ! [A_215,B_216,C_217] :
      ( k1_relset_1(A_215,B_216,C_217) = k1_relat_1(C_217)
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1(A_215,B_216))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1137,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_1124])).

tff(c_1179,plain,(
    ! [B_229,A_230,C_231] :
      ( k1_xboole_0 = B_229
      | k1_relset_1(A_230,B_229,C_231) = A_230
      | ~ v1_funct_2(C_231,A_230,B_229)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_230,B_229))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1182,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_1179])).

tff(c_1194,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1137,c_1182])).

tff(c_1199,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1194])).

tff(c_108,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_96])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_52,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1138,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_1124])).

tff(c_1185,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1179])).

tff(c_1197,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1138,c_1185])).

tff(c_1205,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1197])).

tff(c_1440,plain,(
    ! [A_270,B_271] :
      ( r2_hidden('#skF_2'(A_270,B_271),k1_relat_1(A_270))
      | B_271 = A_270
      | k1_relat_1(B_271) != k1_relat_1(A_270)
      | ~ v1_funct_1(B_271)
      | ~ v1_relat_1(B_271)
      | ~ v1_funct_1(A_270)
      | ~ v1_relat_1(A_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1450,plain,(
    ! [B_271] :
      ( r2_hidden('#skF_2'('#skF_6',B_271),'#skF_3')
      | B_271 = '#skF_6'
      | k1_relat_1(B_271) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_271)
      | ~ v1_relat_1(B_271)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1205,c_1440])).

tff(c_1488,plain,(
    ! [B_282] :
      ( r2_hidden('#skF_2'('#skF_6',B_282),'#skF_3')
      | B_282 = '#skF_6'
      | k1_relat_1(B_282) != '#skF_3'
      | ~ v1_funct_1(B_282)
      | ~ v1_relat_1(B_282) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_54,c_1205,c_1450])).

tff(c_48,plain,(
    ! [E_39] :
      ( k1_funct_1('#skF_5',E_39) = k1_funct_1('#skF_6',E_39)
      | ~ r2_hidden(E_39,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1545,plain,(
    ! [B_292] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_6',B_292)) = k1_funct_1('#skF_6','#skF_2'('#skF_6',B_292))
      | B_292 = '#skF_6'
      | k1_relat_1(B_292) != '#skF_3'
      | ~ v1_funct_1(B_292)
      | ~ v1_relat_1(B_292) ) ),
    inference(resolution,[status(thm)],[c_1488,c_48])).

tff(c_20,plain,(
    ! [B_18,A_14] :
      ( k1_funct_1(B_18,'#skF_2'(A_14,B_18)) != k1_funct_1(A_14,'#skF_2'(A_14,B_18))
      | B_18 = A_14
      | k1_relat_1(B_18) != k1_relat_1(A_14)
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1552,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != '#skF_3'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1545,c_20])).

tff(c_1559,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_60,c_1199,c_108,c_54,c_1205,c_1199,c_1552])).

tff(c_46,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1577,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1559,c_46])).

tff(c_1588,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1111,c_1577])).

tff(c_1589,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1197])).

tff(c_14,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1608,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1589,c_1589,c_14])).

tff(c_1625,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1608,c_50])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1097,plain,(
    ! [C_204,A_205,B_206] :
      ( r2_hidden(C_204,A_205)
      | ~ r2_hidden(C_204,B_206)
      | ~ m1_subset_1(B_206,k1_zfmisc_1(A_205)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2013,plain,(
    ! [A_346,B_347,A_348] :
      ( r2_hidden('#skF_1'(A_346,B_347),A_348)
      | ~ m1_subset_1(A_346,k1_zfmisc_1(A_348))
      | r1_tarski(A_346,B_347) ) ),
    inference(resolution,[status(thm)],[c_6,c_1097])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2034,plain,(
    ! [A_349,A_350] :
      ( ~ m1_subset_1(A_349,k1_zfmisc_1(A_350))
      | r1_tarski(A_349,A_350) ) ),
    inference(resolution,[status(thm)],[c_2013,c_4])).

tff(c_2044,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_1625,c_2034])).

tff(c_10,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1607,plain,(
    ! [A_7] :
      ( A_7 = '#skF_4'
      | ~ r1_tarski(A_7,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1589,c_1589,c_10])).

tff(c_2054,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2044,c_1607])).

tff(c_1590,plain,(
    k1_relat_1('#skF_6') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1197])).

tff(c_2063,plain,(
    k1_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2054,c_1590])).

tff(c_1624,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1608,c_56])).

tff(c_2045,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_1624,c_2034])).

tff(c_2099,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2045,c_1607])).

tff(c_2107,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2099,c_1199])).

tff(c_2128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2063,c_2107])).

tff(c_2129,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1194])).

tff(c_161,plain,(
    ! [A_66,B_67,D_68] :
      ( r2_relset_1(A_66,B_67,D_68,D_68)
      | ~ m1_subset_1(D_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_171,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_161])).

tff(c_218,plain,(
    ! [A_83,B_84,C_85] :
      ( k1_relset_1(A_83,B_84,C_85) = k1_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_231,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_218])).

tff(c_352,plain,(
    ! [B_116,A_117,C_118] :
      ( k1_xboole_0 = B_116
      | k1_relset_1(A_117,B_116,C_118) = A_117
      | ~ v1_funct_2(C_118,A_117,B_116)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_117,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_355,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_352])).

tff(c_367,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_231,c_355])).

tff(c_372,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_367])).

tff(c_232,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_50,c_218])).

tff(c_358,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_352])).

tff(c_370,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_232,c_358])).

tff(c_378,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_370])).

tff(c_623,plain,(
    ! [A_170,B_171] :
      ( r2_hidden('#skF_2'(A_170,B_171),k1_relat_1(A_170))
      | B_171 = A_170
      | k1_relat_1(B_171) != k1_relat_1(A_170)
      | ~ v1_funct_1(B_171)
      | ~ v1_relat_1(B_171)
      | ~ v1_funct_1(A_170)
      | ~ v1_relat_1(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_633,plain,(
    ! [B_171] :
      ( r2_hidden('#skF_2'('#skF_6',B_171),'#skF_3')
      | B_171 = '#skF_6'
      | k1_relat_1(B_171) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_171)
      | ~ v1_relat_1(B_171)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_623])).

tff(c_645,plain,(
    ! [B_172] :
      ( r2_hidden('#skF_2'('#skF_6',B_172),'#skF_3')
      | B_172 = '#skF_6'
      | k1_relat_1(B_172) != '#skF_3'
      | ~ v1_funct_1(B_172)
      | ~ v1_relat_1(B_172) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_54,c_378,c_633])).

tff(c_658,plain,(
    ! [B_172] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_6',B_172)) = k1_funct_1('#skF_6','#skF_2'('#skF_6',B_172))
      | B_172 = '#skF_6'
      | k1_relat_1(B_172) != '#skF_3'
      | ~ v1_funct_1(B_172)
      | ~ v1_relat_1(B_172) ) ),
    inference(resolution,[status(thm)],[c_645,c_48])).

tff(c_718,plain,(
    ! [B_180,A_181] :
      ( k1_funct_1(B_180,'#skF_2'(A_181,B_180)) != k1_funct_1(A_181,'#skF_2'(A_181,B_180))
      | B_180 = A_181
      | k1_relat_1(B_180) != k1_relat_1(A_181)
      | ~ v1_funct_1(B_180)
      | ~ v1_relat_1(B_180)
      | ~ v1_funct_1(A_181)
      | ~ v1_relat_1(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_722,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != '#skF_3'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_658,c_718])).

tff(c_725,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_60,c_372,c_108,c_54,c_378,c_372,c_722])).

tff(c_747,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_725,c_46])).

tff(c_758,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_747])).

tff(c_759,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_370])).

tff(c_34,plain,(
    ! [A_32] :
      ( v1_funct_2(k1_xboole_0,A_32,k1_xboole_0)
      | k1_xboole_0 = A_32
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_32,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_63,plain,(
    ! [A_32] :
      ( v1_funct_2(k1_xboole_0,A_32,k1_xboole_0)
      | k1_xboole_0 = A_32
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_34])).

tff(c_156,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_771,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_759,c_759,c_156])).

tff(c_775,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_759,c_759,c_14])).

tff(c_157,plain,(
    ! [C_63,A_64,B_65] :
      ( r2_hidden(C_63,A_64)
      | ~ r2_hidden(C_63,B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_252,plain,(
    ! [A_91,B_92,A_93] :
      ( r2_hidden('#skF_1'(A_91,B_92),A_93)
      | ~ m1_subset_1(A_91,k1_zfmisc_1(A_93))
      | r1_tarski(A_91,B_92) ) ),
    inference(resolution,[status(thm)],[c_6,c_157])).

tff(c_273,plain,(
    ! [A_94,A_95] :
      ( ~ m1_subset_1(A_94,k1_zfmisc_1(A_95))
      | r1_tarski(A_94,A_95) ) ),
    inference(resolution,[status(thm)],[c_252,c_4])).

tff(c_280,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_273])).

tff(c_820,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_775,c_280])).

tff(c_874,plain,(
    ! [A_190] :
      ( A_190 = '#skF_4'
      | ~ r1_tarski(A_190,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_759,c_759,c_10])).

tff(c_889,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_820,c_874])).

tff(c_821,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_775,c_56])).

tff(c_896,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_889,c_821])).

tff(c_909,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_771,c_896])).

tff(c_910,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_367])).

tff(c_922,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_910,c_910,c_156])).

tff(c_926,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_910,c_910,c_14])).

tff(c_969,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_926,c_280])).

tff(c_1045,plain,(
    ! [A_201] :
      ( A_201 = '#skF_4'
      | ~ r1_tarski(A_201,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_910,c_910,c_10])).

tff(c_1060,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_969,c_1045])).

tff(c_970,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_926,c_56])).

tff(c_1067,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1060,c_970])).

tff(c_1080,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_922,c_1067])).

tff(c_1082,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_1119,plain,(
    ! [A_212,D_213] :
      ( r2_relset_1(A_212,k1_xboole_0,D_213,D_213)
      | ~ m1_subset_1(D_213,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1101])).

tff(c_1122,plain,(
    ! [A_212] : r2_relset_1(A_212,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1082,c_1119])).

tff(c_2139,plain,(
    ! [A_212] : r2_relset_1(A_212,'#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2129,c_2129,c_2129,c_1122])).

tff(c_2148,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2129,c_2129,c_14])).

tff(c_2164,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2148,c_56])).

tff(c_2492,plain,(
    ! [A_402,B_403,A_404] :
      ( r2_hidden('#skF_1'(A_402,B_403),A_404)
      | ~ m1_subset_1(A_402,k1_zfmisc_1(A_404))
      | r1_tarski(A_402,B_403) ) ),
    inference(resolution,[status(thm)],[c_6,c_1097])).

tff(c_2535,plain,(
    ! [A_407,A_408] :
      ( ~ m1_subset_1(A_407,k1_zfmisc_1(A_408))
      | r1_tarski(A_407,A_408) ) ),
    inference(resolution,[status(thm)],[c_2492,c_4])).

tff(c_2548,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_2164,c_2535])).

tff(c_2147,plain,(
    ! [A_7] :
      ( A_7 = '#skF_4'
      | ~ r1_tarski(A_7,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2129,c_2129,c_10])).

tff(c_2586,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2548,c_2147])).

tff(c_2165,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2148,c_50])).

tff(c_2547,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_2165,c_2535])).

tff(c_2555,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2547,c_2147])).

tff(c_2566,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2555,c_46])).

tff(c_2632,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2139,c_2586,c_2566])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n007.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 09:39:51 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.63/1.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.81/1.82  
% 4.81/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.81/1.82  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.81/1.82  
% 4.81/1.82  %Foreground sorts:
% 4.81/1.82  
% 4.81/1.82  
% 4.81/1.82  %Background operators:
% 4.81/1.82  
% 4.81/1.82  
% 4.81/1.82  %Foreground operators:
% 4.81/1.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.81/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.81/1.82  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.81/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.81/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.81/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.81/1.82  tff('#skF_5', type, '#skF_5': $i).
% 4.81/1.82  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.81/1.82  tff('#skF_6', type, '#skF_6': $i).
% 4.81/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.81/1.82  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.81/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.81/1.82  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.81/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.81/1.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.81/1.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.81/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.81/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.81/1.82  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.81/1.82  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.81/1.82  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.81/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.81/1.82  
% 4.90/1.84  tff(f_129, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_2)).
% 4.90/1.84  tff(f_90, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.90/1.84  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.90/1.84  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.90/1.84  tff(f_108, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.90/1.84  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 4.90/1.84  tff(f_44, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.90/1.84  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.90/1.84  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 4.90/1.84  tff(f_38, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 4.90/1.84  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.90/1.84  tff(c_1101, plain, (![A_207, B_208, D_209]: (r2_relset_1(A_207, B_208, D_209, D_209) | ~m1_subset_1(D_209, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.90/1.84  tff(c_1111, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_50, c_1101])).
% 4.90/1.84  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.90/1.84  tff(c_96, plain, (![C_46, A_47, B_48]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.90/1.84  tff(c_107, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_96])).
% 4.90/1.84  tff(c_60, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.90/1.84  tff(c_58, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.90/1.84  tff(c_1124, plain, (![A_215, B_216, C_217]: (k1_relset_1(A_215, B_216, C_217)=k1_relat_1(C_217) | ~m1_subset_1(C_217, k1_zfmisc_1(k2_zfmisc_1(A_215, B_216))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.90/1.84  tff(c_1137, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_1124])).
% 4.90/1.84  tff(c_1179, plain, (![B_229, A_230, C_231]: (k1_xboole_0=B_229 | k1_relset_1(A_230, B_229, C_231)=A_230 | ~v1_funct_2(C_231, A_230, B_229) | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(A_230, B_229))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.90/1.84  tff(c_1182, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_1179])).
% 4.90/1.84  tff(c_1194, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1137, c_1182])).
% 4.90/1.84  tff(c_1199, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_1194])).
% 4.90/1.84  tff(c_108, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_96])).
% 4.90/1.84  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.90/1.84  tff(c_52, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.90/1.84  tff(c_1138, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_1124])).
% 4.90/1.84  tff(c_1185, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_1179])).
% 4.90/1.84  tff(c_1197, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1138, c_1185])).
% 4.90/1.84  tff(c_1205, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_1197])).
% 4.90/1.84  tff(c_1440, plain, (![A_270, B_271]: (r2_hidden('#skF_2'(A_270, B_271), k1_relat_1(A_270)) | B_271=A_270 | k1_relat_1(B_271)!=k1_relat_1(A_270) | ~v1_funct_1(B_271) | ~v1_relat_1(B_271) | ~v1_funct_1(A_270) | ~v1_relat_1(A_270))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.90/1.84  tff(c_1450, plain, (![B_271]: (r2_hidden('#skF_2'('#skF_6', B_271), '#skF_3') | B_271='#skF_6' | k1_relat_1(B_271)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_271) | ~v1_relat_1(B_271) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1205, c_1440])).
% 4.90/1.84  tff(c_1488, plain, (![B_282]: (r2_hidden('#skF_2'('#skF_6', B_282), '#skF_3') | B_282='#skF_6' | k1_relat_1(B_282)!='#skF_3' | ~v1_funct_1(B_282) | ~v1_relat_1(B_282))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_54, c_1205, c_1450])).
% 4.90/1.84  tff(c_48, plain, (![E_39]: (k1_funct_1('#skF_5', E_39)=k1_funct_1('#skF_6', E_39) | ~r2_hidden(E_39, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.90/1.84  tff(c_1545, plain, (![B_292]: (k1_funct_1('#skF_5', '#skF_2'('#skF_6', B_292))=k1_funct_1('#skF_6', '#skF_2'('#skF_6', B_292)) | B_292='#skF_6' | k1_relat_1(B_292)!='#skF_3' | ~v1_funct_1(B_292) | ~v1_relat_1(B_292))), inference(resolution, [status(thm)], [c_1488, c_48])).
% 4.90/1.84  tff(c_20, plain, (![B_18, A_14]: (k1_funct_1(B_18, '#skF_2'(A_14, B_18))!=k1_funct_1(A_14, '#skF_2'(A_14, B_18)) | B_18=A_14 | k1_relat_1(B_18)!=k1_relat_1(A_14) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.90/1.84  tff(c_1552, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_5'='#skF_6' | k1_relat_1('#skF_5')!='#skF_3' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1545, c_20])).
% 4.90/1.84  tff(c_1559, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_107, c_60, c_1199, c_108, c_54, c_1205, c_1199, c_1552])).
% 4.90/1.84  tff(c_46, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.90/1.84  tff(c_1577, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1559, c_46])).
% 4.90/1.84  tff(c_1588, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1111, c_1577])).
% 4.90/1.84  tff(c_1589, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1197])).
% 4.90/1.84  tff(c_14, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.90/1.84  tff(c_1608, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1589, c_1589, c_14])).
% 4.90/1.84  tff(c_1625, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1608, c_50])).
% 4.90/1.84  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.90/1.84  tff(c_1097, plain, (![C_204, A_205, B_206]: (r2_hidden(C_204, A_205) | ~r2_hidden(C_204, B_206) | ~m1_subset_1(B_206, k1_zfmisc_1(A_205)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.90/1.84  tff(c_2013, plain, (![A_346, B_347, A_348]: (r2_hidden('#skF_1'(A_346, B_347), A_348) | ~m1_subset_1(A_346, k1_zfmisc_1(A_348)) | r1_tarski(A_346, B_347))), inference(resolution, [status(thm)], [c_6, c_1097])).
% 4.90/1.84  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.90/1.84  tff(c_2034, plain, (![A_349, A_350]: (~m1_subset_1(A_349, k1_zfmisc_1(A_350)) | r1_tarski(A_349, A_350))), inference(resolution, [status(thm)], [c_2013, c_4])).
% 4.90/1.84  tff(c_2044, plain, (r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_1625, c_2034])).
% 4.90/1.84  tff(c_10, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.90/1.84  tff(c_1607, plain, (![A_7]: (A_7='#skF_4' | ~r1_tarski(A_7, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1589, c_1589, c_10])).
% 4.90/1.84  tff(c_2054, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_2044, c_1607])).
% 4.90/1.84  tff(c_1590, plain, (k1_relat_1('#skF_6')!='#skF_3'), inference(splitRight, [status(thm)], [c_1197])).
% 4.90/1.84  tff(c_2063, plain, (k1_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2054, c_1590])).
% 4.90/1.84  tff(c_1624, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1608, c_56])).
% 4.90/1.84  tff(c_2045, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_1624, c_2034])).
% 4.90/1.84  tff(c_2099, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_2045, c_1607])).
% 4.90/1.84  tff(c_2107, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2099, c_1199])).
% 4.90/1.84  tff(c_2128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2063, c_2107])).
% 4.90/1.84  tff(c_2129, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1194])).
% 4.90/1.84  tff(c_161, plain, (![A_66, B_67, D_68]: (r2_relset_1(A_66, B_67, D_68, D_68) | ~m1_subset_1(D_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.90/1.84  tff(c_171, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_50, c_161])).
% 4.90/1.84  tff(c_218, plain, (![A_83, B_84, C_85]: (k1_relset_1(A_83, B_84, C_85)=k1_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.90/1.84  tff(c_231, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_218])).
% 4.90/1.84  tff(c_352, plain, (![B_116, A_117, C_118]: (k1_xboole_0=B_116 | k1_relset_1(A_117, B_116, C_118)=A_117 | ~v1_funct_2(C_118, A_117, B_116) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_117, B_116))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.90/1.84  tff(c_355, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_352])).
% 4.90/1.84  tff(c_367, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_231, c_355])).
% 4.90/1.84  tff(c_372, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_367])).
% 4.90/1.84  tff(c_232, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_50, c_218])).
% 4.90/1.84  tff(c_358, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_352])).
% 4.90/1.84  tff(c_370, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_232, c_358])).
% 4.90/1.84  tff(c_378, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_370])).
% 4.90/1.84  tff(c_623, plain, (![A_170, B_171]: (r2_hidden('#skF_2'(A_170, B_171), k1_relat_1(A_170)) | B_171=A_170 | k1_relat_1(B_171)!=k1_relat_1(A_170) | ~v1_funct_1(B_171) | ~v1_relat_1(B_171) | ~v1_funct_1(A_170) | ~v1_relat_1(A_170))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.90/1.84  tff(c_633, plain, (![B_171]: (r2_hidden('#skF_2'('#skF_6', B_171), '#skF_3') | B_171='#skF_6' | k1_relat_1(B_171)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_171) | ~v1_relat_1(B_171) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_378, c_623])).
% 4.90/1.84  tff(c_645, plain, (![B_172]: (r2_hidden('#skF_2'('#skF_6', B_172), '#skF_3') | B_172='#skF_6' | k1_relat_1(B_172)!='#skF_3' | ~v1_funct_1(B_172) | ~v1_relat_1(B_172))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_54, c_378, c_633])).
% 4.90/1.84  tff(c_658, plain, (![B_172]: (k1_funct_1('#skF_5', '#skF_2'('#skF_6', B_172))=k1_funct_1('#skF_6', '#skF_2'('#skF_6', B_172)) | B_172='#skF_6' | k1_relat_1(B_172)!='#skF_3' | ~v1_funct_1(B_172) | ~v1_relat_1(B_172))), inference(resolution, [status(thm)], [c_645, c_48])).
% 4.90/1.84  tff(c_718, plain, (![B_180, A_181]: (k1_funct_1(B_180, '#skF_2'(A_181, B_180))!=k1_funct_1(A_181, '#skF_2'(A_181, B_180)) | B_180=A_181 | k1_relat_1(B_180)!=k1_relat_1(A_181) | ~v1_funct_1(B_180) | ~v1_relat_1(B_180) | ~v1_funct_1(A_181) | ~v1_relat_1(A_181))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.90/1.84  tff(c_722, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_5'='#skF_6' | k1_relat_1('#skF_5')!='#skF_3' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_658, c_718])).
% 4.90/1.84  tff(c_725, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_107, c_60, c_372, c_108, c_54, c_378, c_372, c_722])).
% 4.90/1.84  tff(c_747, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_725, c_46])).
% 4.90/1.84  tff(c_758, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_171, c_747])).
% 4.90/1.84  tff(c_759, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_370])).
% 4.90/1.84  tff(c_34, plain, (![A_32]: (v1_funct_2(k1_xboole_0, A_32, k1_xboole_0) | k1_xboole_0=A_32 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_32, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.90/1.84  tff(c_63, plain, (![A_32]: (v1_funct_2(k1_xboole_0, A_32, k1_xboole_0) | k1_xboole_0=A_32 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_34])).
% 4.90/1.84  tff(c_156, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_63])).
% 4.90/1.84  tff(c_771, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_759, c_759, c_156])).
% 4.90/1.84  tff(c_775, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_759, c_759, c_14])).
% 4.90/1.84  tff(c_157, plain, (![C_63, A_64, B_65]: (r2_hidden(C_63, A_64) | ~r2_hidden(C_63, B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.90/1.84  tff(c_252, plain, (![A_91, B_92, A_93]: (r2_hidden('#skF_1'(A_91, B_92), A_93) | ~m1_subset_1(A_91, k1_zfmisc_1(A_93)) | r1_tarski(A_91, B_92))), inference(resolution, [status(thm)], [c_6, c_157])).
% 4.90/1.84  tff(c_273, plain, (![A_94, A_95]: (~m1_subset_1(A_94, k1_zfmisc_1(A_95)) | r1_tarski(A_94, A_95))), inference(resolution, [status(thm)], [c_252, c_4])).
% 4.90/1.84  tff(c_280, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_56, c_273])).
% 4.90/1.84  tff(c_820, plain, (r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_775, c_280])).
% 4.90/1.84  tff(c_874, plain, (![A_190]: (A_190='#skF_4' | ~r1_tarski(A_190, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_759, c_759, c_10])).
% 4.90/1.84  tff(c_889, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_820, c_874])).
% 4.90/1.84  tff(c_821, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_775, c_56])).
% 4.90/1.84  tff(c_896, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_889, c_821])).
% 4.90/1.84  tff(c_909, plain, $false, inference(negUnitSimplification, [status(thm)], [c_771, c_896])).
% 4.90/1.84  tff(c_910, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_367])).
% 4.90/1.84  tff(c_922, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_910, c_910, c_156])).
% 4.90/1.84  tff(c_926, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_910, c_910, c_14])).
% 4.90/1.84  tff(c_969, plain, (r1_tarski('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_926, c_280])).
% 4.90/1.84  tff(c_1045, plain, (![A_201]: (A_201='#skF_4' | ~r1_tarski(A_201, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_910, c_910, c_10])).
% 4.90/1.84  tff(c_1060, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_969, c_1045])).
% 4.90/1.84  tff(c_970, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_926, c_56])).
% 4.90/1.84  tff(c_1067, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1060, c_970])).
% 4.90/1.84  tff(c_1080, plain, $false, inference(negUnitSimplification, [status(thm)], [c_922, c_1067])).
% 4.90/1.84  tff(c_1082, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_63])).
% 4.90/1.84  tff(c_1119, plain, (![A_212, D_213]: (r2_relset_1(A_212, k1_xboole_0, D_213, D_213) | ~m1_subset_1(D_213, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1101])).
% 4.90/1.84  tff(c_1122, plain, (![A_212]: (r2_relset_1(A_212, k1_xboole_0, k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_1082, c_1119])).
% 4.90/1.84  tff(c_2139, plain, (![A_212]: (r2_relset_1(A_212, '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2129, c_2129, c_2129, c_1122])).
% 4.90/1.84  tff(c_2148, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2129, c_2129, c_14])).
% 4.90/1.84  tff(c_2164, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2148, c_56])).
% 4.90/1.84  tff(c_2492, plain, (![A_402, B_403, A_404]: (r2_hidden('#skF_1'(A_402, B_403), A_404) | ~m1_subset_1(A_402, k1_zfmisc_1(A_404)) | r1_tarski(A_402, B_403))), inference(resolution, [status(thm)], [c_6, c_1097])).
% 4.90/1.84  tff(c_2535, plain, (![A_407, A_408]: (~m1_subset_1(A_407, k1_zfmisc_1(A_408)) | r1_tarski(A_407, A_408))), inference(resolution, [status(thm)], [c_2492, c_4])).
% 4.90/1.84  tff(c_2548, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_2164, c_2535])).
% 4.90/1.84  tff(c_2147, plain, (![A_7]: (A_7='#skF_4' | ~r1_tarski(A_7, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2129, c_2129, c_10])).
% 4.90/1.84  tff(c_2586, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_2548, c_2147])).
% 4.90/1.84  tff(c_2165, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2148, c_50])).
% 4.90/1.84  tff(c_2547, plain, (r1_tarski('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_2165, c_2535])).
% 4.90/1.84  tff(c_2555, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_2547, c_2147])).
% 4.90/1.84  tff(c_2566, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2555, c_46])).
% 4.90/1.84  tff(c_2632, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2139, c_2586, c_2566])).
% 4.90/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.90/1.84  
% 4.90/1.84  Inference rules
% 4.90/1.84  ----------------------
% 4.90/1.84  #Ref     : 4
% 4.90/1.84  #Sup     : 535
% 4.90/1.84  #Fact    : 0
% 4.90/1.84  #Define  : 0
% 4.90/1.84  #Split   : 11
% 4.90/1.84  #Chain   : 0
% 4.90/1.84  #Close   : 0
% 4.90/1.84  
% 4.90/1.84  Ordering : KBO
% 4.90/1.84  
% 4.90/1.84  Simplification rules
% 4.90/1.84  ----------------------
% 4.90/1.84  #Subsume      : 66
% 4.90/1.85  #Demod        : 573
% 4.90/1.85  #Tautology    : 315
% 4.90/1.85  #SimpNegUnit  : 3
% 4.90/1.85  #BackRed      : 202
% 4.90/1.85  
% 4.90/1.85  #Partial instantiations: 0
% 4.90/1.85  #Strategies tried      : 1
% 4.90/1.85  
% 4.90/1.85  Timing (in seconds)
% 4.90/1.85  ----------------------
% 4.90/1.85  Preprocessing        : 0.32
% 4.90/1.85  Parsing              : 0.17
% 4.90/1.85  CNF conversion       : 0.02
% 4.90/1.85  Main loop            : 0.74
% 4.90/1.85  Inferencing          : 0.27
% 4.90/1.85  Reduction            : 0.24
% 4.90/1.85  Demodulation         : 0.16
% 4.90/1.85  BG Simplification    : 0.03
% 4.90/1.85  Subsumption          : 0.15
% 4.90/1.85  Abstraction          : 0.03
% 4.90/1.85  MUC search           : 0.00
% 4.90/1.85  Cooper               : 0.00
% 4.90/1.85  Total                : 1.11
% 4.90/1.85  Index Insertion      : 0.00
% 4.90/1.85  Index Deletion       : 0.00
% 4.90/1.85  Index Matching       : 0.00
% 4.90/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
