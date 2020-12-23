%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:34 EST 2020

% Result     : Theorem 7.73s
% Output     : CNFRefutation 7.86s
% Verified   : 
% Statistics : Number of formulae       :  145 (1038 expanded)
%              Number of leaves         :   40 ( 361 expanded)
%              Depth                    :   11
%              Number of atoms          :  238 (2822 expanded)
%              Number of equality atoms :   82 ( 500 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_4

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
    '#skF_3': $i > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_144,negated_conjecture,(
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

tff(f_105,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_123,axiom,(
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

tff(f_85,axiom,(
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

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_54,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(c_64,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_546,plain,(
    ! [A_117,B_118,C_119,D_120] :
      ( r2_relset_1(A_117,B_118,C_119,C_119)
      | ~ m1_subset_1(D_120,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118)))
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_649,plain,(
    ! [C_134] :
      ( r2_relset_1('#skF_5','#skF_6',C_134,C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_64,c_546])).

tff(c_662,plain,(
    r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_64,c_649])).

tff(c_70,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_251,plain,(
    ! [C_75,A_76,B_77] :
      ( v1_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_271,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_251])).

tff(c_74,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_72,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_476,plain,(
    ! [A_111,B_112,C_113] :
      ( k1_relset_1(A_111,B_112,C_113) = k1_relat_1(C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_498,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_70,c_476])).

tff(c_1114,plain,(
    ! [B_161,A_162,C_163] :
      ( k1_xboole_0 = B_161
      | k1_relset_1(A_162,B_161,C_163) = A_162
      | ~ v1_funct_2(C_163,A_162,B_161)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(A_162,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1121,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_1114])).

tff(c_1138,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_498,c_1121])).

tff(c_1144,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1138])).

tff(c_272,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_64,c_251])).

tff(c_68,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_66,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_499,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_64,c_476])).

tff(c_1124,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_1114])).

tff(c_1141,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_499,c_1124])).

tff(c_1169,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1141])).

tff(c_1244,plain,(
    ! [A_167,B_168] :
      ( r2_hidden('#skF_4'(A_167,B_168),k1_relat_1(A_167))
      | B_168 = A_167
      | k1_relat_1(B_168) != k1_relat_1(A_167)
      | ~ v1_funct_1(B_168)
      | ~ v1_relat_1(B_168)
      | ~ v1_funct_1(A_167)
      | ~ v1_relat_1(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1252,plain,(
    ! [B_168] :
      ( r2_hidden('#skF_4'('#skF_8',B_168),'#skF_5')
      | B_168 = '#skF_8'
      | k1_relat_1(B_168) != k1_relat_1('#skF_8')
      | ~ v1_funct_1(B_168)
      | ~ v1_relat_1(B_168)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1169,c_1244])).

tff(c_1680,plain,(
    ! [B_186] :
      ( r2_hidden('#skF_4'('#skF_8',B_186),'#skF_5')
      | B_186 = '#skF_8'
      | k1_relat_1(B_186) != '#skF_5'
      | ~ v1_funct_1(B_186)
      | ~ v1_relat_1(B_186) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_68,c_1169,c_1252])).

tff(c_62,plain,(
    ! [E_47] :
      ( k1_funct_1('#skF_7',E_47) = k1_funct_1('#skF_8',E_47)
      | ~ r2_hidden(E_47,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2052,plain,(
    ! [B_208] :
      ( k1_funct_1('#skF_7','#skF_4'('#skF_8',B_208)) = k1_funct_1('#skF_8','#skF_4'('#skF_8',B_208))
      | B_208 = '#skF_8'
      | k1_relat_1(B_208) != '#skF_5'
      | ~ v1_funct_1(B_208)
      | ~ v1_relat_1(B_208) ) ),
    inference(resolution,[status(thm)],[c_1680,c_62])).

tff(c_34,plain,(
    ! [B_25,A_21] :
      ( k1_funct_1(B_25,'#skF_4'(A_21,B_25)) != k1_funct_1(A_21,'#skF_4'(A_21,B_25))
      | B_25 = A_21
      | k1_relat_1(B_25) != k1_relat_1(A_21)
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2059,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | '#skF_7' = '#skF_8'
    | k1_relat_1('#skF_7') != '#skF_5'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2052,c_34])).

tff(c_2066,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_74,c_1144,c_272,c_68,c_1169,c_1144,c_2059])).

tff(c_60,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2083,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2066,c_60])).

tff(c_2095,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_662,c_2083])).

tff(c_2096,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1141])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2132,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2096,c_12])).

tff(c_22,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2131,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2096,c_2096,c_22])).

tff(c_115,plain,(
    ! [B_57,A_58] :
      ( v1_xboole_0(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58))
      | ~ v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_126,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_70,c_115])).

tff(c_130,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_2249,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2131,c_130])).

tff(c_2254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2132,c_2249])).

tff(c_2255,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1138])).

tff(c_2291,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2255,c_12])).

tff(c_2290,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2255,c_2255,c_22])).

tff(c_2367,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2290,c_130])).

tff(c_2372,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2291,c_2367])).

tff(c_2374,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_127,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_64,c_115])).

tff(c_2387,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2374,c_127])).

tff(c_110,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_2'(A_55,B_56),A_55)
      | r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_114,plain,(
    ! [A_55,B_56] :
      ( ~ v1_xboole_0(A_55)
      | r1_tarski(A_55,B_56) ) ),
    inference(resolution,[status(thm)],[c_110,c_2])).

tff(c_2389,plain,(
    ! [B_224,A_225] :
      ( B_224 = A_225
      | ~ r1_tarski(B_224,A_225)
      | ~ r1_tarski(A_225,B_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2399,plain,(
    ! [B_226,A_227] :
      ( B_226 = A_227
      | ~ r1_tarski(B_226,A_227)
      | ~ v1_xboole_0(A_227) ) ),
    inference(resolution,[status(thm)],[c_114,c_2389])).

tff(c_2409,plain,(
    ! [B_228,A_229] :
      ( B_228 = A_229
      | ~ v1_xboole_0(B_228)
      | ~ v1_xboole_0(A_229) ) ),
    inference(resolution,[status(thm)],[c_114,c_2399])).

tff(c_2443,plain,(
    ! [A_233] :
      ( k1_xboole_0 = A_233
      | ~ v1_xboole_0(A_233) ) ),
    inference(resolution,[status(thm)],[c_12,c_2409])).

tff(c_2460,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_2387,c_2443])).

tff(c_26,plain,(
    ! [A_14] : m1_subset_1('#skF_3'(A_14),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_128,plain,(
    ! [A_58] :
      ( v1_xboole_0('#skF_3'(k1_zfmisc_1(A_58)))
      | ~ v1_xboole_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_26,c_115])).

tff(c_2459,plain,(
    ! [A_58] :
      ( '#skF_3'(k1_zfmisc_1(A_58)) = k1_xboole_0
      | ~ v1_xboole_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_128,c_2443])).

tff(c_4164,plain,(
    ! [A_372] :
      ( '#skF_3'(k1_zfmisc_1(A_372)) = '#skF_8'
      | ~ v1_xboole_0(A_372) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2460,c_2459])).

tff(c_4179,plain,(
    ! [A_372] :
      ( m1_subset_1('#skF_8',k1_zfmisc_1(A_372))
      | ~ v1_xboole_0(A_372) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4164,c_26])).

tff(c_4007,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2460,c_2460,c_22])).

tff(c_4713,plain,(
    ! [A_429,B_430,C_431,D_432] :
      ( r2_relset_1(A_429,B_430,C_431,C_431)
      | ~ m1_subset_1(D_432,k1_zfmisc_1(k2_zfmisc_1(A_429,B_430)))
      | ~ m1_subset_1(C_431,k1_zfmisc_1(k2_zfmisc_1(A_429,B_430))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_5402,plain,(
    ! [A_470,B_471,C_472] :
      ( r2_relset_1(A_470,B_471,C_472,C_472)
      | ~ m1_subset_1(C_472,k1_zfmisc_1(k2_zfmisc_1(A_470,B_471))) ) ),
    inference(resolution,[status(thm)],[c_26,c_4713])).

tff(c_5484,plain,(
    ! [A_479,C_480] :
      ( r2_relset_1(A_479,'#skF_8',C_480,C_480)
      | ~ m1_subset_1(C_480,k1_zfmisc_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4007,c_5402])).

tff(c_5490,plain,(
    ! [A_479] :
      ( r2_relset_1(A_479,'#skF_8','#skF_8','#skF_8')
      | ~ v1_xboole_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_4179,c_5484])).

tff(c_5501,plain,(
    ! [A_479] : r2_relset_1(A_479,'#skF_8','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2387,c_5490])).

tff(c_4031,plain,(
    ! [A_359] :
      ( A_359 = '#skF_8'
      | ~ v1_xboole_0(A_359) ) ),
    inference(resolution,[status(thm)],[c_2387,c_2409])).

tff(c_4044,plain,(
    k2_zfmisc_1('#skF_5','#skF_6') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_2374,c_4031])).

tff(c_20,plain,(
    ! [B_13,A_12] :
      ( k1_xboole_0 = B_13
      | k1_xboole_0 = A_12
      | k2_zfmisc_1(A_12,B_13) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4108,plain,(
    ! [B_365,A_366] :
      ( B_365 = '#skF_8'
      | A_366 = '#skF_8'
      | k2_zfmisc_1(A_366,B_365) != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2460,c_2460,c_2460,c_20])).

tff(c_4120,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_5' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_4044,c_4108])).

tff(c_4123,plain,(
    '#skF_5' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_4120])).

tff(c_24,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2474,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_8',B_13) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2460,c_2460,c_24])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2375,plain,(
    ! [E_222] :
      ( k1_funct_1('#skF_7',E_222) = k1_funct_1('#skF_8',E_222)
      | ~ r2_hidden(E_222,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2385,plain,
    ( k1_funct_1('#skF_7','#skF_1'('#skF_5')) = k1_funct_1('#skF_8','#skF_1'('#skF_5'))
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_2375])).

tff(c_2465,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2385])).

tff(c_2424,plain,(
    ! [A_229] :
      ( k1_xboole_0 = A_229
      | ~ v1_xboole_0(A_229) ) ),
    inference(resolution,[status(thm)],[c_12,c_2409])).

tff(c_2471,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2465,c_2424])).

tff(c_2499,plain,(
    '#skF_5' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2460,c_2471])).

tff(c_2502,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2499,c_64])).

tff(c_2590,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2474,c_2502])).

tff(c_2869,plain,(
    ! [A_287,B_288,C_289,D_290] :
      ( r2_relset_1(A_287,B_288,C_289,C_289)
      | ~ m1_subset_1(D_290,k1_zfmisc_1(k2_zfmisc_1(A_287,B_288)))
      | ~ m1_subset_1(C_289,k1_zfmisc_1(k2_zfmisc_1(A_287,B_288))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3962,plain,(
    ! [A_354,B_355,C_356] :
      ( r2_relset_1(A_354,B_355,C_356,C_356)
      | ~ m1_subset_1(C_356,k1_zfmisc_1(k2_zfmisc_1(A_354,B_355))) ) ),
    inference(resolution,[status(thm)],[c_26,c_2869])).

tff(c_3979,plain,(
    ! [B_357,C_358] :
      ( r2_relset_1('#skF_8',B_357,C_358,C_358)
      | ~ m1_subset_1(C_358,k1_zfmisc_1('#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2474,c_3962])).

tff(c_3997,plain,(
    ! [B_357] : r2_relset_1('#skF_8',B_357,'#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_2590,c_3979])).

tff(c_2373,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_2462,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_2373,c_2443])).

tff(c_2482,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2460,c_2462])).

tff(c_2487,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2482,c_60])).

tff(c_2563,plain,(
    ~ r2_relset_1('#skF_8','#skF_6','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2499,c_2487])).

tff(c_4002,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3997,c_2563])).

tff(c_4004,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_2385])).

tff(c_4126,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4123,c_4004])).

tff(c_4131,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2387,c_4126])).

tff(c_4132,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_4120])).

tff(c_4014,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2460,c_2462])).

tff(c_4019,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4014,c_60])).

tff(c_4134,plain,(
    ~ r2_relset_1('#skF_5','#skF_8','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4132,c_4019])).

tff(c_5506,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5501,c_4134])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:46:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.73/3.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.86/3.09  
% 7.86/3.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.86/3.09  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_4
% 7.86/3.09  
% 7.86/3.09  %Foreground sorts:
% 7.86/3.09  
% 7.86/3.09  
% 7.86/3.09  %Background operators:
% 7.86/3.09  
% 7.86/3.09  
% 7.86/3.09  %Foreground operators:
% 7.86/3.09  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.86/3.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.86/3.09  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.86/3.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.86/3.09  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.86/3.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.86/3.09  tff('#skF_7', type, '#skF_7': $i).
% 7.86/3.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.86/3.09  tff('#skF_5', type, '#skF_5': $i).
% 7.86/3.09  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.86/3.09  tff('#skF_6', type, '#skF_6': $i).
% 7.86/3.09  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.86/3.09  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.86/3.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.86/3.09  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.86/3.09  tff('#skF_8', type, '#skF_8': $i).
% 7.86/3.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.86/3.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.86/3.09  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.86/3.09  tff('#skF_3', type, '#skF_3': $i > $i).
% 7.86/3.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.86/3.09  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.86/3.09  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.86/3.09  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.86/3.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.86/3.09  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.86/3.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.86/3.09  
% 7.86/3.13  tff(f_144, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_2)).
% 7.86/3.13  tff(f_105, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 7.86/3.13  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.86/3.13  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.86/3.13  tff(f_123, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 7.86/3.13  tff(f_85, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 7.86/3.13  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.86/3.13  tff(f_51, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.86/3.13  tff(f_61, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 7.86/3.13  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.86/3.13  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.86/3.13  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.86/3.13  tff(f_54, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 7.86/3.13  tff(c_64, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.86/3.13  tff(c_546, plain, (![A_117, B_118, C_119, D_120]: (r2_relset_1(A_117, B_118, C_119, C_119) | ~m1_subset_1(D_120, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.86/3.13  tff(c_649, plain, (![C_134]: (r2_relset_1('#skF_5', '#skF_6', C_134, C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(resolution, [status(thm)], [c_64, c_546])).
% 7.86/3.13  tff(c_662, plain, (r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_64, c_649])).
% 7.86/3.13  tff(c_70, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.86/3.13  tff(c_251, plain, (![C_75, A_76, B_77]: (v1_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.86/3.13  tff(c_271, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_70, c_251])).
% 7.86/3.13  tff(c_74, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.86/3.13  tff(c_72, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.86/3.13  tff(c_476, plain, (![A_111, B_112, C_113]: (k1_relset_1(A_111, B_112, C_113)=k1_relat_1(C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.86/3.13  tff(c_498, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_70, c_476])).
% 7.86/3.13  tff(c_1114, plain, (![B_161, A_162, C_163]: (k1_xboole_0=B_161 | k1_relset_1(A_162, B_161, C_163)=A_162 | ~v1_funct_2(C_163, A_162, B_161) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(A_162, B_161))))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.86/3.13  tff(c_1121, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_5' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_70, c_1114])).
% 7.86/3.13  tff(c_1138, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_498, c_1121])).
% 7.86/3.13  tff(c_1144, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitLeft, [status(thm)], [c_1138])).
% 7.86/3.13  tff(c_272, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_64, c_251])).
% 7.86/3.13  tff(c_68, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.86/3.13  tff(c_66, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.86/3.13  tff(c_499, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_64, c_476])).
% 7.86/3.13  tff(c_1124, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_64, c_1114])).
% 7.86/3.13  tff(c_1141, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_499, c_1124])).
% 7.86/3.13  tff(c_1169, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_1141])).
% 7.86/3.13  tff(c_1244, plain, (![A_167, B_168]: (r2_hidden('#skF_4'(A_167, B_168), k1_relat_1(A_167)) | B_168=A_167 | k1_relat_1(B_168)!=k1_relat_1(A_167) | ~v1_funct_1(B_168) | ~v1_relat_1(B_168) | ~v1_funct_1(A_167) | ~v1_relat_1(A_167))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.86/3.13  tff(c_1252, plain, (![B_168]: (r2_hidden('#skF_4'('#skF_8', B_168), '#skF_5') | B_168='#skF_8' | k1_relat_1(B_168)!=k1_relat_1('#skF_8') | ~v1_funct_1(B_168) | ~v1_relat_1(B_168) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1169, c_1244])).
% 7.86/3.13  tff(c_1680, plain, (![B_186]: (r2_hidden('#skF_4'('#skF_8', B_186), '#skF_5') | B_186='#skF_8' | k1_relat_1(B_186)!='#skF_5' | ~v1_funct_1(B_186) | ~v1_relat_1(B_186))), inference(demodulation, [status(thm), theory('equality')], [c_272, c_68, c_1169, c_1252])).
% 7.86/3.13  tff(c_62, plain, (![E_47]: (k1_funct_1('#skF_7', E_47)=k1_funct_1('#skF_8', E_47) | ~r2_hidden(E_47, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.86/3.13  tff(c_2052, plain, (![B_208]: (k1_funct_1('#skF_7', '#skF_4'('#skF_8', B_208))=k1_funct_1('#skF_8', '#skF_4'('#skF_8', B_208)) | B_208='#skF_8' | k1_relat_1(B_208)!='#skF_5' | ~v1_funct_1(B_208) | ~v1_relat_1(B_208))), inference(resolution, [status(thm)], [c_1680, c_62])).
% 7.86/3.13  tff(c_34, plain, (![B_25, A_21]: (k1_funct_1(B_25, '#skF_4'(A_21, B_25))!=k1_funct_1(A_21, '#skF_4'(A_21, B_25)) | B_25=A_21 | k1_relat_1(B_25)!=k1_relat_1(A_21) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.86/3.13  tff(c_2059, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | '#skF_7'='#skF_8' | k1_relat_1('#skF_7')!='#skF_5' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2052, c_34])).
% 7.86/3.13  tff(c_2066, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_271, c_74, c_1144, c_272, c_68, c_1169, c_1144, c_2059])).
% 7.86/3.13  tff(c_60, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.86/3.13  tff(c_2083, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2066, c_60])).
% 7.86/3.13  tff(c_2095, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_662, c_2083])).
% 7.86/3.13  tff(c_2096, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_1141])).
% 7.86/3.13  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.86/3.13  tff(c_2132, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2096, c_12])).
% 7.86/3.13  tff(c_22, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.86/3.13  tff(c_2131, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2096, c_2096, c_22])).
% 7.86/3.13  tff(c_115, plain, (![B_57, A_58]: (v1_xboole_0(B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)) | ~v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.86/3.13  tff(c_126, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_70, c_115])).
% 7.86/3.13  tff(c_130, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_126])).
% 7.86/3.13  tff(c_2249, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2131, c_130])).
% 7.86/3.13  tff(c_2254, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2132, c_2249])).
% 7.86/3.13  tff(c_2255, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_1138])).
% 7.86/3.13  tff(c_2291, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2255, c_12])).
% 7.86/3.13  tff(c_2290, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2255, c_2255, c_22])).
% 7.86/3.13  tff(c_2367, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2290, c_130])).
% 7.86/3.13  tff(c_2372, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2291, c_2367])).
% 7.86/3.13  tff(c_2374, plain, (v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_126])).
% 7.86/3.13  tff(c_127, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_64, c_115])).
% 7.86/3.13  tff(c_2387, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2374, c_127])).
% 7.86/3.13  tff(c_110, plain, (![A_55, B_56]: (r2_hidden('#skF_2'(A_55, B_56), A_55) | r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.86/3.13  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.86/3.13  tff(c_114, plain, (![A_55, B_56]: (~v1_xboole_0(A_55) | r1_tarski(A_55, B_56))), inference(resolution, [status(thm)], [c_110, c_2])).
% 7.86/3.13  tff(c_2389, plain, (![B_224, A_225]: (B_224=A_225 | ~r1_tarski(B_224, A_225) | ~r1_tarski(A_225, B_224))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.86/3.13  tff(c_2399, plain, (![B_226, A_227]: (B_226=A_227 | ~r1_tarski(B_226, A_227) | ~v1_xboole_0(A_227))), inference(resolution, [status(thm)], [c_114, c_2389])).
% 7.86/3.13  tff(c_2409, plain, (![B_228, A_229]: (B_228=A_229 | ~v1_xboole_0(B_228) | ~v1_xboole_0(A_229))), inference(resolution, [status(thm)], [c_114, c_2399])).
% 7.86/3.13  tff(c_2443, plain, (![A_233]: (k1_xboole_0=A_233 | ~v1_xboole_0(A_233))), inference(resolution, [status(thm)], [c_12, c_2409])).
% 7.86/3.13  tff(c_2460, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_2387, c_2443])).
% 7.86/3.13  tff(c_26, plain, (![A_14]: (m1_subset_1('#skF_3'(A_14), A_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.86/3.13  tff(c_128, plain, (![A_58]: (v1_xboole_0('#skF_3'(k1_zfmisc_1(A_58))) | ~v1_xboole_0(A_58))), inference(resolution, [status(thm)], [c_26, c_115])).
% 7.86/3.13  tff(c_2459, plain, (![A_58]: ('#skF_3'(k1_zfmisc_1(A_58))=k1_xboole_0 | ~v1_xboole_0(A_58))), inference(resolution, [status(thm)], [c_128, c_2443])).
% 7.86/3.13  tff(c_4164, plain, (![A_372]: ('#skF_3'(k1_zfmisc_1(A_372))='#skF_8' | ~v1_xboole_0(A_372))), inference(demodulation, [status(thm), theory('equality')], [c_2460, c_2459])).
% 7.86/3.13  tff(c_4179, plain, (![A_372]: (m1_subset_1('#skF_8', k1_zfmisc_1(A_372)) | ~v1_xboole_0(A_372))), inference(superposition, [status(thm), theory('equality')], [c_4164, c_26])).
% 7.86/3.13  tff(c_4007, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2460, c_2460, c_22])).
% 7.86/3.13  tff(c_4713, plain, (![A_429, B_430, C_431, D_432]: (r2_relset_1(A_429, B_430, C_431, C_431) | ~m1_subset_1(D_432, k1_zfmisc_1(k2_zfmisc_1(A_429, B_430))) | ~m1_subset_1(C_431, k1_zfmisc_1(k2_zfmisc_1(A_429, B_430))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.86/3.13  tff(c_5402, plain, (![A_470, B_471, C_472]: (r2_relset_1(A_470, B_471, C_472, C_472) | ~m1_subset_1(C_472, k1_zfmisc_1(k2_zfmisc_1(A_470, B_471))))), inference(resolution, [status(thm)], [c_26, c_4713])).
% 7.86/3.13  tff(c_5484, plain, (![A_479, C_480]: (r2_relset_1(A_479, '#skF_8', C_480, C_480) | ~m1_subset_1(C_480, k1_zfmisc_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_4007, c_5402])).
% 7.86/3.13  tff(c_5490, plain, (![A_479]: (r2_relset_1(A_479, '#skF_8', '#skF_8', '#skF_8') | ~v1_xboole_0('#skF_8'))), inference(resolution, [status(thm)], [c_4179, c_5484])).
% 7.86/3.13  tff(c_5501, plain, (![A_479]: (r2_relset_1(A_479, '#skF_8', '#skF_8', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2387, c_5490])).
% 7.86/3.13  tff(c_4031, plain, (![A_359]: (A_359='#skF_8' | ~v1_xboole_0(A_359))), inference(resolution, [status(thm)], [c_2387, c_2409])).
% 7.86/3.13  tff(c_4044, plain, (k2_zfmisc_1('#skF_5', '#skF_6')='#skF_8'), inference(resolution, [status(thm)], [c_2374, c_4031])).
% 7.86/3.13  tff(c_20, plain, (![B_13, A_12]: (k1_xboole_0=B_13 | k1_xboole_0=A_12 | k2_zfmisc_1(A_12, B_13)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.86/3.13  tff(c_4108, plain, (![B_365, A_366]: (B_365='#skF_8' | A_366='#skF_8' | k2_zfmisc_1(A_366, B_365)!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2460, c_2460, c_2460, c_20])).
% 7.86/3.13  tff(c_4120, plain, ('#skF_6'='#skF_8' | '#skF_5'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_4044, c_4108])).
% 7.86/3.13  tff(c_4123, plain, ('#skF_5'='#skF_8'), inference(splitLeft, [status(thm)], [c_4120])).
% 7.86/3.13  tff(c_24, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.86/3.13  tff(c_2474, plain, (![B_13]: (k2_zfmisc_1('#skF_8', B_13)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2460, c_2460, c_24])).
% 7.86/3.13  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.86/3.13  tff(c_2375, plain, (![E_222]: (k1_funct_1('#skF_7', E_222)=k1_funct_1('#skF_8', E_222) | ~r2_hidden(E_222, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 7.86/3.13  tff(c_2385, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_5'))=k1_funct_1('#skF_8', '#skF_1'('#skF_5')) | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_2375])).
% 7.86/3.13  tff(c_2465, plain, (v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_2385])).
% 7.86/3.13  tff(c_2424, plain, (![A_229]: (k1_xboole_0=A_229 | ~v1_xboole_0(A_229))), inference(resolution, [status(thm)], [c_12, c_2409])).
% 7.86/3.13  tff(c_2471, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_2465, c_2424])).
% 7.86/3.13  tff(c_2499, plain, ('#skF_5'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2460, c_2471])).
% 7.86/3.13  tff(c_2502, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_2499, c_64])).
% 7.86/3.13  tff(c_2590, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_2474, c_2502])).
% 7.86/3.13  tff(c_2869, plain, (![A_287, B_288, C_289, D_290]: (r2_relset_1(A_287, B_288, C_289, C_289) | ~m1_subset_1(D_290, k1_zfmisc_1(k2_zfmisc_1(A_287, B_288))) | ~m1_subset_1(C_289, k1_zfmisc_1(k2_zfmisc_1(A_287, B_288))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.86/3.13  tff(c_3962, plain, (![A_354, B_355, C_356]: (r2_relset_1(A_354, B_355, C_356, C_356) | ~m1_subset_1(C_356, k1_zfmisc_1(k2_zfmisc_1(A_354, B_355))))), inference(resolution, [status(thm)], [c_26, c_2869])).
% 7.86/3.13  tff(c_3979, plain, (![B_357, C_358]: (r2_relset_1('#skF_8', B_357, C_358, C_358) | ~m1_subset_1(C_358, k1_zfmisc_1('#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_2474, c_3962])).
% 7.86/3.13  tff(c_3997, plain, (![B_357]: (r2_relset_1('#skF_8', B_357, '#skF_8', '#skF_8'))), inference(resolution, [status(thm)], [c_2590, c_3979])).
% 7.86/3.13  tff(c_2373, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_126])).
% 7.86/3.13  tff(c_2462, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_2373, c_2443])).
% 7.86/3.13  tff(c_2482, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2460, c_2462])).
% 7.86/3.13  tff(c_2487, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2482, c_60])).
% 7.86/3.13  tff(c_2563, plain, (~r2_relset_1('#skF_8', '#skF_6', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2499, c_2487])).
% 7.86/3.13  tff(c_4002, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3997, c_2563])).
% 7.86/3.13  tff(c_4004, plain, (~v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_2385])).
% 7.86/3.13  tff(c_4126, plain, (~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4123, c_4004])).
% 7.86/3.13  tff(c_4131, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2387, c_4126])).
% 7.86/3.13  tff(c_4132, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_4120])).
% 7.86/3.13  tff(c_4014, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2460, c_2462])).
% 7.86/3.13  tff(c_4019, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4014, c_60])).
% 7.86/3.13  tff(c_4134, plain, (~r2_relset_1('#skF_5', '#skF_8', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4132, c_4019])).
% 7.86/3.13  tff(c_5506, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5501, c_4134])).
% 7.86/3.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.86/3.13  
% 7.86/3.13  Inference rules
% 7.86/3.13  ----------------------
% 7.86/3.13  #Ref     : 3
% 7.86/3.13  #Sup     : 1165
% 7.86/3.13  #Fact    : 0
% 7.86/3.13  #Define  : 0
% 7.86/3.13  #Split   : 9
% 7.86/3.13  #Chain   : 0
% 7.86/3.13  #Close   : 0
% 7.86/3.13  
% 7.86/3.13  Ordering : KBO
% 7.86/3.13  
% 7.86/3.13  Simplification rules
% 7.86/3.13  ----------------------
% 7.86/3.13  #Subsume      : 299
% 7.86/3.13  #Demod        : 1070
% 7.86/3.13  #Tautology    : 554
% 7.86/3.13  #SimpNegUnit  : 11
% 7.86/3.13  #BackRed      : 157
% 7.86/3.13  
% 7.86/3.13  #Partial instantiations: 0
% 7.86/3.13  #Strategies tried      : 1
% 7.86/3.13  
% 7.86/3.13  Timing (in seconds)
% 7.86/3.13  ----------------------
% 7.86/3.14  Preprocessing        : 0.54
% 7.86/3.14  Parsing              : 0.27
% 7.86/3.14  CNF conversion       : 0.04
% 7.86/3.14  Main loop            : 1.64
% 7.86/3.14  Inferencing          : 0.56
% 7.86/3.14  Reduction            : 0.58
% 7.86/3.14  Demodulation         : 0.42
% 7.86/3.14  BG Simplification    : 0.06
% 7.86/3.14  Subsumption          : 0.29
% 7.86/3.14  Abstraction          : 0.07
% 7.86/3.14  MUC search           : 0.00
% 7.86/3.14  Cooper               : 0.00
% 7.86/3.14  Total                : 2.26
% 7.86/3.14  Index Insertion      : 0.00
% 7.86/3.14  Index Deletion       : 0.00
% 7.86/3.14  Index Matching       : 0.00
% 7.86/3.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
