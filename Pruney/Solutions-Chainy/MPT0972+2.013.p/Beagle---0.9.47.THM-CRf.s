%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:36 EST 2020

% Result     : Theorem 5.12s
% Output     : CNFRefutation 5.48s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 560 expanded)
%              Number of leaves         :   36 ( 202 expanded)
%              Depth                    :   12
%              Number of atoms          :  177 (1520 expanded)
%              Number of equality atoms :   58 ( 281 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_4

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_141,negated_conjecture,(
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

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_120,axiom,(
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

tff(f_79,axiom,(
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

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

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

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_56,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_152,plain,(
    ! [C_72,B_73,A_74] :
      ( v1_xboole_0(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(B_73,A_74)))
      | ~ v1_xboole_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_164,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_152])).

tff(c_166,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_164])).

tff(c_1543,plain,(
    ! [A_244,B_245,D_246] :
      ( r2_relset_1(A_244,B_245,D_246,D_246)
      | ~ m1_subset_1(D_246,k1_zfmisc_1(k2_zfmisc_1(A_244,B_245))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1552,plain,(
    r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_56,c_1543])).

tff(c_62,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_77,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_90,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_77])).

tff(c_66,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_64,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1742,plain,(
    ! [A_276,B_277,C_278] :
      ( k1_relset_1(A_276,B_277,C_278) = k1_relat_1(C_278)
      | ~ m1_subset_1(C_278,k1_zfmisc_1(k2_zfmisc_1(A_276,B_277))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1761,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_62,c_1742])).

tff(c_2118,plain,(
    ! [B_324,A_325,C_326] :
      ( k1_xboole_0 = B_324
      | k1_relset_1(A_325,B_324,C_326) = A_325
      | ~ v1_funct_2(C_326,A_325,B_324)
      | ~ m1_subset_1(C_326,k1_zfmisc_1(k2_zfmisc_1(A_325,B_324))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2134,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_2118])).

tff(c_2142,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1761,c_2134])).

tff(c_2149,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_2142])).

tff(c_89,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_56,c_77])).

tff(c_60,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_58,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1760,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_56,c_1742])).

tff(c_2131,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_2118])).

tff(c_2139,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1760,c_2131])).

tff(c_2143,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_2139])).

tff(c_2535,plain,(
    ! [A_368,B_369] :
      ( r2_hidden('#skF_4'(A_368,B_369),k1_relat_1(A_368))
      | B_369 = A_368
      | k1_relat_1(B_369) != k1_relat_1(A_368)
      | ~ v1_funct_1(B_369)
      | ~ v1_relat_1(B_369)
      | ~ v1_funct_1(A_368)
      | ~ v1_relat_1(A_368) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2548,plain,(
    ! [B_369] :
      ( r2_hidden('#skF_4'('#skF_8',B_369),'#skF_5')
      | B_369 = '#skF_8'
      | k1_relat_1(B_369) != k1_relat_1('#skF_8')
      | ~ v1_funct_1(B_369)
      | ~ v1_relat_1(B_369)
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2143,c_2535])).

tff(c_2571,plain,(
    ! [B_371] :
      ( r2_hidden('#skF_4'('#skF_8',B_371),'#skF_5')
      | B_371 = '#skF_8'
      | k1_relat_1(B_371) != '#skF_5'
      | ~ v1_funct_1(B_371)
      | ~ v1_relat_1(B_371) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_60,c_2143,c_2548])).

tff(c_54,plain,(
    ! [E_45] :
      ( k1_funct_1('#skF_7',E_45) = k1_funct_1('#skF_8',E_45)
      | ~ r2_hidden(E_45,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_3000,plain,(
    ! [B_401] :
      ( k1_funct_1('#skF_7','#skF_4'('#skF_8',B_401)) = k1_funct_1('#skF_8','#skF_4'('#skF_8',B_401))
      | B_401 = '#skF_8'
      | k1_relat_1(B_401) != '#skF_5'
      | ~ v1_funct_1(B_401)
      | ~ v1_relat_1(B_401) ) ),
    inference(resolution,[status(thm)],[c_2571,c_54])).

tff(c_26,plain,(
    ! [B_22,A_18] :
      ( k1_funct_1(B_22,'#skF_4'(A_18,B_22)) != k1_funct_1(A_18,'#skF_4'(A_18,B_22))
      | B_22 = A_18
      | k1_relat_1(B_22) != k1_relat_1(A_18)
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_3007,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | '#skF_7' = '#skF_8'
    | k1_relat_1('#skF_7') != '#skF_5'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_3000,c_26])).

tff(c_3014,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_66,c_2149,c_89,c_60,c_2143,c_2149,c_3007])).

tff(c_52,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_3042,plain,(
    ~ r2_relset_1('#skF_5','#skF_6','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3014,c_52])).

tff(c_3053,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1552,c_3042])).

tff(c_3054,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2142])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3070,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3054,c_12])).

tff(c_3072,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_3070])).

tff(c_3073,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2139])).

tff(c_3089,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3073,c_12])).

tff(c_3091,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_3089])).

tff(c_3092,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_91,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_2'(A_55,B_56),A_55)
      | r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_95,plain,(
    ! [A_55,B_56] :
      ( ~ v1_xboole_0(A_55)
      | r1_tarski(A_55,B_56) ) ),
    inference(resolution,[status(thm)],[c_91,c_2])).

tff(c_97,plain,(
    ! [B_59,A_60] :
      ( B_59 = A_60
      | ~ r1_tarski(B_59,A_60)
      | ~ r1_tarski(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_118,plain,(
    ! [B_62,A_63] :
      ( B_62 = A_63
      | ~ r1_tarski(B_62,A_63)
      | ~ v1_xboole_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_95,c_97])).

tff(c_128,plain,(
    ! [B_64,A_65] :
      ( B_64 = A_65
      | ~ v1_xboole_0(B_64)
      | ~ v1_xboole_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_95,c_118])).

tff(c_131,plain,(
    ! [A_65] :
      ( k1_xboole_0 = A_65
      | ~ v1_xboole_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_12,c_128])).

tff(c_3099,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_3092,c_131])).

tff(c_3093,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_3106,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_3093,c_131])).

tff(c_3122,plain,(
    '#skF_6' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3099,c_3106])).

tff(c_165,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_152])).

tff(c_3135,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3092,c_3122,c_165])).

tff(c_125,plain,(
    ! [B_56,A_55] :
      ( B_56 = A_55
      | ~ v1_xboole_0(B_56)
      | ~ v1_xboole_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_95,c_118])).

tff(c_3107,plain,(
    ! [A_55] :
      ( A_55 = '#skF_6'
      | ~ v1_xboole_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_3093,c_125])).

tff(c_3140,plain,(
    ! [A_405] :
      ( A_405 = '#skF_8'
      | ~ v1_xboole_0(A_405) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3122,c_3107])).

tff(c_3147,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_3135,c_3140])).

tff(c_3126,plain,(
    ~ r2_relset_1('#skF_5','#skF_8','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3122,c_52])).

tff(c_3168,plain,(
    ~ r2_relset_1('#skF_5','#skF_8','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3147,c_3126])).

tff(c_3125,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3122,c_62])).

tff(c_3169,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3147,c_3125])).

tff(c_36,plain,(
    ! [A_34,B_35,D_37] :
      ( r2_relset_1(A_34,B_35,D_37,D_37)
      | ~ m1_subset_1(D_37,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_3171,plain,(
    r2_relset_1('#skF_5','#skF_8','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_3169,c_36])).

tff(c_3181,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3168,c_3171])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:33:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.12/1.97  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.12/1.98  
% 5.12/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.12/1.98  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_4
% 5.12/1.98  
% 5.12/1.98  %Foreground sorts:
% 5.12/1.98  
% 5.12/1.98  
% 5.12/1.98  %Background operators:
% 5.12/1.98  
% 5.12/1.98  
% 5.12/1.98  %Foreground operators:
% 5.12/1.98  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.12/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.12/1.98  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.12/1.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.12/1.98  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.12/1.98  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.12/1.98  tff('#skF_7', type, '#skF_7': $i).
% 5.12/1.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.12/1.98  tff('#skF_5', type, '#skF_5': $i).
% 5.12/1.98  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.12/1.98  tff('#skF_6', type, '#skF_6': $i).
% 5.12/1.98  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.12/1.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.12/1.98  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.12/1.98  tff('#skF_8', type, '#skF_8': $i).
% 5.12/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.12/1.98  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.12/1.98  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.12/1.98  tff('#skF_3', type, '#skF_3': $i > $i).
% 5.12/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.12/1.98  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.12/1.98  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.12/1.98  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.12/1.98  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.12/1.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.12/1.98  
% 5.48/2.00  tff(f_141, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 5.48/2.00  tff(f_90, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 5.48/2.00  tff(f_102, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.48/2.00  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.48/2.00  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.48/2.00  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.48/2.00  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 5.48/2.00  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.48/2.00  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.48/2.00  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.48/2.00  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.48/2.00  tff(c_56, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.48/2.00  tff(c_152, plain, (![C_72, B_73, A_74]: (v1_xboole_0(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(B_73, A_74))) | ~v1_xboole_0(A_74))), inference(cnfTransformation, [status(thm)], [f_90])).
% 5.48/2.00  tff(c_164, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_56, c_152])).
% 5.48/2.00  tff(c_166, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_164])).
% 5.48/2.00  tff(c_1543, plain, (![A_244, B_245, D_246]: (r2_relset_1(A_244, B_245, D_246, D_246) | ~m1_subset_1(D_246, k1_zfmisc_1(k2_zfmisc_1(A_244, B_245))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.48/2.00  tff(c_1552, plain, (r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_56, c_1543])).
% 5.48/2.00  tff(c_62, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.48/2.00  tff(c_77, plain, (![C_52, A_53, B_54]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.48/2.00  tff(c_90, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_62, c_77])).
% 5.48/2.00  tff(c_66, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.48/2.00  tff(c_64, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.48/2.00  tff(c_1742, plain, (![A_276, B_277, C_278]: (k1_relset_1(A_276, B_277, C_278)=k1_relat_1(C_278) | ~m1_subset_1(C_278, k1_zfmisc_1(k2_zfmisc_1(A_276, B_277))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.48/2.00  tff(c_1761, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_62, c_1742])).
% 5.48/2.00  tff(c_2118, plain, (![B_324, A_325, C_326]: (k1_xboole_0=B_324 | k1_relset_1(A_325, B_324, C_326)=A_325 | ~v1_funct_2(C_326, A_325, B_324) | ~m1_subset_1(C_326, k1_zfmisc_1(k2_zfmisc_1(A_325, B_324))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.48/2.00  tff(c_2134, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_5' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_62, c_2118])).
% 5.48/2.00  tff(c_2142, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1761, c_2134])).
% 5.48/2.00  tff(c_2149, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitLeft, [status(thm)], [c_2142])).
% 5.48/2.00  tff(c_89, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_56, c_77])).
% 5.48/2.00  tff(c_60, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.48/2.00  tff(c_58, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.48/2.00  tff(c_1760, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_56, c_1742])).
% 5.48/2.00  tff(c_2131, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_56, c_2118])).
% 5.48/2.00  tff(c_2139, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1760, c_2131])).
% 5.48/2.00  tff(c_2143, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_2139])).
% 5.48/2.00  tff(c_2535, plain, (![A_368, B_369]: (r2_hidden('#skF_4'(A_368, B_369), k1_relat_1(A_368)) | B_369=A_368 | k1_relat_1(B_369)!=k1_relat_1(A_368) | ~v1_funct_1(B_369) | ~v1_relat_1(B_369) | ~v1_funct_1(A_368) | ~v1_relat_1(A_368))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.48/2.00  tff(c_2548, plain, (![B_369]: (r2_hidden('#skF_4'('#skF_8', B_369), '#skF_5') | B_369='#skF_8' | k1_relat_1(B_369)!=k1_relat_1('#skF_8') | ~v1_funct_1(B_369) | ~v1_relat_1(B_369) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2143, c_2535])).
% 5.48/2.00  tff(c_2571, plain, (![B_371]: (r2_hidden('#skF_4'('#skF_8', B_371), '#skF_5') | B_371='#skF_8' | k1_relat_1(B_371)!='#skF_5' | ~v1_funct_1(B_371) | ~v1_relat_1(B_371))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_60, c_2143, c_2548])).
% 5.48/2.00  tff(c_54, plain, (![E_45]: (k1_funct_1('#skF_7', E_45)=k1_funct_1('#skF_8', E_45) | ~r2_hidden(E_45, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.48/2.00  tff(c_3000, plain, (![B_401]: (k1_funct_1('#skF_7', '#skF_4'('#skF_8', B_401))=k1_funct_1('#skF_8', '#skF_4'('#skF_8', B_401)) | B_401='#skF_8' | k1_relat_1(B_401)!='#skF_5' | ~v1_funct_1(B_401) | ~v1_relat_1(B_401))), inference(resolution, [status(thm)], [c_2571, c_54])).
% 5.48/2.00  tff(c_26, plain, (![B_22, A_18]: (k1_funct_1(B_22, '#skF_4'(A_18, B_22))!=k1_funct_1(A_18, '#skF_4'(A_18, B_22)) | B_22=A_18 | k1_relat_1(B_22)!=k1_relat_1(A_18) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.48/2.00  tff(c_3007, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | '#skF_7'='#skF_8' | k1_relat_1('#skF_7')!='#skF_5' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_3000, c_26])).
% 5.48/2.00  tff(c_3014, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_66, c_2149, c_89, c_60, c_2143, c_2149, c_3007])).
% 5.48/2.00  tff(c_52, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.48/2.00  tff(c_3042, plain, (~r2_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3014, c_52])).
% 5.48/2.00  tff(c_3053, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1552, c_3042])).
% 5.48/2.00  tff(c_3054, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_2142])).
% 5.48/2.00  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.48/2.00  tff(c_3070, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3054, c_12])).
% 5.48/2.00  tff(c_3072, plain, $false, inference(negUnitSimplification, [status(thm)], [c_166, c_3070])).
% 5.48/2.00  tff(c_3073, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_2139])).
% 5.48/2.00  tff(c_3089, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_3073, c_12])).
% 5.48/2.00  tff(c_3091, plain, $false, inference(negUnitSimplification, [status(thm)], [c_166, c_3089])).
% 5.48/2.00  tff(c_3092, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_164])).
% 5.48/2.00  tff(c_91, plain, (![A_55, B_56]: (r2_hidden('#skF_2'(A_55, B_56), A_55) | r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.48/2.00  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.48/2.00  tff(c_95, plain, (![A_55, B_56]: (~v1_xboole_0(A_55) | r1_tarski(A_55, B_56))), inference(resolution, [status(thm)], [c_91, c_2])).
% 5.48/2.00  tff(c_97, plain, (![B_59, A_60]: (B_59=A_60 | ~r1_tarski(B_59, A_60) | ~r1_tarski(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.48/2.00  tff(c_118, plain, (![B_62, A_63]: (B_62=A_63 | ~r1_tarski(B_62, A_63) | ~v1_xboole_0(A_63))), inference(resolution, [status(thm)], [c_95, c_97])).
% 5.48/2.00  tff(c_128, plain, (![B_64, A_65]: (B_64=A_65 | ~v1_xboole_0(B_64) | ~v1_xboole_0(A_65))), inference(resolution, [status(thm)], [c_95, c_118])).
% 5.48/2.00  tff(c_131, plain, (![A_65]: (k1_xboole_0=A_65 | ~v1_xboole_0(A_65))), inference(resolution, [status(thm)], [c_12, c_128])).
% 5.48/2.00  tff(c_3099, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_3092, c_131])).
% 5.48/2.00  tff(c_3093, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_164])).
% 5.48/2.00  tff(c_3106, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_3093, c_131])).
% 5.48/2.00  tff(c_3122, plain, ('#skF_6'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_3099, c_3106])).
% 5.48/2.00  tff(c_165, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_62, c_152])).
% 5.48/2.00  tff(c_3135, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_3092, c_3122, c_165])).
% 5.48/2.00  tff(c_125, plain, (![B_56, A_55]: (B_56=A_55 | ~v1_xboole_0(B_56) | ~v1_xboole_0(A_55))), inference(resolution, [status(thm)], [c_95, c_118])).
% 5.48/2.00  tff(c_3107, plain, (![A_55]: (A_55='#skF_6' | ~v1_xboole_0(A_55))), inference(resolution, [status(thm)], [c_3093, c_125])).
% 5.48/2.00  tff(c_3140, plain, (![A_405]: (A_405='#skF_8' | ~v1_xboole_0(A_405))), inference(demodulation, [status(thm), theory('equality')], [c_3122, c_3107])).
% 5.48/2.00  tff(c_3147, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_3135, c_3140])).
% 5.48/2.00  tff(c_3126, plain, (~r2_relset_1('#skF_5', '#skF_8', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3122, c_52])).
% 5.48/2.00  tff(c_3168, plain, (~r2_relset_1('#skF_5', '#skF_8', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3147, c_3126])).
% 5.48/2.00  tff(c_3125, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_3122, c_62])).
% 5.48/2.00  tff(c_3169, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_3147, c_3125])).
% 5.48/2.00  tff(c_36, plain, (![A_34, B_35, D_37]: (r2_relset_1(A_34, B_35, D_37, D_37) | ~m1_subset_1(D_37, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.48/2.00  tff(c_3171, plain, (r2_relset_1('#skF_5', '#skF_8', '#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_3169, c_36])).
% 5.48/2.00  tff(c_3181, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3168, c_3171])).
% 5.48/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.48/2.00  
% 5.48/2.00  Inference rules
% 5.48/2.00  ----------------------
% 5.48/2.00  #Ref     : 1
% 5.48/2.00  #Sup     : 751
% 5.48/2.00  #Fact    : 0
% 5.48/2.00  #Define  : 0
% 5.48/2.00  #Split   : 20
% 5.48/2.00  #Chain   : 0
% 5.48/2.00  #Close   : 0
% 5.48/2.00  
% 5.48/2.00  Ordering : KBO
% 5.48/2.00  
% 5.48/2.00  Simplification rules
% 5.48/2.00  ----------------------
% 5.48/2.00  #Subsume      : 246
% 5.48/2.00  #Demod        : 331
% 5.48/2.00  #Tautology    : 216
% 5.48/2.00  #SimpNegUnit  : 14
% 5.48/2.00  #BackRed      : 84
% 5.48/2.00  
% 5.48/2.00  #Partial instantiations: 0
% 5.48/2.00  #Strategies tried      : 1
% 5.48/2.00  
% 5.48/2.00  Timing (in seconds)
% 5.48/2.00  ----------------------
% 5.48/2.00  Preprocessing        : 0.34
% 5.48/2.00  Parsing              : 0.18
% 5.48/2.00  CNF conversion       : 0.02
% 5.48/2.00  Main loop            : 0.89
% 5.48/2.00  Inferencing          : 0.31
% 5.48/2.00  Reduction            : 0.25
% 5.48/2.00  Demodulation         : 0.16
% 5.48/2.00  BG Simplification    : 0.04
% 5.48/2.00  Subsumption          : 0.22
% 5.48/2.00  Abstraction          : 0.04
% 5.48/2.00  MUC search           : 0.00
% 5.48/2.00  Cooper               : 0.00
% 5.48/2.00  Total                : 1.27
% 5.48/2.00  Index Insertion      : 0.00
% 5.48/2.00  Index Deletion       : 0.00
% 5.48/2.00  Index Matching       : 0.00
% 5.48/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
