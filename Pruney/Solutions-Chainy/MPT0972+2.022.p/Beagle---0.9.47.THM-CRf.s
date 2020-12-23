%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:37 EST 2020

% Result     : Theorem 4.62s
% Output     : CNFRefutation 4.62s
% Verified   : 
% Statistics : Number of formulae       :  152 (2441 expanded)
%              Number of leaves         :   36 ( 808 expanded)
%              Depth                    :   14
%              Number of atoms          :  251 (6155 expanded)
%              Number of equality atoms :   92 (1137 expanded)
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_128,negated_conjecture,(
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

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_107,axiom,(
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

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_73,axiom,(
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

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_129,plain,(
    ! [E_54] :
      ( k1_funct_1('#skF_7',E_54) = k1_funct_1('#skF_6',E_54)
      | ~ r2_hidden(E_54,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_134,plain,
    ( k1_funct_1('#skF_7','#skF_1'('#skF_4')) = k1_funct_1('#skF_6','#skF_1'('#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_129])).

tff(c_203,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_135,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_2'(A_55,B_56),A_55)
      | r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_150,plain,(
    ! [A_55,B_56] :
      ( ~ v1_xboole_0(A_55)
      | r1_tarski(A_55,B_56) ) ),
    inference(resolution,[status(thm)],[c_135,c_2])).

tff(c_170,plain,(
    ! [B_62,A_63] :
      ( B_62 = A_63
      | ~ r1_tarski(B_62,A_63)
      | ~ r1_tarski(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_253,plain,(
    ! [B_75,A_76] :
      ( B_75 = A_76
      | ~ r1_tarski(B_75,A_76)
      | ~ v1_xboole_0(A_76) ) ),
    inference(resolution,[status(thm)],[c_150,c_170])).

tff(c_271,plain,(
    ! [B_77,A_78] :
      ( B_77 = A_78
      | ~ v1_xboole_0(B_77)
      | ~ v1_xboole_0(A_78) ) ),
    inference(resolution,[status(thm)],[c_150,c_253])).

tff(c_287,plain,(
    ! [A_80] :
      ( k1_xboole_0 = A_80
      | ~ v1_xboole_0(A_80) ) ),
    inference(resolution,[status(thm)],[c_12,c_271])).

tff(c_294,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_203,c_287])).

tff(c_24,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_302,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_4',B_13) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_294,c_24])).

tff(c_58,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_103,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(A_46,B_47)
      | ~ m1_subset_1(A_46,k1_zfmisc_1(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_111,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_58,c_103])).

tff(c_317,plain,(
    r1_tarski('#skF_7','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_111])).

tff(c_179,plain,(
    ! [B_56,A_55] :
      ( B_56 = A_55
      | ~ r1_tarski(B_56,A_55)
      | ~ v1_xboole_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_150,c_170])).

tff(c_339,plain,
    ( '#skF_7' = '#skF_4'
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_317,c_179])).

tff(c_344,plain,(
    '#skF_7' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_339])).

tff(c_320,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_58])).

tff(c_359,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_320])).

tff(c_22,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_42,plain,(
    ! [A_32] :
      ( v1_funct_2(k1_xboole_0,A_32,k1_xboole_0)
      | k1_xboole_0 = A_32
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_32,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_72,plain,(
    ! [A_32] :
      ( v1_funct_2(k1_xboole_0,A_32,k1_xboole_0)
      | k1_xboole_0 = A_32
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_42])).

tff(c_335,plain,(
    ! [A_32] :
      ( v1_funct_2('#skF_4',A_32,'#skF_4')
      | A_32 = '#skF_4'
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_294,c_294,c_294,c_294,c_72])).

tff(c_336,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_335])).

tff(c_409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_336])).

tff(c_411,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_335])).

tff(c_412,plain,(
    ! [A_84,B_85,D_86] :
      ( r2_relset_1(A_84,B_85,D_86,D_86)
      | ~ m1_subset_1(D_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_603,plain,(
    ! [B_104,D_105] :
      ( r2_relset_1('#skF_4',B_104,D_105,D_105)
      | ~ m1_subset_1(D_105,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_412])).

tff(c_609,plain,(
    ! [B_104] : r2_relset_1('#skF_4',B_104,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_411,c_603])).

tff(c_64,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_110,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_64,c_103])).

tff(c_318,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_110])).

tff(c_447,plain,
    ( '#skF_6' = '#skF_4'
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_318,c_179])).

tff(c_452,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_447])).

tff(c_421,plain,
    ( '#skF_7' = '#skF_4'
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_317,c_179])).

tff(c_426,plain,(
    '#skF_7' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_421])).

tff(c_54,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_432,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_54])).

tff(c_510,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_432])).

tff(c_613,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_609,c_510])).

tff(c_615,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_759,plain,(
    ! [A_126,B_127,D_128] :
      ( r2_relset_1(A_126,B_127,D_128,D_128)
      | ~ m1_subset_1(D_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_772,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_759])).

tff(c_152,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_169,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_152])).

tff(c_62,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_60,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_850,plain,(
    ! [A_145,B_146,C_147] :
      ( k1_relset_1(A_145,B_146,C_147) = k1_relat_1(C_147)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_869,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_850])).

tff(c_1124,plain,(
    ! [B_193,A_194,C_195] :
      ( k1_xboole_0 = B_193
      | k1_relset_1(A_194,B_193,C_195) = A_194
      | ~ v1_funct_2(C_195,A_194,B_193)
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_194,B_193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1134,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_1124])).

tff(c_1147,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_869,c_1134])).

tff(c_1155,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1147])).

tff(c_168,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_152])).

tff(c_68,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_66,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_868,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_64,c_850])).

tff(c_1131,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_1124])).

tff(c_1144,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_868,c_1131])).

tff(c_1149,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1144])).

tff(c_1382,plain,(
    ! [A_220,B_221] :
      ( r2_hidden('#skF_3'(A_220,B_221),k1_relat_1(A_220))
      | B_221 = A_220
      | k1_relat_1(B_221) != k1_relat_1(A_220)
      | ~ v1_funct_1(B_221)
      | ~ v1_relat_1(B_221)
      | ~ v1_funct_1(A_220)
      | ~ v1_relat_1(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1393,plain,(
    ! [B_221] :
      ( r2_hidden('#skF_3'('#skF_6',B_221),'#skF_4')
      | B_221 = '#skF_6'
      | k1_relat_1(B_221) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_221)
      | ~ v1_relat_1(B_221)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1149,c_1382])).

tff(c_1506,plain,(
    ! [B_230] :
      ( r2_hidden('#skF_3'('#skF_6',B_230),'#skF_4')
      | B_230 = '#skF_6'
      | k1_relat_1(B_230) != '#skF_4'
      | ~ v1_funct_1(B_230)
      | ~ v1_relat_1(B_230) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_68,c_1149,c_1393])).

tff(c_56,plain,(
    ! [E_39] :
      ( k1_funct_1('#skF_7',E_39) = k1_funct_1('#skF_6',E_39)
      | ~ r2_hidden(E_39,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_1898,plain,(
    ! [B_261] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_6',B_261)) = k1_funct_1('#skF_6','#skF_3'('#skF_6',B_261))
      | B_261 = '#skF_6'
      | k1_relat_1(B_261) != '#skF_4'
      | ~ v1_funct_1(B_261)
      | ~ v1_relat_1(B_261) ) ),
    inference(resolution,[status(thm)],[c_1506,c_56])).

tff(c_30,plain,(
    ! [B_20,A_16] :
      ( k1_funct_1(B_20,'#skF_3'(A_16,B_20)) != k1_funct_1(A_16,'#skF_3'(A_16,B_20))
      | B_20 = A_16
      | k1_relat_1(B_20) != k1_relat_1(A_16)
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1905,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_7') != '#skF_4'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1898,c_30])).

tff(c_1912,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_62,c_1155,c_168,c_68,c_1149,c_1155,c_1905])).

tff(c_1937,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1912,c_54])).

tff(c_1948,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_772,c_1937])).

tff(c_1949,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1147])).

tff(c_1977,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1949,c_12])).

tff(c_1976,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1949,c_1949,c_22])).

tff(c_670,plain,(
    ! [B_116,A_117] :
      ( B_116 = A_117
      | ~ r1_tarski(B_116,A_117)
      | ~ v1_xboole_0(A_117) ) ),
    inference(resolution,[status(thm)],[c_150,c_170])).

tff(c_684,plain,
    ( k2_zfmisc_1('#skF_4','#skF_5') = '#skF_7'
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_111,c_670])).

tff(c_702,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_684])).

tff(c_2061,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1976,c_702])).

tff(c_2068,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1977,c_2061])).

tff(c_2069,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1144])).

tff(c_2097,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2069,c_12])).

tff(c_2096,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2069,c_2069,c_22])).

tff(c_2173,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2096,c_702])).

tff(c_2180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2097,c_2173])).

tff(c_2181,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_684])).

tff(c_2182,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_684])).

tff(c_2209,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2181,c_2182])).

tff(c_2184,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2181,c_110])).

tff(c_2207,plain,
    ( '#skF_7' = '#skF_6'
    | ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_2184,c_179])).

tff(c_2274,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2209,c_2207])).

tff(c_688,plain,(
    ! [B_118,A_119] :
      ( B_118 = A_119
      | ~ v1_xboole_0(B_118)
      | ~ v1_xboole_0(A_119) ) ),
    inference(resolution,[status(thm)],[c_150,c_670])).

tff(c_691,plain,(
    ! [A_119] :
      ( k1_xboole_0 = A_119
      | ~ v1_xboole_0(A_119) ) ),
    inference(resolution,[status(thm)],[c_12,c_688])).

tff(c_2218,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_2209,c_691])).

tff(c_2277,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2274,c_2218])).

tff(c_20,plain,(
    ! [B_13,A_12] :
      ( k1_xboole_0 = B_13
      | k1_xboole_0 = A_12
      | k2_zfmisc_1(A_12,B_13) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2197,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 != '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_2181,c_20])).

tff(c_2403,plain,
    ( '#skF_5' = '#skF_6'
    | '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2277,c_2274,c_2277,c_2277,c_2197])).

tff(c_2404,plain,(
    '#skF_6' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2403])).

tff(c_2278,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2274,c_2209])).

tff(c_2414,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2404,c_2278])).

tff(c_2420,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_615,c_2414])).

tff(c_2421,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2403])).

tff(c_2285,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2274,c_54])).

tff(c_2431,plain,(
    ~ r2_relset_1('#skF_4','#skF_6','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2421,c_2285])).

tff(c_2185,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2181,c_64])).

tff(c_2276,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2274,c_2185])).

tff(c_2280,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2274,c_2181])).

tff(c_2373,plain,(
    ! [A_276,B_277,D_278] :
      ( r2_relset_1(A_276,B_277,D_278,D_278)
      | ~ m1_subset_1(D_278,k1_zfmisc_1(k2_zfmisc_1(A_276,B_277))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2379,plain,(
    ! [D_278] :
      ( r2_relset_1('#skF_4','#skF_5',D_278,D_278)
      | ~ m1_subset_1(D_278,k1_zfmisc_1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2280,c_2373])).

tff(c_2505,plain,(
    ! [D_292] :
      ( r2_relset_1('#skF_4','#skF_6',D_292,D_292)
      | ~ m1_subset_1(D_292,k1_zfmisc_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2421,c_2379])).

tff(c_2507,plain,(
    r2_relset_1('#skF_4','#skF_6','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_2276,c_2505])).

tff(c_2514,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2431,c_2507])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:03:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.62/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/1.85  
% 4.62/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/1.86  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 4.62/1.86  
% 4.62/1.86  %Foreground sorts:
% 4.62/1.86  
% 4.62/1.86  
% 4.62/1.86  %Background operators:
% 4.62/1.86  
% 4.62/1.86  
% 4.62/1.86  %Foreground operators:
% 4.62/1.86  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.62/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.62/1.86  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.62/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.62/1.86  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.62/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.62/1.86  tff('#skF_7', type, '#skF_7': $i).
% 4.62/1.86  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.62/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.62/1.86  tff('#skF_5', type, '#skF_5': $i).
% 4.62/1.86  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.62/1.86  tff('#skF_6', type, '#skF_6': $i).
% 4.62/1.86  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.62/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.62/1.86  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.62/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.62/1.86  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.62/1.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.62/1.86  tff('#skF_4', type, '#skF_4': $i).
% 4.62/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.62/1.86  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.62/1.86  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.62/1.86  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.62/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.62/1.86  
% 4.62/1.88  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.62/1.88  tff(f_128, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 4.62/1.88  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.62/1.88  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.62/1.88  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.62/1.88  tff(f_51, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.62/1.88  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.62/1.88  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.62/1.88  tff(f_89, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.62/1.88  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.62/1.88  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.62/1.88  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 4.62/1.88  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.62/1.88  tff(c_129, plain, (![E_54]: (k1_funct_1('#skF_7', E_54)=k1_funct_1('#skF_6', E_54) | ~r2_hidden(E_54, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.62/1.88  tff(c_134, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_4'))=k1_funct_1('#skF_6', '#skF_1'('#skF_4')) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_129])).
% 4.62/1.88  tff(c_203, plain, (v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_134])).
% 4.62/1.88  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.62/1.88  tff(c_135, plain, (![A_55, B_56]: (r2_hidden('#skF_2'(A_55, B_56), A_55) | r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.62/1.88  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.62/1.88  tff(c_150, plain, (![A_55, B_56]: (~v1_xboole_0(A_55) | r1_tarski(A_55, B_56))), inference(resolution, [status(thm)], [c_135, c_2])).
% 4.62/1.88  tff(c_170, plain, (![B_62, A_63]: (B_62=A_63 | ~r1_tarski(B_62, A_63) | ~r1_tarski(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.62/1.88  tff(c_253, plain, (![B_75, A_76]: (B_75=A_76 | ~r1_tarski(B_75, A_76) | ~v1_xboole_0(A_76))), inference(resolution, [status(thm)], [c_150, c_170])).
% 4.62/1.88  tff(c_271, plain, (![B_77, A_78]: (B_77=A_78 | ~v1_xboole_0(B_77) | ~v1_xboole_0(A_78))), inference(resolution, [status(thm)], [c_150, c_253])).
% 4.62/1.88  tff(c_287, plain, (![A_80]: (k1_xboole_0=A_80 | ~v1_xboole_0(A_80))), inference(resolution, [status(thm)], [c_12, c_271])).
% 4.62/1.88  tff(c_294, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_203, c_287])).
% 4.62/1.88  tff(c_24, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.62/1.88  tff(c_302, plain, (![B_13]: (k2_zfmisc_1('#skF_4', B_13)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_294, c_294, c_24])).
% 4.62/1.88  tff(c_58, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.62/1.88  tff(c_103, plain, (![A_46, B_47]: (r1_tarski(A_46, B_47) | ~m1_subset_1(A_46, k1_zfmisc_1(B_47)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.62/1.88  tff(c_111, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_58, c_103])).
% 4.62/1.88  tff(c_317, plain, (r1_tarski('#skF_7', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_302, c_111])).
% 4.62/1.88  tff(c_179, plain, (![B_56, A_55]: (B_56=A_55 | ~r1_tarski(B_56, A_55) | ~v1_xboole_0(A_55))), inference(resolution, [status(thm)], [c_150, c_170])).
% 4.62/1.88  tff(c_339, plain, ('#skF_7'='#skF_4' | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_317, c_179])).
% 4.62/1.88  tff(c_344, plain, ('#skF_7'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_203, c_339])).
% 4.62/1.88  tff(c_320, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_302, c_58])).
% 4.62/1.88  tff(c_359, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_344, c_320])).
% 4.62/1.88  tff(c_22, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.62/1.88  tff(c_42, plain, (![A_32]: (v1_funct_2(k1_xboole_0, A_32, k1_xboole_0) | k1_xboole_0=A_32 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_32, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.62/1.88  tff(c_72, plain, (![A_32]: (v1_funct_2(k1_xboole_0, A_32, k1_xboole_0) | k1_xboole_0=A_32 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_42])).
% 4.62/1.88  tff(c_335, plain, (![A_32]: (v1_funct_2('#skF_4', A_32, '#skF_4') | A_32='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_294, c_294, c_294, c_294, c_294, c_72])).
% 4.62/1.88  tff(c_336, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_335])).
% 4.62/1.88  tff(c_409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_359, c_336])).
% 4.62/1.88  tff(c_411, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_335])).
% 4.62/1.88  tff(c_412, plain, (![A_84, B_85, D_86]: (r2_relset_1(A_84, B_85, D_86, D_86) | ~m1_subset_1(D_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.62/1.88  tff(c_603, plain, (![B_104, D_105]: (r2_relset_1('#skF_4', B_104, D_105, D_105) | ~m1_subset_1(D_105, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_302, c_412])).
% 4.62/1.88  tff(c_609, plain, (![B_104]: (r2_relset_1('#skF_4', B_104, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_411, c_603])).
% 4.62/1.88  tff(c_64, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.62/1.88  tff(c_110, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_64, c_103])).
% 4.62/1.88  tff(c_318, plain, (r1_tarski('#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_302, c_110])).
% 4.62/1.88  tff(c_447, plain, ('#skF_6'='#skF_4' | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_318, c_179])).
% 4.62/1.88  tff(c_452, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_203, c_447])).
% 4.62/1.88  tff(c_421, plain, ('#skF_7'='#skF_4' | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_317, c_179])).
% 4.62/1.88  tff(c_426, plain, ('#skF_7'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_203, c_421])).
% 4.62/1.88  tff(c_54, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.62/1.88  tff(c_432, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_426, c_54])).
% 4.62/1.88  tff(c_510, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_452, c_432])).
% 4.62/1.88  tff(c_613, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_609, c_510])).
% 4.62/1.88  tff(c_615, plain, (~v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_134])).
% 4.62/1.88  tff(c_759, plain, (![A_126, B_127, D_128]: (r2_relset_1(A_126, B_127, D_128, D_128) | ~m1_subset_1(D_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.62/1.88  tff(c_772, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_64, c_759])).
% 4.62/1.88  tff(c_152, plain, (![C_59, A_60, B_61]: (v1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.62/1.88  tff(c_169, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_58, c_152])).
% 4.62/1.88  tff(c_62, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.62/1.88  tff(c_60, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.62/1.88  tff(c_850, plain, (![A_145, B_146, C_147]: (k1_relset_1(A_145, B_146, C_147)=k1_relat_1(C_147) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.62/1.88  tff(c_869, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_58, c_850])).
% 4.62/1.88  tff(c_1124, plain, (![B_193, A_194, C_195]: (k1_xboole_0=B_193 | k1_relset_1(A_194, B_193, C_195)=A_194 | ~v1_funct_2(C_195, A_194, B_193) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_194, B_193))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.62/1.88  tff(c_1134, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_58, c_1124])).
% 4.62/1.88  tff(c_1147, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_869, c_1134])).
% 4.62/1.88  tff(c_1155, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_1147])).
% 4.62/1.88  tff(c_168, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_64, c_152])).
% 4.62/1.88  tff(c_68, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.62/1.88  tff(c_66, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.62/1.88  tff(c_868, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_64, c_850])).
% 4.62/1.88  tff(c_1131, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_64, c_1124])).
% 4.62/1.88  tff(c_1144, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_868, c_1131])).
% 4.62/1.88  tff(c_1149, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_1144])).
% 4.62/1.88  tff(c_1382, plain, (![A_220, B_221]: (r2_hidden('#skF_3'(A_220, B_221), k1_relat_1(A_220)) | B_221=A_220 | k1_relat_1(B_221)!=k1_relat_1(A_220) | ~v1_funct_1(B_221) | ~v1_relat_1(B_221) | ~v1_funct_1(A_220) | ~v1_relat_1(A_220))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.62/1.88  tff(c_1393, plain, (![B_221]: (r2_hidden('#skF_3'('#skF_6', B_221), '#skF_4') | B_221='#skF_6' | k1_relat_1(B_221)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_221) | ~v1_relat_1(B_221) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1149, c_1382])).
% 4.62/1.88  tff(c_1506, plain, (![B_230]: (r2_hidden('#skF_3'('#skF_6', B_230), '#skF_4') | B_230='#skF_6' | k1_relat_1(B_230)!='#skF_4' | ~v1_funct_1(B_230) | ~v1_relat_1(B_230))), inference(demodulation, [status(thm), theory('equality')], [c_168, c_68, c_1149, c_1393])).
% 4.62/1.88  tff(c_56, plain, (![E_39]: (k1_funct_1('#skF_7', E_39)=k1_funct_1('#skF_6', E_39) | ~r2_hidden(E_39, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.62/1.88  tff(c_1898, plain, (![B_261]: (k1_funct_1('#skF_7', '#skF_3'('#skF_6', B_261))=k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_261)) | B_261='#skF_6' | k1_relat_1(B_261)!='#skF_4' | ~v1_funct_1(B_261) | ~v1_relat_1(B_261))), inference(resolution, [status(thm)], [c_1506, c_56])).
% 4.62/1.88  tff(c_30, plain, (![B_20, A_16]: (k1_funct_1(B_20, '#skF_3'(A_16, B_20))!=k1_funct_1(A_16, '#skF_3'(A_16, B_20)) | B_20=A_16 | k1_relat_1(B_20)!=k1_relat_1(A_16) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.62/1.88  tff(c_1905, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_7'='#skF_6' | k1_relat_1('#skF_7')!='#skF_4' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1898, c_30])).
% 4.62/1.88  tff(c_1912, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_169, c_62, c_1155, c_168, c_68, c_1149, c_1155, c_1905])).
% 4.62/1.88  tff(c_1937, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1912, c_54])).
% 4.62/1.88  tff(c_1948, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_772, c_1937])).
% 4.62/1.88  tff(c_1949, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1147])).
% 4.62/1.88  tff(c_1977, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1949, c_12])).
% 4.62/1.88  tff(c_1976, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1949, c_1949, c_22])).
% 4.62/1.88  tff(c_670, plain, (![B_116, A_117]: (B_116=A_117 | ~r1_tarski(B_116, A_117) | ~v1_xboole_0(A_117))), inference(resolution, [status(thm)], [c_150, c_170])).
% 4.62/1.88  tff(c_684, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_7' | ~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_111, c_670])).
% 4.62/1.88  tff(c_702, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_684])).
% 4.62/1.88  tff(c_2061, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1976, c_702])).
% 4.62/1.88  tff(c_2068, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1977, c_2061])).
% 4.62/1.88  tff(c_2069, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1144])).
% 4.62/1.88  tff(c_2097, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2069, c_12])).
% 4.62/1.88  tff(c_2096, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2069, c_2069, c_22])).
% 4.62/1.88  tff(c_2173, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2096, c_702])).
% 4.62/1.88  tff(c_2180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2097, c_2173])).
% 4.62/1.88  tff(c_2181, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_7'), inference(splitRight, [status(thm)], [c_684])).
% 4.62/1.88  tff(c_2182, plain, (v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_684])).
% 4.62/1.88  tff(c_2209, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2181, c_2182])).
% 4.62/1.88  tff(c_2184, plain, (r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2181, c_110])).
% 4.62/1.88  tff(c_2207, plain, ('#skF_7'='#skF_6' | ~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_2184, c_179])).
% 4.62/1.88  tff(c_2274, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2209, c_2207])).
% 4.62/1.88  tff(c_688, plain, (![B_118, A_119]: (B_118=A_119 | ~v1_xboole_0(B_118) | ~v1_xboole_0(A_119))), inference(resolution, [status(thm)], [c_150, c_670])).
% 4.62/1.88  tff(c_691, plain, (![A_119]: (k1_xboole_0=A_119 | ~v1_xboole_0(A_119))), inference(resolution, [status(thm)], [c_12, c_688])).
% 4.62/1.88  tff(c_2218, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_2209, c_691])).
% 4.62/1.88  tff(c_2277, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2274, c_2218])).
% 4.62/1.88  tff(c_20, plain, (![B_13, A_12]: (k1_xboole_0=B_13 | k1_xboole_0=A_12 | k2_zfmisc_1(A_12, B_13)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.62/1.88  tff(c_2197, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0!='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_2181, c_20])).
% 4.62/1.88  tff(c_2403, plain, ('#skF_5'='#skF_6' | '#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2277, c_2274, c_2277, c_2277, c_2197])).
% 4.62/1.88  tff(c_2404, plain, ('#skF_6'='#skF_4'), inference(splitLeft, [status(thm)], [c_2403])).
% 4.62/1.88  tff(c_2278, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2274, c_2209])).
% 4.62/1.88  tff(c_2414, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2404, c_2278])).
% 4.62/1.88  tff(c_2420, plain, $false, inference(negUnitSimplification, [status(thm)], [c_615, c_2414])).
% 4.62/1.88  tff(c_2421, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_2403])).
% 4.62/1.88  tff(c_2285, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2274, c_54])).
% 4.62/1.88  tff(c_2431, plain, (~r2_relset_1('#skF_4', '#skF_6', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2421, c_2285])).
% 4.62/1.88  tff(c_2185, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_2181, c_64])).
% 4.62/1.88  tff(c_2276, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_2274, c_2185])).
% 4.62/1.88  tff(c_2280, plain, (k2_zfmisc_1('#skF_4', '#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_2274, c_2181])).
% 4.62/1.88  tff(c_2373, plain, (![A_276, B_277, D_278]: (r2_relset_1(A_276, B_277, D_278, D_278) | ~m1_subset_1(D_278, k1_zfmisc_1(k2_zfmisc_1(A_276, B_277))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.62/1.88  tff(c_2379, plain, (![D_278]: (r2_relset_1('#skF_4', '#skF_5', D_278, D_278) | ~m1_subset_1(D_278, k1_zfmisc_1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_2280, c_2373])).
% 4.62/1.88  tff(c_2505, plain, (![D_292]: (r2_relset_1('#skF_4', '#skF_6', D_292, D_292) | ~m1_subset_1(D_292, k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_2421, c_2379])).
% 4.62/1.88  tff(c_2507, plain, (r2_relset_1('#skF_4', '#skF_6', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_2276, c_2505])).
% 4.62/1.88  tff(c_2514, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2431, c_2507])).
% 4.62/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/1.88  
% 4.62/1.88  Inference rules
% 4.62/1.88  ----------------------
% 4.62/1.88  #Ref     : 1
% 4.62/1.88  #Sup     : 501
% 4.62/1.88  #Fact    : 0
% 4.62/1.88  #Define  : 0
% 4.62/1.88  #Split   : 14
% 4.62/1.88  #Chain   : 0
% 4.62/1.88  #Close   : 0
% 4.62/1.88  
% 4.62/1.88  Ordering : KBO
% 4.62/1.88  
% 4.62/1.88  Simplification rules
% 4.62/1.88  ----------------------
% 4.62/1.88  #Subsume      : 110
% 4.62/1.88  #Demod        : 676
% 4.62/1.88  #Tautology    : 290
% 4.62/1.88  #SimpNegUnit  : 11
% 4.62/1.88  #BackRed      : 231
% 4.62/1.88  
% 4.62/1.88  #Partial instantiations: 0
% 4.62/1.88  #Strategies tried      : 1
% 4.62/1.88  
% 4.62/1.88  Timing (in seconds)
% 4.62/1.88  ----------------------
% 4.62/1.88  Preprocessing        : 0.36
% 4.62/1.88  Parsing              : 0.19
% 4.62/1.88  CNF conversion       : 0.02
% 4.62/1.88  Main loop            : 0.72
% 4.62/1.88  Inferencing          : 0.22
% 4.62/1.88  Reduction            : 0.24
% 4.62/1.88  Demodulation         : 0.17
% 4.62/1.88  BG Simplification    : 0.03
% 4.62/1.88  Subsumption          : 0.15
% 4.62/1.88  Abstraction          : 0.03
% 4.62/1.88  MUC search           : 0.00
% 4.62/1.88  Cooper               : 0.00
% 4.62/1.88  Total                : 1.13
% 4.62/1.88  Index Insertion      : 0.00
% 4.62/1.88  Index Deletion       : 0.00
% 4.62/1.88  Index Matching       : 0.00
% 4.62/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
