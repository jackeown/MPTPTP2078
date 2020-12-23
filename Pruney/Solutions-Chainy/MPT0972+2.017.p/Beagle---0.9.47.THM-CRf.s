%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:37 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 255 expanded)
%              Number of leaves         :   36 ( 103 expanded)
%              Depth                    :   11
%              Number of atoms          :  183 ( 801 expanded)
%              Number of equality atoms :   50 ( 182 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_135,negated_conjecture,(
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

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_84,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_114,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_48,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
          & ~ v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_subset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_58,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_593,plain,(
    ! [A_139,B_140,D_141] :
      ( r2_relset_1(A_139,B_140,D_141,D_141)
      | ~ m1_subset_1(D_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_600,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_593])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_127,plain,(
    ! [C_63,B_64,A_65] :
      ( v1_xboole_0(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(B_64,A_65)))
      | ~ v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_139,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_127])).

tff(c_141,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_142,plain,(
    ! [A_66,B_67,D_68] :
      ( r2_relset_1(A_66,B_67,D_68,D_68)
      | ~ m1_subset_1(D_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_151,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_142])).

tff(c_52,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_68,plain,(
    ! [C_46,A_47,B_48] :
      ( v1_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_81,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_68])).

tff(c_56,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_54,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_178,plain,(
    ! [A_77,B_78,C_79] :
      ( k1_relset_1(A_77,B_78,C_79) = k1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_191,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_52,c_178])).

tff(c_270,plain,(
    ! [B_99,A_100,C_101] :
      ( k1_xboole_0 = B_99
      | k1_relset_1(A_100,B_99,C_101) = A_100
      | ~ v1_funct_2(C_101,A_100,B_99)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_100,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_280,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_270])).

tff(c_287,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_191,c_280])).

tff(c_289,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_287])).

tff(c_80,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_68])).

tff(c_62,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_60,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_190,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_178])).

tff(c_277,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_270])).

tff(c_284,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_190,c_277])).

tff(c_288,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_284])).

tff(c_338,plain,(
    ! [A_109,B_110] :
      ( r2_hidden('#skF_3'(A_109,B_110),k1_relat_1(A_109))
      | B_110 = A_109
      | k1_relat_1(B_110) != k1_relat_1(A_109)
      | ~ v1_funct_1(B_110)
      | ~ v1_relat_1(B_110)
      | ~ v1_funct_1(A_109)
      | ~ v1_relat_1(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_346,plain,(
    ! [B_110] :
      ( r2_hidden('#skF_3'('#skF_6',B_110),'#skF_4')
      | B_110 = '#skF_6'
      | k1_relat_1(B_110) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_110)
      | ~ v1_relat_1(B_110)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_338])).

tff(c_360,plain,(
    ! [B_112] :
      ( r2_hidden('#skF_3'('#skF_6',B_112),'#skF_4')
      | B_112 = '#skF_6'
      | k1_relat_1(B_112) != '#skF_4'
      | ~ v1_funct_1(B_112)
      | ~ v1_relat_1(B_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_62,c_288,c_346])).

tff(c_50,plain,(
    ! [E_40] :
      ( k1_funct_1('#skF_7',E_40) = k1_funct_1('#skF_6',E_40)
      | ~ r2_hidden(E_40,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_366,plain,(
    ! [B_112] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_6',B_112)) = k1_funct_1('#skF_6','#skF_3'('#skF_6',B_112))
      | B_112 = '#skF_6'
      | k1_relat_1(B_112) != '#skF_4'
      | ~ v1_funct_1(B_112)
      | ~ v1_relat_1(B_112) ) ),
    inference(resolution,[status(thm)],[c_360,c_50])).

tff(c_413,plain,(
    ! [B_119,A_120] :
      ( k1_funct_1(B_119,'#skF_3'(A_120,B_119)) != k1_funct_1(A_120,'#skF_3'(A_120,B_119))
      | B_119 = A_120
      | k1_relat_1(B_119) != k1_relat_1(A_120)
      | ~ v1_funct_1(B_119)
      | ~ v1_relat_1(B_119)
      | ~ v1_funct_1(A_120)
      | ~ v1_relat_1(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_417,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_7') != '#skF_4'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_366,c_413])).

tff(c_423,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_56,c_289,c_80,c_62,c_289,c_288,c_417])).

tff(c_48,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_438,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_48])).

tff(c_448,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_438])).

tff(c_449,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_287])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_457,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_449,c_8])).

tff(c_459,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_457])).

tff(c_460,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_284])).

tff(c_468,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_460,c_8])).

tff(c_470,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_468])).

tff(c_472,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_140,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_127])).

tff(c_473,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_475,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_472,c_473])).

tff(c_477,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_18,plain,(
    ! [A_8] :
      ( m1_subset_1('#skF_2'(A_8),k1_zfmisc_1(A_8))
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_504,plain,(
    ! [B_127,A_128] :
      ( v1_xboole_0('#skF_2'(k2_zfmisc_1(B_127,A_128)))
      | ~ v1_xboole_0(A_128)
      | v1_xboole_0(k2_zfmisc_1(B_127,A_128)) ) ),
    inference(resolution,[status(thm)],[c_18,c_127])).

tff(c_16,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0('#skF_2'(A_8))
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_509,plain,(
    ! [A_129,B_130] :
      ( ~ v1_xboole_0(A_129)
      | v1_xboole_0(k2_zfmisc_1(B_130,A_129)) ) ),
    inference(resolution,[status(thm)],[c_504,c_16])).

tff(c_115,plain,(
    ! [C_58,B_59,A_60] :
      ( ~ v1_xboole_0(C_58)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(C_58))
      | ~ r2_hidden(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_123,plain,(
    ! [A_60] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(A_60,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_58,c_115])).

tff(c_125,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_123])).

tff(c_512,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_509,c_125])).

tff(c_516,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_512])).

tff(c_518,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_124,plain,(
    ! [A_60] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'))
      | ~ r2_hidden(A_60,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_52,c_115])).

tff(c_559,plain,(
    ! [A_137] : ~ r2_hidden(A_137,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_518,c_124])).

tff(c_565,plain,(
    ! [B_138] : r1_tarski('#skF_7',B_138) ),
    inference(resolution,[status(thm)],[c_6,c_559])).

tff(c_519,plain,(
    ! [A_131] : ~ r2_hidden(A_131,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_525,plain,(
    ! [B_132] : r1_tarski('#skF_6',B_132) ),
    inference(resolution,[status(thm)],[c_6,c_519])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_528,plain,(
    ! [B_132] :
      ( B_132 = '#skF_6'
      | ~ r1_tarski(B_132,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_525,c_10])).

tff(c_572,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_565,c_528])).

tff(c_580,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_572,c_48])).

tff(c_602,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_600,c_580])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:10:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.75/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.42  
% 2.75/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.42  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_1
% 2.75/1.42  
% 2.75/1.42  %Foreground sorts:
% 2.75/1.42  
% 2.75/1.42  
% 2.75/1.42  %Background operators:
% 2.75/1.42  
% 2.75/1.42  
% 2.75/1.42  %Foreground operators:
% 2.75/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.75/1.42  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.75/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.75/1.42  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.75/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.75/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.75/1.42  tff('#skF_7', type, '#skF_7': $i).
% 2.75/1.42  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.75/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.75/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.75/1.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.75/1.42  tff('#skF_6', type, '#skF_6': $i).
% 2.75/1.42  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.75/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.75/1.42  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.75/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.75/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.75/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.75/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.75/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.75/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.75/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.75/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.75/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.75/1.42  
% 2.75/1.44  tff(f_135, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_2)).
% 2.75/1.44  tff(f_96, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 2.75/1.44  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.75/1.44  tff(f_84, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 2.75/1.44  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.75/1.44  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.75/1.44  tff(f_114, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.75/1.44  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_funct_1)).
% 2.75/1.44  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.75/1.44  tff(f_48, axiom, (![A]: (~v1_xboole_0(A) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_subset_1)).
% 2.75/1.44  tff(f_55, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.75/1.44  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.75/1.44  tff(c_58, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.75/1.44  tff(c_593, plain, (![A_139, B_140, D_141]: (r2_relset_1(A_139, B_140, D_141, D_141) | ~m1_subset_1(D_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.75/1.44  tff(c_600, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_58, c_593])).
% 2.75/1.44  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.75/1.44  tff(c_127, plain, (![C_63, B_64, A_65]: (v1_xboole_0(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(B_64, A_65))) | ~v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.75/1.44  tff(c_139, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_58, c_127])).
% 2.75/1.44  tff(c_141, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_139])).
% 2.75/1.44  tff(c_142, plain, (![A_66, B_67, D_68]: (r2_relset_1(A_66, B_67, D_68, D_68) | ~m1_subset_1(D_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.75/1.44  tff(c_151, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_58, c_142])).
% 2.75/1.44  tff(c_52, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.75/1.44  tff(c_68, plain, (![C_46, A_47, B_48]: (v1_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.75/1.44  tff(c_81, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_52, c_68])).
% 2.75/1.44  tff(c_56, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.75/1.44  tff(c_54, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.75/1.44  tff(c_178, plain, (![A_77, B_78, C_79]: (k1_relset_1(A_77, B_78, C_79)=k1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.75/1.44  tff(c_191, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_52, c_178])).
% 2.75/1.44  tff(c_270, plain, (![B_99, A_100, C_101]: (k1_xboole_0=B_99 | k1_relset_1(A_100, B_99, C_101)=A_100 | ~v1_funct_2(C_101, A_100, B_99) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_100, B_99))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 2.75/1.44  tff(c_280, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_52, c_270])).
% 2.75/1.44  tff(c_287, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_191, c_280])).
% 2.75/1.44  tff(c_289, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_287])).
% 2.75/1.44  tff(c_80, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_68])).
% 2.75/1.44  tff(c_62, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.75/1.44  tff(c_60, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.75/1.44  tff(c_190, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_58, c_178])).
% 2.75/1.44  tff(c_277, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_58, c_270])).
% 2.75/1.44  tff(c_284, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_190, c_277])).
% 2.75/1.44  tff(c_288, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_284])).
% 2.75/1.44  tff(c_338, plain, (![A_109, B_110]: (r2_hidden('#skF_3'(A_109, B_110), k1_relat_1(A_109)) | B_110=A_109 | k1_relat_1(B_110)!=k1_relat_1(A_109) | ~v1_funct_1(B_110) | ~v1_relat_1(B_110) | ~v1_funct_1(A_109) | ~v1_relat_1(A_109))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.75/1.44  tff(c_346, plain, (![B_110]: (r2_hidden('#skF_3'('#skF_6', B_110), '#skF_4') | B_110='#skF_6' | k1_relat_1(B_110)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_110) | ~v1_relat_1(B_110) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_288, c_338])).
% 2.75/1.44  tff(c_360, plain, (![B_112]: (r2_hidden('#skF_3'('#skF_6', B_112), '#skF_4') | B_112='#skF_6' | k1_relat_1(B_112)!='#skF_4' | ~v1_funct_1(B_112) | ~v1_relat_1(B_112))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_62, c_288, c_346])).
% 2.75/1.44  tff(c_50, plain, (![E_40]: (k1_funct_1('#skF_7', E_40)=k1_funct_1('#skF_6', E_40) | ~r2_hidden(E_40, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.75/1.44  tff(c_366, plain, (![B_112]: (k1_funct_1('#skF_7', '#skF_3'('#skF_6', B_112))=k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_112)) | B_112='#skF_6' | k1_relat_1(B_112)!='#skF_4' | ~v1_funct_1(B_112) | ~v1_relat_1(B_112))), inference(resolution, [status(thm)], [c_360, c_50])).
% 2.75/1.44  tff(c_413, plain, (![B_119, A_120]: (k1_funct_1(B_119, '#skF_3'(A_120, B_119))!=k1_funct_1(A_120, '#skF_3'(A_120, B_119)) | B_119=A_120 | k1_relat_1(B_119)!=k1_relat_1(A_120) | ~v1_funct_1(B_119) | ~v1_relat_1(B_119) | ~v1_funct_1(A_120) | ~v1_relat_1(A_120))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.75/1.44  tff(c_417, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_7'='#skF_6' | k1_relat_1('#skF_7')!='#skF_4' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_366, c_413])).
% 2.75/1.44  tff(c_423, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_81, c_56, c_289, c_80, c_62, c_289, c_288, c_417])).
% 2.75/1.44  tff(c_48, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.75/1.44  tff(c_438, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_423, c_48])).
% 2.75/1.44  tff(c_448, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_151, c_438])).
% 2.75/1.44  tff(c_449, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_287])).
% 2.75/1.44  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.75/1.44  tff(c_457, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_449, c_8])).
% 2.75/1.44  tff(c_459, plain, $false, inference(negUnitSimplification, [status(thm)], [c_141, c_457])).
% 2.75/1.44  tff(c_460, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_284])).
% 2.75/1.44  tff(c_468, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_460, c_8])).
% 2.75/1.44  tff(c_470, plain, $false, inference(negUnitSimplification, [status(thm)], [c_141, c_468])).
% 2.75/1.44  tff(c_472, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_139])).
% 2.75/1.44  tff(c_140, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_52, c_127])).
% 2.75/1.44  tff(c_473, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_140])).
% 2.75/1.44  tff(c_475, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_472, c_473])).
% 2.75/1.44  tff(c_477, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_140])).
% 2.75/1.44  tff(c_18, plain, (![A_8]: (m1_subset_1('#skF_2'(A_8), k1_zfmisc_1(A_8)) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.75/1.44  tff(c_504, plain, (![B_127, A_128]: (v1_xboole_0('#skF_2'(k2_zfmisc_1(B_127, A_128))) | ~v1_xboole_0(A_128) | v1_xboole_0(k2_zfmisc_1(B_127, A_128)))), inference(resolution, [status(thm)], [c_18, c_127])).
% 2.75/1.44  tff(c_16, plain, (![A_8]: (~v1_xboole_0('#skF_2'(A_8)) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.75/1.44  tff(c_509, plain, (![A_129, B_130]: (~v1_xboole_0(A_129) | v1_xboole_0(k2_zfmisc_1(B_130, A_129)))), inference(resolution, [status(thm)], [c_504, c_16])).
% 2.75/1.44  tff(c_115, plain, (![C_58, B_59, A_60]: (~v1_xboole_0(C_58) | ~m1_subset_1(B_59, k1_zfmisc_1(C_58)) | ~r2_hidden(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.75/1.44  tff(c_123, plain, (![A_60]: (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(A_60, '#skF_6'))), inference(resolution, [status(thm)], [c_58, c_115])).
% 2.75/1.44  tff(c_125, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_123])).
% 2.75/1.44  tff(c_512, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_509, c_125])).
% 2.75/1.44  tff(c_516, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_477, c_512])).
% 2.75/1.44  tff(c_518, plain, (v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_123])).
% 2.75/1.44  tff(c_124, plain, (![A_60]: (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5')) | ~r2_hidden(A_60, '#skF_7'))), inference(resolution, [status(thm)], [c_52, c_115])).
% 2.75/1.44  tff(c_559, plain, (![A_137]: (~r2_hidden(A_137, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_518, c_124])).
% 2.75/1.44  tff(c_565, plain, (![B_138]: (r1_tarski('#skF_7', B_138))), inference(resolution, [status(thm)], [c_6, c_559])).
% 2.75/1.44  tff(c_519, plain, (![A_131]: (~r2_hidden(A_131, '#skF_6'))), inference(splitRight, [status(thm)], [c_123])).
% 2.75/1.44  tff(c_525, plain, (![B_132]: (r1_tarski('#skF_6', B_132))), inference(resolution, [status(thm)], [c_6, c_519])).
% 2.75/1.44  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.75/1.44  tff(c_528, plain, (![B_132]: (B_132='#skF_6' | ~r1_tarski(B_132, '#skF_6'))), inference(resolution, [status(thm)], [c_525, c_10])).
% 2.75/1.44  tff(c_572, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_565, c_528])).
% 2.75/1.44  tff(c_580, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_572, c_48])).
% 2.75/1.44  tff(c_602, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_600, c_580])).
% 2.75/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.75/1.44  
% 2.75/1.44  Inference rules
% 2.75/1.44  ----------------------
% 2.75/1.44  #Ref     : 1
% 2.75/1.44  #Sup     : 98
% 2.75/1.44  #Fact    : 0
% 2.75/1.44  #Define  : 0
% 2.75/1.44  #Split   : 6
% 2.75/1.44  #Chain   : 0
% 2.75/1.44  #Close   : 0
% 2.75/1.44  
% 2.75/1.44  Ordering : KBO
% 2.75/1.44  
% 2.75/1.44  Simplification rules
% 2.75/1.44  ----------------------
% 2.75/1.44  #Subsume      : 11
% 2.75/1.44  #Demod        : 121
% 2.75/1.44  #Tautology    : 60
% 2.75/1.44  #SimpNegUnit  : 2
% 2.75/1.44  #BackRed      : 33
% 2.75/1.44  
% 2.75/1.44  #Partial instantiations: 0
% 2.75/1.44  #Strategies tried      : 1
% 2.75/1.44  
% 2.75/1.44  Timing (in seconds)
% 2.75/1.44  ----------------------
% 2.75/1.44  Preprocessing        : 0.34
% 2.75/1.44  Parsing              : 0.17
% 2.75/1.44  CNF conversion       : 0.02
% 2.75/1.44  Main loop            : 0.33
% 2.75/1.44  Inferencing          : 0.12
% 2.75/1.44  Reduction            : 0.10
% 2.75/1.44  Demodulation         : 0.07
% 2.75/1.44  BG Simplification    : 0.02
% 2.75/1.44  Subsumption          : 0.06
% 2.75/1.44  Abstraction          : 0.02
% 2.75/1.44  MUC search           : 0.00
% 2.75/1.44  Cooper               : 0.00
% 2.75/1.44  Total                : 0.71
% 2.75/1.44  Index Insertion      : 0.00
% 2.75/1.44  Index Deletion       : 0.00
% 2.75/1.44  Index Matching       : 0.00
% 2.75/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
