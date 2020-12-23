%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:36 EST 2020

% Result     : Theorem 4.13s
% Output     : CNFRefutation 4.13s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 423 expanded)
%              Number of leaves         :   36 ( 158 expanded)
%              Depth                    :   11
%              Number of atoms          :  179 (1179 expanded)
%              Number of equality atoms :   58 ( 239 expanded)
%              Maximal formula depth    :   11 (   4 average)
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

tff(f_139,negated_conjecture,(
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

tff(f_88,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_118,axiom,(
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

tff(f_77,axiom,(
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

tff(f_53,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_66,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_487,plain,(
    ! [C_109,B_110,A_111] :
      ( v1_xboole_0(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(B_110,A_111)))
      | ~ v1_xboole_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_504,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_487])).

tff(c_520,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_504])).

tff(c_569,plain,(
    ! [A_122,B_123,D_124] :
      ( r2_relset_1(A_122,B_123,D_124,D_124)
      | ~ m1_subset_1(D_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_585,plain,(
    r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_569])).

tff(c_60,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_108,plain,(
    ! [C_54,A_55,B_56] :
      ( v1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_124,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_108])).

tff(c_64,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_62,plain,(
    v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_644,plain,(
    ! [A_133,B_134,C_135] :
      ( k1_relset_1(A_133,B_134,C_135) = k1_relat_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_667,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_644])).

tff(c_813,plain,(
    ! [B_152,A_153,C_154] :
      ( k1_xboole_0 = B_152
      | k1_relset_1(A_153,B_152,C_154) = A_153
      | ~ v1_funct_2(C_154,A_153,B_152)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_153,B_152))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_827,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_7') = '#skF_4'
    | ~ v1_funct_2('#skF_7','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_813])).

tff(c_845,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_7') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_667,c_827])).

tff(c_855,plain,(
    k1_relat_1('#skF_7') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_845])).

tff(c_123,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_108])).

tff(c_70,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_68,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_666,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_644])).

tff(c_824,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_813])).

tff(c_842,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_666,c_824])).

tff(c_849,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_842])).

tff(c_1137,plain,(
    ! [A_184,B_185] :
      ( r2_hidden('#skF_3'(A_184,B_185),k1_relat_1(A_184))
      | B_185 = A_184
      | k1_relat_1(B_185) != k1_relat_1(A_184)
      | ~ v1_funct_1(B_185)
      | ~ v1_relat_1(B_185)
      | ~ v1_funct_1(A_184)
      | ~ v1_relat_1(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1148,plain,(
    ! [B_185] :
      ( r2_hidden('#skF_3'('#skF_6',B_185),'#skF_4')
      | B_185 = '#skF_6'
      | k1_relat_1(B_185) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_185)
      | ~ v1_relat_1(B_185)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_849,c_1137])).

tff(c_1818,plain,(
    ! [B_234] :
      ( r2_hidden('#skF_3'('#skF_6',B_234),'#skF_4')
      | B_234 = '#skF_6'
      | k1_relat_1(B_234) != '#skF_4'
      | ~ v1_funct_1(B_234)
      | ~ v1_relat_1(B_234) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_70,c_849,c_1148])).

tff(c_58,plain,(
    ! [E_45] :
      ( k1_funct_1('#skF_7',E_45) = k1_funct_1('#skF_6',E_45)
      | ~ r2_hidden(E_45,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1843,plain,(
    ! [B_236] :
      ( k1_funct_1('#skF_7','#skF_3'('#skF_6',B_236)) = k1_funct_1('#skF_6','#skF_3'('#skF_6',B_236))
      | B_236 = '#skF_6'
      | k1_relat_1(B_236) != '#skF_4'
      | ~ v1_funct_1(B_236)
      | ~ v1_relat_1(B_236) ) ),
    inference(resolution,[status(thm)],[c_1818,c_58])).

tff(c_30,plain,(
    ! [B_22,A_18] :
      ( k1_funct_1(B_22,'#skF_3'(A_18,B_22)) != k1_funct_1(A_18,'#skF_3'(A_18,B_22))
      | B_22 = A_18
      | k1_relat_1(B_22) != k1_relat_1(A_18)
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1850,plain,
    ( k1_relat_1('#skF_7') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_7' = '#skF_6'
    | k1_relat_1('#skF_7') != '#skF_4'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1843,c_30])).

tff(c_1857,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_64,c_855,c_123,c_70,c_849,c_855,c_1850])).

tff(c_56,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1873,plain,(
    ~ r2_relset_1('#skF_4','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1857,c_56])).

tff(c_1883,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_585,c_1873])).

tff(c_1884,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_845])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1912,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1884,c_12])).

tff(c_1914,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_520,c_1912])).

tff(c_1915,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_842])).

tff(c_1943,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1915,c_12])).

tff(c_1945,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_520,c_1943])).

tff(c_1946,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_504])).

tff(c_158,plain,(
    ! [A_65,B_66] :
      ( r2_hidden('#skF_2'(A_65,B_66),A_65)
      | r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_173,plain,(
    ! [A_65,B_66] :
      ( ~ v1_xboole_0(A_65)
      | r1_tarski(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_158,c_2])).

tff(c_174,plain,(
    ! [A_67,B_68] :
      ( ~ v1_xboole_0(A_67)
      | r1_tarski(A_67,B_68) ) ),
    inference(resolution,[status(thm)],[c_158,c_2])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_178,plain,(
    ! [B_69,A_70] :
      ( B_69 = A_70
      | ~ r1_tarski(B_69,A_70)
      | ~ v1_xboole_0(A_70) ) ),
    inference(resolution,[status(thm)],[c_174,c_14])).

tff(c_188,plain,(
    ! [B_71,A_72] :
      ( B_71 = A_72
      | ~ v1_xboole_0(B_71)
      | ~ v1_xboole_0(A_72) ) ),
    inference(resolution,[status(thm)],[c_173,c_178])).

tff(c_191,plain,(
    ! [A_72] :
      ( k1_xboole_0 = A_72
      | ~ v1_xboole_0(A_72) ) ),
    inference(resolution,[status(thm)],[c_12,c_188])).

tff(c_1953,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1946,c_191])).

tff(c_26,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1962,plain,(
    ! [A_237,B_238,D_239] :
      ( r2_relset_1(A_237,B_238,D_239,D_239)
      | ~ m1_subset_1(D_239,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1976,plain,(
    ! [A_237,B_238] : r2_relset_1(A_237,B_238,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_1962])).

tff(c_2104,plain,(
    ! [A_237,B_238] : r2_relset_1(A_237,B_238,'#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1953,c_1953,c_1976])).

tff(c_1947,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_504])).

tff(c_1960,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1947,c_191])).

tff(c_1992,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1953,c_1960])).

tff(c_505,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_60,c_487])).

tff(c_2005,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1946,c_1992,c_505])).

tff(c_185,plain,(
    ! [B_66,A_65] :
      ( B_66 = A_65
      | ~ v1_xboole_0(B_66)
      | ~ v1_xboole_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_173,c_178])).

tff(c_1961,plain,(
    ! [A_65] :
      ( A_65 = '#skF_5'
      | ~ v1_xboole_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_1947,c_185])).

tff(c_2010,plain,(
    ! [A_240] :
      ( A_240 = '#skF_6'
      | ~ v1_xboole_0(A_240) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1992,c_1961])).

tff(c_2017,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2005,c_2010])).

tff(c_1996,plain,(
    ~ r2_relset_1('#skF_4','#skF_6','#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1992,c_56])).

tff(c_2108,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2104,c_2017,c_1996])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:56:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.13/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.13/1.69  
% 4.13/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.13/1.69  %$ r2_relset_1 > v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 4.13/1.69  
% 4.13/1.69  %Foreground sorts:
% 4.13/1.69  
% 4.13/1.69  
% 4.13/1.69  %Background operators:
% 4.13/1.69  
% 4.13/1.69  
% 4.13/1.69  %Foreground operators:
% 4.13/1.69  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.13/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.13/1.69  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.13/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.13/1.69  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.13/1.69  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.13/1.69  tff('#skF_7', type, '#skF_7': $i).
% 4.13/1.69  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.13/1.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.13/1.69  tff('#skF_5', type, '#skF_5': $i).
% 4.13/1.69  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.13/1.69  tff('#skF_6', type, '#skF_6': $i).
% 4.13/1.69  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.13/1.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.13/1.69  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.13/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.13/1.69  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.13/1.69  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.13/1.69  tff('#skF_4', type, '#skF_4': $i).
% 4.13/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.13/1.69  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.13/1.69  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.13/1.69  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.13/1.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.13/1.69  
% 4.13/1.72  tff(f_139, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (r2_hidden(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_2)).
% 4.13/1.72  tff(f_88, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 4.13/1.72  tff(f_100, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.13/1.72  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.13/1.72  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.13/1.72  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.13/1.72  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 4.13/1.72  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.13/1.72  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.13/1.72  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.13/1.72  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.13/1.72  tff(f_53, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.13/1.72  tff(c_66, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.13/1.72  tff(c_487, plain, (![C_109, B_110, A_111]: (v1_xboole_0(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(B_110, A_111))) | ~v1_xboole_0(A_111))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.13/1.72  tff(c_504, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_66, c_487])).
% 4.13/1.72  tff(c_520, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_504])).
% 4.13/1.72  tff(c_569, plain, (![A_122, B_123, D_124]: (r2_relset_1(A_122, B_123, D_124, D_124) | ~m1_subset_1(D_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.13/1.72  tff(c_585, plain, (r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_66, c_569])).
% 4.13/1.72  tff(c_60, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.13/1.72  tff(c_108, plain, (![C_54, A_55, B_56]: (v1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.13/1.72  tff(c_124, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_60, c_108])).
% 4.13/1.72  tff(c_64, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.13/1.72  tff(c_62, plain, (v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.13/1.72  tff(c_644, plain, (![A_133, B_134, C_135]: (k1_relset_1(A_133, B_134, C_135)=k1_relat_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.13/1.72  tff(c_667, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_60, c_644])).
% 4.13/1.72  tff(c_813, plain, (![B_152, A_153, C_154]: (k1_xboole_0=B_152 | k1_relset_1(A_153, B_152, C_154)=A_153 | ~v1_funct_2(C_154, A_153, B_152) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_153, B_152))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.13/1.72  tff(c_827, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_7')='#skF_4' | ~v1_funct_2('#skF_7', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_60, c_813])).
% 4.13/1.72  tff(c_845, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_7')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_667, c_827])).
% 4.13/1.72  tff(c_855, plain, (k1_relat_1('#skF_7')='#skF_4'), inference(splitLeft, [status(thm)], [c_845])).
% 4.13/1.72  tff(c_123, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_108])).
% 4.13/1.72  tff(c_70, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.13/1.72  tff(c_68, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.13/1.72  tff(c_666, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_644])).
% 4.13/1.72  tff(c_824, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_66, c_813])).
% 4.13/1.72  tff(c_842, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_666, c_824])).
% 4.13/1.72  tff(c_849, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_842])).
% 4.13/1.72  tff(c_1137, plain, (![A_184, B_185]: (r2_hidden('#skF_3'(A_184, B_185), k1_relat_1(A_184)) | B_185=A_184 | k1_relat_1(B_185)!=k1_relat_1(A_184) | ~v1_funct_1(B_185) | ~v1_relat_1(B_185) | ~v1_funct_1(A_184) | ~v1_relat_1(A_184))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.13/1.72  tff(c_1148, plain, (![B_185]: (r2_hidden('#skF_3'('#skF_6', B_185), '#skF_4') | B_185='#skF_6' | k1_relat_1(B_185)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_185) | ~v1_relat_1(B_185) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_849, c_1137])).
% 4.13/1.72  tff(c_1818, plain, (![B_234]: (r2_hidden('#skF_3'('#skF_6', B_234), '#skF_4') | B_234='#skF_6' | k1_relat_1(B_234)!='#skF_4' | ~v1_funct_1(B_234) | ~v1_relat_1(B_234))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_70, c_849, c_1148])).
% 4.13/1.72  tff(c_58, plain, (![E_45]: (k1_funct_1('#skF_7', E_45)=k1_funct_1('#skF_6', E_45) | ~r2_hidden(E_45, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.13/1.72  tff(c_1843, plain, (![B_236]: (k1_funct_1('#skF_7', '#skF_3'('#skF_6', B_236))=k1_funct_1('#skF_6', '#skF_3'('#skF_6', B_236)) | B_236='#skF_6' | k1_relat_1(B_236)!='#skF_4' | ~v1_funct_1(B_236) | ~v1_relat_1(B_236))), inference(resolution, [status(thm)], [c_1818, c_58])).
% 4.13/1.72  tff(c_30, plain, (![B_22, A_18]: (k1_funct_1(B_22, '#skF_3'(A_18, B_22))!=k1_funct_1(A_18, '#skF_3'(A_18, B_22)) | B_22=A_18 | k1_relat_1(B_22)!=k1_relat_1(A_18) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.13/1.72  tff(c_1850, plain, (k1_relat_1('#skF_7')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_7'='#skF_6' | k1_relat_1('#skF_7')!='#skF_4' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1843, c_30])).
% 4.13/1.72  tff(c_1857, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_64, c_855, c_123, c_70, c_849, c_855, c_1850])).
% 4.13/1.72  tff(c_56, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.13/1.72  tff(c_1873, plain, (~r2_relset_1('#skF_4', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1857, c_56])).
% 4.13/1.72  tff(c_1883, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_585, c_1873])).
% 4.13/1.72  tff(c_1884, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_845])).
% 4.13/1.72  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.13/1.72  tff(c_1912, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1884, c_12])).
% 4.13/1.72  tff(c_1914, plain, $false, inference(negUnitSimplification, [status(thm)], [c_520, c_1912])).
% 4.13/1.72  tff(c_1915, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_842])).
% 4.13/1.72  tff(c_1943, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1915, c_12])).
% 4.13/1.72  tff(c_1945, plain, $false, inference(negUnitSimplification, [status(thm)], [c_520, c_1943])).
% 4.13/1.72  tff(c_1946, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_504])).
% 4.13/1.72  tff(c_158, plain, (![A_65, B_66]: (r2_hidden('#skF_2'(A_65, B_66), A_65) | r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.13/1.72  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.13/1.72  tff(c_173, plain, (![A_65, B_66]: (~v1_xboole_0(A_65) | r1_tarski(A_65, B_66))), inference(resolution, [status(thm)], [c_158, c_2])).
% 4.13/1.72  tff(c_174, plain, (![A_67, B_68]: (~v1_xboole_0(A_67) | r1_tarski(A_67, B_68))), inference(resolution, [status(thm)], [c_158, c_2])).
% 4.13/1.72  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.13/1.72  tff(c_178, plain, (![B_69, A_70]: (B_69=A_70 | ~r1_tarski(B_69, A_70) | ~v1_xboole_0(A_70))), inference(resolution, [status(thm)], [c_174, c_14])).
% 4.13/1.72  tff(c_188, plain, (![B_71, A_72]: (B_71=A_72 | ~v1_xboole_0(B_71) | ~v1_xboole_0(A_72))), inference(resolution, [status(thm)], [c_173, c_178])).
% 4.13/1.72  tff(c_191, plain, (![A_72]: (k1_xboole_0=A_72 | ~v1_xboole_0(A_72))), inference(resolution, [status(thm)], [c_12, c_188])).
% 4.13/1.72  tff(c_1953, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_1946, c_191])).
% 4.13/1.72  tff(c_26, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.13/1.72  tff(c_1962, plain, (![A_237, B_238, D_239]: (r2_relset_1(A_237, B_238, D_239, D_239) | ~m1_subset_1(D_239, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.13/1.72  tff(c_1976, plain, (![A_237, B_238]: (r2_relset_1(A_237, B_238, k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_1962])).
% 4.13/1.72  tff(c_2104, plain, (![A_237, B_238]: (r2_relset_1(A_237, B_238, '#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1953, c_1953, c_1976])).
% 4.13/1.72  tff(c_1947, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_504])).
% 4.13/1.72  tff(c_1960, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_1947, c_191])).
% 4.13/1.72  tff(c_1992, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1953, c_1960])).
% 4.13/1.72  tff(c_505, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_60, c_487])).
% 4.13/1.72  tff(c_2005, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1946, c_1992, c_505])).
% 4.13/1.72  tff(c_185, plain, (![B_66, A_65]: (B_66=A_65 | ~v1_xboole_0(B_66) | ~v1_xboole_0(A_65))), inference(resolution, [status(thm)], [c_173, c_178])).
% 4.13/1.72  tff(c_1961, plain, (![A_65]: (A_65='#skF_5' | ~v1_xboole_0(A_65))), inference(resolution, [status(thm)], [c_1947, c_185])).
% 4.13/1.72  tff(c_2010, plain, (![A_240]: (A_240='#skF_6' | ~v1_xboole_0(A_240))), inference(demodulation, [status(thm), theory('equality')], [c_1992, c_1961])).
% 4.13/1.72  tff(c_2017, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_2005, c_2010])).
% 4.13/1.72  tff(c_1996, plain, (~r2_relset_1('#skF_4', '#skF_6', '#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1992, c_56])).
% 4.13/1.72  tff(c_2108, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2104, c_2017, c_1996])).
% 4.13/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.13/1.72  
% 4.13/1.72  Inference rules
% 4.13/1.72  ----------------------
% 4.13/1.72  #Ref     : 1
% 4.13/1.72  #Sup     : 416
% 4.13/1.72  #Fact    : 0
% 4.13/1.72  #Define  : 0
% 4.13/1.72  #Split   : 11
% 4.13/1.72  #Chain   : 0
% 4.13/1.72  #Close   : 0
% 4.13/1.72  
% 4.13/1.72  Ordering : KBO
% 4.13/1.72  
% 4.13/1.72  Simplification rules
% 4.13/1.72  ----------------------
% 4.13/1.72  #Subsume      : 108
% 4.13/1.72  #Demod        : 429
% 4.13/1.72  #Tautology    : 236
% 4.13/1.72  #SimpNegUnit  : 24
% 4.13/1.72  #BackRed      : 123
% 4.13/1.72  
% 4.13/1.72  #Partial instantiations: 0
% 4.13/1.72  #Strategies tried      : 1
% 4.13/1.72  
% 4.13/1.72  Timing (in seconds)
% 4.13/1.72  ----------------------
% 4.13/1.72  Preprocessing        : 0.34
% 4.13/1.72  Parsing              : 0.18
% 4.13/1.72  CNF conversion       : 0.02
% 4.13/1.72  Main loop            : 0.60
% 4.13/1.72  Inferencing          : 0.19
% 4.13/1.72  Reduction            : 0.19
% 4.13/1.72  Demodulation         : 0.13
% 4.13/1.72  BG Simplification    : 0.03
% 4.13/1.72  Subsumption          : 0.13
% 4.13/1.72  Abstraction          : 0.03
% 4.13/1.72  MUC search           : 0.00
% 4.13/1.72  Cooper               : 0.00
% 4.13/1.72  Total                : 0.99
% 4.13/1.72  Index Insertion      : 0.00
% 4.13/1.72  Index Deletion       : 0.00
% 4.13/1.72  Index Matching       : 0.00
% 4.13/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
