%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:54 EST 2020

% Result     : Theorem 4.16s
% Output     : CNFRefutation 4.57s
% Verified   : 
% Statistics : Number of formulae       :  169 (1604 expanded)
%              Number of leaves         :   37 ( 505 expanded)
%              Depth                    :   17
%              Number of atoms          :  271 (3842 expanded)
%              Number of equality atoms :   83 (1233 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_130,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_117,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_xboole_0(C)
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_relset_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_106,axiom,(
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

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_65,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_74,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_70,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2632,plain,(
    ! [C_338,A_339,B_340] :
      ( m1_subset_1(C_338,k1_zfmisc_1(k2_zfmisc_1(A_339,B_340)))
      | ~ r1_tarski(k2_relat_1(C_338),B_340)
      | ~ r1_tarski(k1_relat_1(C_338),A_339)
      | ~ v1_relat_1(C_338) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_110,plain,(
    ! [A_37,B_38] : v1_xboole_0('#skF_2'(A_37,B_38)) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_114,plain,(
    ! [A_37,B_38] : '#skF_2'(A_37,B_38) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_110,c_6])).

tff(c_64,plain,(
    ! [A_27,B_28] : v1_xboole_0('#skF_2'(A_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_130,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_64])).

tff(c_18,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_295,plain,(
    ! [C_65,B_66,A_67] :
      ( ~ v1_xboole_0(C_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(C_65))
      | ~ r2_hidden(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_317,plain,(
    ! [B_70,A_71,A_72] :
      ( ~ v1_xboole_0(B_70)
      | ~ r2_hidden(A_71,A_72)
      | ~ r1_tarski(A_72,B_70) ) ),
    inference(resolution,[status(thm)],[c_22,c_295])).

tff(c_321,plain,(
    ! [B_73,A_74] :
      ( ~ v1_xboole_0(B_73)
      | ~ r1_tarski(A_74,B_73)
      | v1_xboole_0(A_74) ) ),
    inference(resolution,[status(thm)],[c_4,c_317])).

tff(c_343,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_70,c_321])).

tff(c_345,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_343])).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_68,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_76,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')))
    | ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68])).

tff(c_147,plain,(
    ~ v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_420,plain,(
    ! [C_87,A_88,B_89] :
      ( m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89)))
      | ~ r1_tarski(k2_relat_1(C_87),B_89)
      | ~ r1_tarski(k1_relat_1(C_87),A_88)
      | ~ v1_relat_1(C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_789,plain,(
    ! [C_133,A_134,B_135] :
      ( r1_tarski(C_133,k2_zfmisc_1(A_134,B_135))
      | ~ r1_tarski(k2_relat_1(C_133),B_135)
      | ~ r1_tarski(k1_relat_1(C_133),A_134)
      | ~ v1_relat_1(C_133) ) ),
    inference(resolution,[status(thm)],[c_420,c_20])).

tff(c_796,plain,(
    ! [A_134] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_134,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_134)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_70,c_789])).

tff(c_822,plain,(
    ! [A_138] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_138,'#skF_3'))
      | ~ r1_tarski(k1_relat_1('#skF_4'),A_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_796])).

tff(c_832,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_12,c_822])).

tff(c_396,plain,(
    ! [A_82,B_83,C_84] :
      ( k1_relset_1(A_82,B_83,C_84) = k1_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_412,plain,(
    ! [A_82,B_83,A_10] :
      ( k1_relset_1(A_82,B_83,A_10) = k1_relat_1(A_10)
      | ~ r1_tarski(A_10,k2_zfmisc_1(A_82,B_83)) ) ),
    inference(resolution,[status(thm)],[c_22,c_396])).

tff(c_841,plain,(
    k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_832,c_412])).

tff(c_570,plain,(
    ! [B_108,C_109,A_110] :
      ( k1_xboole_0 = B_108
      | v1_funct_2(C_109,A_110,B_108)
      | k1_relset_1(A_110,B_108,C_109) != A_110
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_110,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_948,plain,(
    ! [B_148,A_149,A_150] :
      ( k1_xboole_0 = B_148
      | v1_funct_2(A_149,A_150,B_148)
      | k1_relset_1(A_150,B_148,A_149) != A_150
      | ~ r1_tarski(A_149,k2_zfmisc_1(A_150,B_148)) ) ),
    inference(resolution,[status(thm)],[c_22,c_570])).

tff(c_954,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3')
    | k1_relset_1(k1_relat_1('#skF_4'),'#skF_3','#skF_4') != k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_832,c_948])).

tff(c_974,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4',k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_841,c_954])).

tff(c_975,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_974])).

tff(c_1024,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_975,c_130])).

tff(c_1035,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_345,c_1024])).

tff(c_1037,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_343])).

tff(c_1041,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1037,c_6])).

tff(c_173,plain,(
    ! [A_53] :
      ( k2_relat_1(A_53) = k1_xboole_0
      | k1_relat_1(A_53) != k1_xboole_0
      | ~ v1_relat_1(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_187,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_74,c_173])).

tff(c_188,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_187])).

tff(c_212,plain,(
    ! [A_58] :
      ( k1_relat_1(A_58) = k1_xboole_0
      | k2_relat_1(A_58) != k1_xboole_0
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_221,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_74,c_212])).

tff(c_228,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_221])).

tff(c_1047,plain,(
    k2_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1041,c_228])).

tff(c_1036,plain,(
    v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_343])).

tff(c_1118,plain,(
    ! [A_157] :
      ( A_157 = '#skF_3'
      | ~ v1_xboole_0(A_157) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1041,c_6])).

tff(c_1121,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1036,c_1118])).

tff(c_1128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1047,c_1121])).

tff(c_1130,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_1195,plain,(
    ! [A_165] :
      ( r1_tarski(A_165,k2_zfmisc_1(k1_relat_1(A_165),k2_relat_1(A_165)))
      | ~ v1_relat_1(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1200,plain,
    ( r1_tarski('#skF_4',k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_4')))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1130,c_1195])).

tff(c_1212,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_18,c_1200])).

tff(c_1262,plain,(
    ! [C_169,B_170,A_171] :
      ( ~ v1_xboole_0(C_169)
      | ~ m1_subset_1(B_170,k1_zfmisc_1(C_169))
      | ~ r2_hidden(A_171,B_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1284,plain,(
    ! [B_174,A_175,A_176] :
      ( ~ v1_xboole_0(B_174)
      | ~ r2_hidden(A_175,A_176)
      | ~ r1_tarski(A_176,B_174) ) ),
    inference(resolution,[status(thm)],[c_22,c_1262])).

tff(c_1288,plain,(
    ! [B_177,A_178] :
      ( ~ v1_xboole_0(B_177)
      | ~ r1_tarski(A_178,B_177)
      | v1_xboole_0(A_178) ) ),
    inference(resolution,[status(thm)],[c_4,c_1284])).

tff(c_1294,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1212,c_1288])).

tff(c_1312,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_1294])).

tff(c_1322,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1312,c_6])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1221,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_1212,c_8])).

tff(c_1223,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1221])).

tff(c_1328,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1322,c_1223])).

tff(c_1355,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1328])).

tff(c_1356,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1221])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1377,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1356,c_1356,c_30])).

tff(c_66,plain,(
    ! [A_27,B_28] : m1_subset_1('#skF_2'(A_27,B_28),k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1158,plain,(
    ! [A_27,B_28] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_66])).

tff(c_1362,plain,(
    ! [A_27,B_28] : m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1356,c_1158])).

tff(c_1561,plain,(
    ! [A_200,B_201,C_202] :
      ( k1_relset_1(A_200,B_201,C_202) = k1_relat_1(C_202)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1564,plain,(
    ! [A_27,B_28] : k1_relset_1(A_27,B_28,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1362,c_1561])).

tff(c_1576,plain,(
    ! [A_27,B_28] : k1_relset_1(A_27,B_28,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1377,c_1564])).

tff(c_52,plain,(
    ! [B_25,C_26,A_24] :
      ( k1_xboole_0 = B_25
      | v1_funct_2(C_26,A_24,B_25)
      | k1_relset_1(A_24,B_25,C_26) != A_24
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1723,plain,(
    ! [B_223,C_224,A_225] :
      ( B_223 = '#skF_4'
      | v1_funct_2(C_224,A_225,B_223)
      | k1_relset_1(A_225,B_223,C_224) != A_225
      | ~ m1_subset_1(C_224,k1_zfmisc_1(k2_zfmisc_1(A_225,B_223))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1356,c_52])).

tff(c_1729,plain,(
    ! [B_28,A_27] :
      ( B_28 = '#skF_4'
      | v1_funct_2('#skF_4',A_27,B_28)
      | k1_relset_1(A_27,B_28,'#skF_4') != A_27 ) ),
    inference(resolution,[status(thm)],[c_1362,c_1723])).

tff(c_1762,plain,(
    ! [B_228,A_229] :
      ( B_228 = '#skF_4'
      | v1_funct_2('#skF_4',A_229,B_228)
      | A_229 != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1576,c_1729])).

tff(c_1136,plain,(
    ~ v1_funct_2('#skF_4',k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1130,c_147])).

tff(c_1363,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1356,c_1136])).

tff(c_1779,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1762,c_1363])).

tff(c_1129,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_187])).

tff(c_1131,plain,(
    r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1129,c_70])).

tff(c_1168,plain,(
    ! [B_161,A_162] :
      ( B_161 = A_162
      | ~ r1_tarski(B_161,A_162)
      | ~ r1_tarski(A_162,B_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1173,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1131,c_1168])).

tff(c_1194,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1173])).

tff(c_1359,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1356,c_1194])).

tff(c_1781,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1779,c_1359])).

tff(c_1785,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1781])).

tff(c_1786,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1173])).

tff(c_1800,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1786,c_130])).

tff(c_1802,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_3',B_9) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1786,c_1786,c_18])).

tff(c_1794,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1786,c_1130])).

tff(c_1795,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1786,c_1129])).

tff(c_26,plain,(
    ! [A_15] :
      ( r1_tarski(A_15,k2_zfmisc_1(k1_relat_1(A_15),k2_relat_1(A_15)))
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1840,plain,
    ( r1_tarski('#skF_4',k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1795,c_26])).

tff(c_1844,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1794,c_1840])).

tff(c_1937,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1802,c_1844])).

tff(c_1849,plain,(
    ! [C_233,B_234,A_235] :
      ( ~ v1_xboole_0(C_233)
      | ~ m1_subset_1(B_234,k1_zfmisc_1(C_233))
      | ~ r2_hidden(A_235,B_234) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1999,plain,(
    ! [B_251,A_252,A_253] :
      ( ~ v1_xboole_0(B_251)
      | ~ r2_hidden(A_252,A_253)
      | ~ r1_tarski(A_253,B_251) ) ),
    inference(resolution,[status(thm)],[c_22,c_1849])).

tff(c_2003,plain,(
    ! [B_254,A_255] :
      ( ~ v1_xboole_0(B_254)
      | ~ r1_tarski(A_255,B_254)
      | v1_xboole_0(A_255) ) ),
    inference(resolution,[status(thm)],[c_4,c_1999])).

tff(c_2006,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1937,c_2003])).

tff(c_2018,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1800,c_2006])).

tff(c_1803,plain,(
    ! [A_5] :
      ( A_5 = '#skF_3'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1786,c_6])).

tff(c_2026,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2018,c_1803])).

tff(c_1940,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_1937,c_8])).

tff(c_1943,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1940])).

tff(c_2031,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2026,c_1943])).

tff(c_2055,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_2031])).

tff(c_2056,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1940])).

tff(c_2074,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2056,c_1794])).

tff(c_1790,plain,(
    ! [A_27,B_28] : m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1786,c_1158])).

tff(c_2201,plain,(
    ! [A_271,B_272] : m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_271,B_272))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2056,c_1790])).

tff(c_42,plain,(
    ! [A_18,B_19,C_20] :
      ( k1_relset_1(A_18,B_19,C_20) = k1_relat_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2204,plain,(
    ! [A_271,B_272] : k1_relset_1(A_271,B_272,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2201,c_42])).

tff(c_2215,plain,(
    ! [A_271,B_272] : k1_relset_1(A_271,B_272,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2074,c_2204])).

tff(c_1159,plain,(
    ! [A_159,B_160] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_66])).

tff(c_1164,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1159])).

tff(c_1789,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1786,c_1786,c_1164])).

tff(c_2063,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2056,c_2056,c_1789])).

tff(c_2078,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2056,c_1786])).

tff(c_50,plain,(
    ! [C_26,B_25] :
      ( v1_funct_2(C_26,k1_xboole_0,B_25)
      | k1_relset_1(k1_xboole_0,B_25,C_26) != k1_xboole_0
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_78,plain,(
    ! [C_26,B_25] :
      ( v1_funct_2(C_26,k1_xboole_0,B_25)
      | k1_relset_1(k1_xboole_0,B_25,C_26) != k1_xboole_0
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_50])).

tff(c_2331,plain,(
    ! [C_290,B_291] :
      ( v1_funct_2(C_290,'#skF_4',B_291)
      | k1_relset_1('#skF_4',B_291,C_290) != '#skF_4'
      | ~ m1_subset_1(C_290,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2078,c_2078,c_2078,c_2078,c_78])).

tff(c_2333,plain,(
    ! [B_291] :
      ( v1_funct_2('#skF_4','#skF_4',B_291)
      | k1_relset_1('#skF_4',B_291,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_2063,c_2331])).

tff(c_2339,plain,(
    ! [B_291] : v1_funct_2('#skF_4','#skF_4',B_291) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2215,c_2333])).

tff(c_1791,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1786,c_1136])).

tff(c_2066,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2056,c_2056,c_1791])).

tff(c_2343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2339,c_2066])).

tff(c_2344,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'),'#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_2643,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2632,c_2344])).

tff(c_2656,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_12,c_70,c_2643])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:39:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.16/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.16/1.75  
% 4.16/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.16/1.75  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 4.16/1.75  
% 4.16/1.75  %Foreground sorts:
% 4.16/1.75  
% 4.16/1.75  
% 4.16/1.75  %Background operators:
% 4.16/1.75  
% 4.16/1.75  
% 4.16/1.75  %Foreground operators:
% 4.16/1.75  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.16/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.16/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.16/1.75  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.16/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.16/1.75  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.16/1.75  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.16/1.75  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.16/1.75  tff('#skF_3', type, '#skF_3': $i).
% 4.16/1.75  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.16/1.75  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.16/1.75  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.16/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.16/1.75  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.16/1.75  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.16/1.75  tff('#skF_4', type, '#skF_4': $i).
% 4.16/1.75  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.16/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.16/1.75  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.16/1.75  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.16/1.75  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.16/1.75  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.16/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.16/1.75  
% 4.57/1.80  tff(f_130, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 4.57/1.80  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.57/1.80  tff(f_88, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 4.57/1.80  tff(f_117, axiom, (![A, B]: (?[C]: ((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_xboole_0(C)) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_relset_1)).
% 4.57/1.80  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 4.57/1.80  tff(f_47, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.57/1.80  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.57/1.80  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.57/1.80  tff(f_58, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 4.57/1.80  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.57/1.80  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 4.57/1.80  tff(f_71, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 4.57/1.80  tff(f_62, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 4.57/1.80  tff(f_65, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 4.57/1.80  tff(c_74, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.57/1.80  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.57/1.80  tff(c_70, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.57/1.80  tff(c_2632, plain, (![C_338, A_339, B_340]: (m1_subset_1(C_338, k1_zfmisc_1(k2_zfmisc_1(A_339, B_340))) | ~r1_tarski(k2_relat_1(C_338), B_340) | ~r1_tarski(k1_relat_1(C_338), A_339) | ~v1_relat_1(C_338))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.57/1.80  tff(c_110, plain, (![A_37, B_38]: (v1_xboole_0('#skF_2'(A_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.57/1.80  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.57/1.80  tff(c_114, plain, (![A_37, B_38]: ('#skF_2'(A_37, B_38)=k1_xboole_0)), inference(resolution, [status(thm)], [c_110, c_6])).
% 4.57/1.80  tff(c_64, plain, (![A_27, B_28]: (v1_xboole_0('#skF_2'(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.57/1.80  tff(c_130, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_114, c_64])).
% 4.57/1.80  tff(c_18, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.57/1.80  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.57/1.80  tff(c_22, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.57/1.80  tff(c_295, plain, (![C_65, B_66, A_67]: (~v1_xboole_0(C_65) | ~m1_subset_1(B_66, k1_zfmisc_1(C_65)) | ~r2_hidden(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.57/1.80  tff(c_317, plain, (![B_70, A_71, A_72]: (~v1_xboole_0(B_70) | ~r2_hidden(A_71, A_72) | ~r1_tarski(A_72, B_70))), inference(resolution, [status(thm)], [c_22, c_295])).
% 4.57/1.80  tff(c_321, plain, (![B_73, A_74]: (~v1_xboole_0(B_73) | ~r1_tarski(A_74, B_73) | v1_xboole_0(A_74))), inference(resolution, [status(thm)], [c_4, c_317])).
% 4.57/1.80  tff(c_343, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0(k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_70, c_321])).
% 4.57/1.80  tff(c_345, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_343])).
% 4.57/1.80  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.57/1.80  tff(c_68, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_130])).
% 4.57/1.80  tff(c_76, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))) | ~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68])).
% 4.57/1.80  tff(c_147, plain, (~v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_76])).
% 4.57/1.80  tff(c_420, plain, (![C_87, A_88, B_89]: (m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))) | ~r1_tarski(k2_relat_1(C_87), B_89) | ~r1_tarski(k1_relat_1(C_87), A_88) | ~v1_relat_1(C_87))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.57/1.80  tff(c_20, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.57/1.80  tff(c_789, plain, (![C_133, A_134, B_135]: (r1_tarski(C_133, k2_zfmisc_1(A_134, B_135)) | ~r1_tarski(k2_relat_1(C_133), B_135) | ~r1_tarski(k1_relat_1(C_133), A_134) | ~v1_relat_1(C_133))), inference(resolution, [status(thm)], [c_420, c_20])).
% 4.57/1.80  tff(c_796, plain, (![A_134]: (r1_tarski('#skF_4', k2_zfmisc_1(A_134, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_134) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_70, c_789])).
% 4.57/1.80  tff(c_822, plain, (![A_138]: (r1_tarski('#skF_4', k2_zfmisc_1(A_138, '#skF_3')) | ~r1_tarski(k1_relat_1('#skF_4'), A_138))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_796])).
% 4.57/1.80  tff(c_832, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3'))), inference(resolution, [status(thm)], [c_12, c_822])).
% 4.57/1.80  tff(c_396, plain, (![A_82, B_83, C_84]: (k1_relset_1(A_82, B_83, C_84)=k1_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.57/1.80  tff(c_412, plain, (![A_82, B_83, A_10]: (k1_relset_1(A_82, B_83, A_10)=k1_relat_1(A_10) | ~r1_tarski(A_10, k2_zfmisc_1(A_82, B_83)))), inference(resolution, [status(thm)], [c_22, c_396])).
% 4.57/1.80  tff(c_841, plain, (k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_832, c_412])).
% 4.57/1.80  tff(c_570, plain, (![B_108, C_109, A_110]: (k1_xboole_0=B_108 | v1_funct_2(C_109, A_110, B_108) | k1_relset_1(A_110, B_108, C_109)!=A_110 | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_110, B_108))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.57/1.80  tff(c_948, plain, (![B_148, A_149, A_150]: (k1_xboole_0=B_148 | v1_funct_2(A_149, A_150, B_148) | k1_relset_1(A_150, B_148, A_149)!=A_150 | ~r1_tarski(A_149, k2_zfmisc_1(A_150, B_148)))), inference(resolution, [status(thm)], [c_22, c_570])).
% 4.57/1.80  tff(c_954, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3') | k1_relset_1(k1_relat_1('#skF_4'), '#skF_3', '#skF_4')!=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_832, c_948])).
% 4.57/1.80  tff(c_974, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_841, c_954])).
% 4.57/1.80  tff(c_975, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_147, c_974])).
% 4.57/1.80  tff(c_1024, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_975, c_130])).
% 4.57/1.80  tff(c_1035, plain, $false, inference(negUnitSimplification, [status(thm)], [c_345, c_1024])).
% 4.57/1.80  tff(c_1037, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_343])).
% 4.57/1.80  tff(c_1041, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1037, c_6])).
% 4.57/1.80  tff(c_173, plain, (![A_53]: (k2_relat_1(A_53)=k1_xboole_0 | k1_relat_1(A_53)!=k1_xboole_0 | ~v1_relat_1(A_53))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.57/1.80  tff(c_187, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_74, c_173])).
% 4.57/1.80  tff(c_188, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_187])).
% 4.57/1.80  tff(c_212, plain, (![A_58]: (k1_relat_1(A_58)=k1_xboole_0 | k2_relat_1(A_58)!=k1_xboole_0 | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.57/1.80  tff(c_221, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_74, c_212])).
% 4.57/1.80  tff(c_228, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_188, c_221])).
% 4.57/1.80  tff(c_1047, plain, (k2_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1041, c_228])).
% 4.57/1.80  tff(c_1036, plain, (v1_xboole_0(k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_343])).
% 4.57/1.80  tff(c_1118, plain, (![A_157]: (A_157='#skF_3' | ~v1_xboole_0(A_157))), inference(demodulation, [status(thm), theory('equality')], [c_1041, c_6])).
% 4.57/1.80  tff(c_1121, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_1036, c_1118])).
% 4.57/1.80  tff(c_1128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1047, c_1121])).
% 4.57/1.80  tff(c_1130, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_187])).
% 4.57/1.80  tff(c_1195, plain, (![A_165]: (r1_tarski(A_165, k2_zfmisc_1(k1_relat_1(A_165), k2_relat_1(A_165))) | ~v1_relat_1(A_165))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.57/1.80  tff(c_1200, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_4'))) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1130, c_1195])).
% 4.57/1.80  tff(c_1212, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_74, c_18, c_1200])).
% 4.57/1.80  tff(c_1262, plain, (![C_169, B_170, A_171]: (~v1_xboole_0(C_169) | ~m1_subset_1(B_170, k1_zfmisc_1(C_169)) | ~r2_hidden(A_171, B_170))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.57/1.80  tff(c_1284, plain, (![B_174, A_175, A_176]: (~v1_xboole_0(B_174) | ~r2_hidden(A_175, A_176) | ~r1_tarski(A_176, B_174))), inference(resolution, [status(thm)], [c_22, c_1262])).
% 4.57/1.80  tff(c_1288, plain, (![B_177, A_178]: (~v1_xboole_0(B_177) | ~r1_tarski(A_178, B_177) | v1_xboole_0(A_178))), inference(resolution, [status(thm)], [c_4, c_1284])).
% 4.57/1.80  tff(c_1294, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1212, c_1288])).
% 4.57/1.80  tff(c_1312, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_1294])).
% 4.57/1.80  tff(c_1322, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1312, c_6])).
% 4.57/1.80  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.57/1.80  tff(c_1221, plain, (k1_xboole_0='#skF_4' | ~r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_1212, c_8])).
% 4.57/1.80  tff(c_1223, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(splitLeft, [status(thm)], [c_1221])).
% 4.57/1.80  tff(c_1328, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1322, c_1223])).
% 4.57/1.80  tff(c_1355, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_1328])).
% 4.57/1.80  tff(c_1356, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1221])).
% 4.57/1.80  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.57/1.80  tff(c_1377, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1356, c_1356, c_30])).
% 4.57/1.80  tff(c_66, plain, (![A_27, B_28]: (m1_subset_1('#skF_2'(A_27, B_28), k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 4.57/1.80  tff(c_1158, plain, (![A_27, B_28]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_66])).
% 4.57/1.80  tff(c_1362, plain, (![A_27, B_28]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(demodulation, [status(thm), theory('equality')], [c_1356, c_1158])).
% 4.57/1.80  tff(c_1561, plain, (![A_200, B_201, C_202]: (k1_relset_1(A_200, B_201, C_202)=k1_relat_1(C_202) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.57/1.80  tff(c_1564, plain, (![A_27, B_28]: (k1_relset_1(A_27, B_28, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1362, c_1561])).
% 4.57/1.80  tff(c_1576, plain, (![A_27, B_28]: (k1_relset_1(A_27, B_28, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1377, c_1564])).
% 4.57/1.80  tff(c_52, plain, (![B_25, C_26, A_24]: (k1_xboole_0=B_25 | v1_funct_2(C_26, A_24, B_25) | k1_relset_1(A_24, B_25, C_26)!=A_24 | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.57/1.80  tff(c_1723, plain, (![B_223, C_224, A_225]: (B_223='#skF_4' | v1_funct_2(C_224, A_225, B_223) | k1_relset_1(A_225, B_223, C_224)!=A_225 | ~m1_subset_1(C_224, k1_zfmisc_1(k2_zfmisc_1(A_225, B_223))))), inference(demodulation, [status(thm), theory('equality')], [c_1356, c_52])).
% 4.57/1.80  tff(c_1729, plain, (![B_28, A_27]: (B_28='#skF_4' | v1_funct_2('#skF_4', A_27, B_28) | k1_relset_1(A_27, B_28, '#skF_4')!=A_27)), inference(resolution, [status(thm)], [c_1362, c_1723])).
% 4.57/1.80  tff(c_1762, plain, (![B_228, A_229]: (B_228='#skF_4' | v1_funct_2('#skF_4', A_229, B_228) | A_229!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1576, c_1729])).
% 4.57/1.80  tff(c_1136, plain, (~v1_funct_2('#skF_4', k1_xboole_0, '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1130, c_147])).
% 4.57/1.80  tff(c_1363, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1356, c_1136])).
% 4.57/1.80  tff(c_1779, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_1762, c_1363])).
% 4.57/1.80  tff(c_1129, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_187])).
% 4.57/1.80  tff(c_1131, plain, (r1_tarski(k1_xboole_0, '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1129, c_70])).
% 4.57/1.80  tff(c_1168, plain, (![B_161, A_162]: (B_161=A_162 | ~r1_tarski(B_161, A_162) | ~r1_tarski(A_162, B_161))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.57/1.80  tff(c_1173, plain, (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_1131, c_1168])).
% 4.57/1.80  tff(c_1194, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1173])).
% 4.57/1.80  tff(c_1359, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1356, c_1194])).
% 4.57/1.80  tff(c_1781, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1779, c_1359])).
% 4.57/1.80  tff(c_1785, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_1781])).
% 4.57/1.80  tff(c_1786, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1173])).
% 4.57/1.80  tff(c_1800, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1786, c_130])).
% 4.57/1.80  tff(c_1802, plain, (![B_9]: (k2_zfmisc_1('#skF_3', B_9)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1786, c_1786, c_18])).
% 4.57/1.80  tff(c_1794, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1786, c_1130])).
% 4.57/1.80  tff(c_1795, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1786, c_1129])).
% 4.57/1.80  tff(c_26, plain, (![A_15]: (r1_tarski(A_15, k2_zfmisc_1(k1_relat_1(A_15), k2_relat_1(A_15))) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.57/1.80  tff(c_1840, plain, (r1_tarski('#skF_4', k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1795, c_26])).
% 4.57/1.80  tff(c_1844, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_3', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1794, c_1840])).
% 4.57/1.80  tff(c_1937, plain, (r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1802, c_1844])).
% 4.57/1.80  tff(c_1849, plain, (![C_233, B_234, A_235]: (~v1_xboole_0(C_233) | ~m1_subset_1(B_234, k1_zfmisc_1(C_233)) | ~r2_hidden(A_235, B_234))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.57/1.80  tff(c_1999, plain, (![B_251, A_252, A_253]: (~v1_xboole_0(B_251) | ~r2_hidden(A_252, A_253) | ~r1_tarski(A_253, B_251))), inference(resolution, [status(thm)], [c_22, c_1849])).
% 4.57/1.80  tff(c_2003, plain, (![B_254, A_255]: (~v1_xboole_0(B_254) | ~r1_tarski(A_255, B_254) | v1_xboole_0(A_255))), inference(resolution, [status(thm)], [c_4, c_1999])).
% 4.57/1.80  tff(c_2006, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1937, c_2003])).
% 4.57/1.80  tff(c_2018, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1800, c_2006])).
% 4.57/1.80  tff(c_1803, plain, (![A_5]: (A_5='#skF_3' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_1786, c_6])).
% 4.57/1.80  tff(c_2026, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_2018, c_1803])).
% 4.57/1.80  tff(c_1940, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_1937, c_8])).
% 4.57/1.80  tff(c_1943, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_1940])).
% 4.57/1.80  tff(c_2031, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2026, c_1943])).
% 4.57/1.80  tff(c_2055, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_2031])).
% 4.57/1.80  tff(c_2056, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_1940])).
% 4.57/1.80  tff(c_2074, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2056, c_1794])).
% 4.57/1.80  tff(c_1790, plain, (![A_27, B_28]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(demodulation, [status(thm), theory('equality')], [c_1786, c_1158])).
% 4.57/1.80  tff(c_2201, plain, (![A_271, B_272]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_271, B_272))))), inference(demodulation, [status(thm), theory('equality')], [c_2056, c_1790])).
% 4.57/1.80  tff(c_42, plain, (![A_18, B_19, C_20]: (k1_relset_1(A_18, B_19, C_20)=k1_relat_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.57/1.80  tff(c_2204, plain, (![A_271, B_272]: (k1_relset_1(A_271, B_272, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_2201, c_42])).
% 4.57/1.80  tff(c_2215, plain, (![A_271, B_272]: (k1_relset_1(A_271, B_272, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2074, c_2204])).
% 4.57/1.80  tff(c_1159, plain, (![A_159, B_160]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_66])).
% 4.57/1.80  tff(c_1164, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1159])).
% 4.57/1.80  tff(c_1789, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1786, c_1786, c_1164])).
% 4.57/1.80  tff(c_2063, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2056, c_2056, c_1789])).
% 4.57/1.80  tff(c_2078, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2056, c_1786])).
% 4.57/1.80  tff(c_50, plain, (![C_26, B_25]: (v1_funct_2(C_26, k1_xboole_0, B_25) | k1_relset_1(k1_xboole_0, B_25, C_26)!=k1_xboole_0 | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_25))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.57/1.80  tff(c_78, plain, (![C_26, B_25]: (v1_funct_2(C_26, k1_xboole_0, B_25) | k1_relset_1(k1_xboole_0, B_25, C_26)!=k1_xboole_0 | ~m1_subset_1(C_26, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_50])).
% 4.57/1.80  tff(c_2331, plain, (![C_290, B_291]: (v1_funct_2(C_290, '#skF_4', B_291) | k1_relset_1('#skF_4', B_291, C_290)!='#skF_4' | ~m1_subset_1(C_290, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2078, c_2078, c_2078, c_2078, c_78])).
% 4.57/1.80  tff(c_2333, plain, (![B_291]: (v1_funct_2('#skF_4', '#skF_4', B_291) | k1_relset_1('#skF_4', B_291, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_2063, c_2331])).
% 4.57/1.80  tff(c_2339, plain, (![B_291]: (v1_funct_2('#skF_4', '#skF_4', B_291))), inference(demodulation, [status(thm), theory('equality')], [c_2215, c_2333])).
% 4.57/1.80  tff(c_1791, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1786, c_1136])).
% 4.57/1.80  tff(c_2066, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2056, c_2056, c_1791])).
% 4.57/1.80  tff(c_2343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2339, c_2066])).
% 4.57/1.80  tff(c_2344, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_4'), '#skF_3')))), inference(splitRight, [status(thm)], [c_76])).
% 4.57/1.80  tff(c_2643, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2632, c_2344])).
% 4.57/1.80  tff(c_2656, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_12, c_70, c_2643])).
% 4.57/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.57/1.80  
% 4.57/1.80  Inference rules
% 4.57/1.80  ----------------------
% 4.57/1.80  #Ref     : 0
% 4.57/1.80  #Sup     : 517
% 4.57/1.80  #Fact    : 0
% 4.57/1.80  #Define  : 0
% 4.57/1.80  #Split   : 15
% 4.57/1.80  #Chain   : 0
% 4.57/1.80  #Close   : 0
% 4.57/1.80  
% 4.57/1.80  Ordering : KBO
% 4.57/1.80  
% 4.57/1.80  Simplification rules
% 4.57/1.80  ----------------------
% 4.57/1.80  #Subsume      : 35
% 4.57/1.80  #Demod        : 831
% 4.57/1.80  #Tautology    : 330
% 4.57/1.80  #SimpNegUnit  : 5
% 4.57/1.80  #BackRed      : 208
% 4.57/1.80  
% 4.57/1.80  #Partial instantiations: 0
% 4.57/1.80  #Strategies tried      : 1
% 4.57/1.80  
% 4.57/1.80  Timing (in seconds)
% 4.57/1.80  ----------------------
% 4.57/1.80  Preprocessing        : 0.34
% 4.57/1.80  Parsing              : 0.17
% 4.57/1.80  CNF conversion       : 0.02
% 4.57/1.80  Main loop            : 0.65
% 4.57/1.81  Inferencing          : 0.22
% 4.57/1.81  Reduction            : 0.22
% 4.57/1.81  Demodulation         : 0.16
% 4.57/1.81  BG Simplification    : 0.03
% 4.57/1.81  Subsumption          : 0.11
% 4.57/1.81  Abstraction          : 0.03
% 4.57/1.81  MUC search           : 0.00
% 4.57/1.81  Cooper               : 0.00
% 4.57/1.81  Total                : 1.08
% 4.57/1.81  Index Insertion      : 0.00
% 4.57/1.81  Index Deletion       : 0.00
% 4.57/1.81  Index Matching       : 0.00
% 4.57/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
