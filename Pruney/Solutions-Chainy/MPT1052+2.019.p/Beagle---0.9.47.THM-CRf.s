%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:11 EST 2020

% Result     : Theorem 12.80s
% Output     : CNFRefutation 13.01s
% Verified   : 
% Statistics : Number of formulae       :  272 (1715 expanded)
%              Number of leaves         :   46 ( 594 expanded)
%              Depth                    :   17
%              Number of atoms          :  521 (3583 expanded)
%              Number of equality atoms :  243 (1287 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_relset_1 > k4_xboole_0 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k3_partfun1,type,(
    k3_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

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

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_159,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(C,k1_funct_2(A,B))
         => ( k1_relat_1(C) = A
            & r1_tarski(k2_relat_1(C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_funct_2)).

tff(f_37,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_109,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_103,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_100,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_146,axiom,(
    ! [A,B,C] :
      ( r2_hidden(C,k1_funct_2(A,B))
     => ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_89,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_138,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & v1_xboole_0(B) )
     => v1_xboole_0(k1_funct_2(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_2)).

tff(f_131,axiom,(
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

tff(f_113,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_61,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_84,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_8,plain,(
    v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_126,plain,(
    ! [A_46] :
      ( k1_xboole_0 = A_46
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_130,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_126])).

tff(c_52,plain,(
    ! [A_27] :
      ( k2_relat_1(A_27) = k1_xboole_0
      | k1_relat_1(A_27) != k1_xboole_0
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_239,plain,(
    ! [A_70] :
      ( k2_relat_1(A_70) = '#skF_2'
      | k1_relat_1(A_70) != '#skF_2'
      | ~ v1_relat_1(A_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_130,c_52])).

tff(c_253,plain,
    ( k2_relat_1('#skF_6') = '#skF_2'
    | k1_relat_1('#skF_6') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_84,c_239])).

tff(c_269,plain,(
    k1_relat_1('#skF_6') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_253])).

tff(c_287,plain,(
    ! [A_79,B_80] :
      ( r2_hidden('#skF_3'(A_79,B_80),B_80)
      | r1_xboole_0(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_297,plain,(
    ! [B_81,A_82] :
      ( ~ v1_xboole_0(B_81)
      | r1_xboole_0(A_82,B_81) ) ),
    inference(resolution,[status(thm)],[c_287,c_2])).

tff(c_22,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = A_14
      | ~ r1_xboole_0(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_302,plain,(
    ! [A_83,B_84] :
      ( k4_xboole_0(A_83,B_84) = A_83
      | ~ v1_xboole_0(B_84) ) ),
    inference(resolution,[status(thm)],[c_297,c_22])).

tff(c_305,plain,(
    ! [A_83] : k4_xboole_0(A_83,'#skF_2') = A_83 ),
    inference(resolution,[status(thm)],[c_8,c_302])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | k4_xboole_0(A_11,B_12) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_216,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | k4_xboole_0(A_11,B_12) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_16])).

tff(c_30,plain,(
    ! [B_17] : k2_zfmisc_1(k1_xboole_0,B_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_120,plain,(
    ! [A_44,B_45] : v1_relat_1(k2_zfmisc_1(A_44,B_45)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_122,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_120])).

tff(c_132,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_122])).

tff(c_48,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_136,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_130,c_48])).

tff(c_991,plain,(
    ! [A_155,B_156] :
      ( r1_tarski(k1_relat_1(A_155),k1_relat_1(B_156))
      | ~ r1_tarski(A_155,B_156)
      | ~ v1_relat_1(B_156)
      | ~ v1_relat_1(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1006,plain,(
    ! [A_155] :
      ( r1_tarski(k1_relat_1(A_155),'#skF_2')
      | ~ r1_tarski(A_155,'#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(A_155) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_991])).

tff(c_1016,plain,(
    ! [A_157] :
      ( r1_tarski(k1_relat_1(A_157),'#skF_2')
      | ~ r1_tarski(A_157,'#skF_2')
      | ~ v1_relat_1(A_157) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_1006])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = k1_xboole_0
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_203,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = '#skF_2'
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_18])).

tff(c_1021,plain,(
    ! [A_157] :
      ( k4_xboole_0(k1_relat_1(A_157),'#skF_2') = '#skF_2'
      | ~ r1_tarski(A_157,'#skF_2')
      | ~ v1_relat_1(A_157) ) ),
    inference(resolution,[status(thm)],[c_1016,c_203])).

tff(c_1035,plain,(
    ! [A_158] :
      ( k1_relat_1(A_158) = '#skF_2'
      | ~ r1_tarski(A_158,'#skF_2')
      | ~ v1_relat_1(A_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_1021])).

tff(c_1048,plain,(
    ! [A_11] :
      ( k1_relat_1(A_11) = '#skF_2'
      | ~ v1_relat_1(A_11)
      | k4_xboole_0(A_11,'#skF_2') != '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_216,c_1035])).

tff(c_1062,plain,(
    ! [A_159] :
      ( k1_relat_1(A_159) = '#skF_2'
      | ~ v1_relat_1(A_159)
      | A_159 != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_1048])).

tff(c_1071,plain,
    ( k1_relat_1('#skF_6') = '#skF_2'
    | '#skF_6' != '#skF_2' ),
    inference(resolution,[status(thm)],[c_84,c_1062])).

tff(c_1077,plain,(
    '#skF_6' != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_269,c_1071])).

tff(c_28,plain,(
    ! [A_16] : k2_zfmisc_1(A_16,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_134,plain,(
    ! [A_16] : k2_zfmisc_1(A_16,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_130,c_28])).

tff(c_78,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
    | k1_relat_1('#skF_6') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_156,plain,(
    k1_relat_1('#skF_6') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_80,plain,(
    r2_hidden('#skF_6',k1_funct_2('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_654,plain,(
    ! [C_118,A_119,B_120] :
      ( m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120)))
      | ~ r2_hidden(C_118,k1_funct_2(A_119,B_120)) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_32,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_777,plain,(
    ! [C_135,A_136,B_137] :
      ( r1_tarski(C_135,k2_zfmisc_1(A_136,B_137))
      | ~ r2_hidden(C_135,k1_funct_2(A_136,B_137)) ) ),
    inference(resolution,[status(thm)],[c_654,c_32])).

tff(c_808,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_80,c_777])).

tff(c_36,plain,(
    ! [A_20,B_21] : v1_relat_1(k2_zfmisc_1(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_40,plain,(
    ! [A_22,B_23] :
      ( k1_relat_1(k2_zfmisc_1(A_22,B_23)) = A_22
      | k1_xboole_0 = B_23
      | k1_xboole_0 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_580,plain,(
    ! [A_22,B_23] :
      ( k1_relat_1(k2_zfmisc_1(A_22,B_23)) = A_22
      | B_23 = '#skF_2'
      | A_22 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_130,c_40])).

tff(c_1000,plain,(
    ! [A_155,A_22,B_23] :
      ( r1_tarski(k1_relat_1(A_155),A_22)
      | ~ r1_tarski(A_155,k2_zfmisc_1(A_22,B_23))
      | ~ v1_relat_1(k2_zfmisc_1(A_22,B_23))
      | ~ v1_relat_1(A_155)
      | B_23 = '#skF_2'
      | A_22 = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_580,c_991])).

tff(c_6740,plain,(
    ! [A_409,A_410,B_411] :
      ( r1_tarski(k1_relat_1(A_409),A_410)
      | ~ r1_tarski(A_409,k2_zfmisc_1(A_410,B_411))
      | ~ v1_relat_1(A_409)
      | B_411 = '#skF_2'
      | A_410 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1000])).

tff(c_6754,plain,
    ( r1_tarski(k1_relat_1('#skF_6'),'#skF_4')
    | ~ v1_relat_1('#skF_6')
    | '#skF_5' = '#skF_2'
    | '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_808,c_6740])).

tff(c_6776,plain,
    ( r1_tarski(k1_relat_1('#skF_6'),'#skF_4')
    | '#skF_5' = '#skF_2'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_6754])).

tff(c_6782,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_6776])).

tff(c_6875,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6782,c_1077])).

tff(c_6911,plain,(
    ! [A_83] : k4_xboole_0(A_83,'#skF_4') = A_83 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6782,c_305])).

tff(c_133,plain,(
    ! [B_17] : k2_zfmisc_1('#skF_2',B_17) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_130,c_30])).

tff(c_6918,plain,(
    ! [B_17] : k2_zfmisc_1('#skF_4',B_17) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6782,c_6782,c_133])).

tff(c_812,plain,(
    k4_xboole_0('#skF_6',k2_zfmisc_1('#skF_4','#skF_5')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_808,c_203])).

tff(c_6888,plain,(
    k4_xboole_0('#skF_6',k2_zfmisc_1('#skF_4','#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6782,c_812])).

tff(c_7572,plain,(
    '#skF_6' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6911,c_6918,c_6888])).

tff(c_7573,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6875,c_7572])).

tff(c_7574,plain,
    ( '#skF_5' = '#skF_2'
    | r1_tarski(k1_relat_1('#skF_6'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_6776])).

tff(c_7601,plain,(
    r1_tarski(k1_relat_1('#skF_6'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_7574])).

tff(c_7605,plain,(
    k4_xboole_0(k1_relat_1('#skF_6'),'#skF_4') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_7601,c_203])).

tff(c_325,plain,(
    ! [A_86,B_87] :
      ( v1_xboole_0(k1_funct_2(A_86,B_87))
      | ~ v1_xboole_0(B_87)
      | v1_xboole_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_131,plain,(
    ! [A_5] :
      ( A_5 = '#skF_2'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_6])).

tff(c_359,plain,(
    ! [A_89,B_90] :
      ( k1_funct_2(A_89,B_90) = '#skF_2'
      | ~ v1_xboole_0(B_90)
      | v1_xboole_0(A_89) ) ),
    inference(resolution,[status(thm)],[c_325,c_131])).

tff(c_366,plain,(
    ! [A_91] :
      ( k1_funct_2(A_91,'#skF_2') = '#skF_2'
      | v1_xboole_0(A_91) ) ),
    inference(resolution,[status(thm)],[c_8,c_359])).

tff(c_301,plain,(
    ! [A_82,B_81] :
      ( k4_xboole_0(A_82,B_81) = A_82
      | ~ v1_xboole_0(B_81) ) ),
    inference(resolution,[status(thm)],[c_297,c_22])).

tff(c_384,plain,(
    ! [A_82,A_91] :
      ( k4_xboole_0(A_82,A_91) = A_82
      | k1_funct_2(A_91,'#skF_2') = '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_366,c_301])).

tff(c_7614,plain,
    ( k1_relat_1('#skF_6') = '#skF_2'
    | k1_funct_2('#skF_4','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_7605,c_384])).

tff(c_7630,plain,(
    k1_funct_2('#skF_4','#skF_2') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_269,c_7614])).

tff(c_7575,plain,(
    '#skF_2' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6776])).

tff(c_38,plain,(
    ! [A_22,B_23] :
      ( k2_relat_1(k2_zfmisc_1(A_22,B_23)) = B_23
      | k1_xboole_0 = B_23
      | k1_xboole_0 = A_22 ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_442,plain,(
    ! [A_22,B_23] :
      ( k2_relat_1(k2_zfmisc_1(A_22,B_23)) = B_23
      | B_23 = '#skF_2'
      | A_22 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_130,c_38])).

tff(c_1185,plain,(
    ! [A_169,B_170] :
      ( r1_tarski(k2_relat_1(A_169),k2_relat_1(B_170))
      | ~ r1_tarski(A_169,B_170)
      | ~ v1_relat_1(B_170)
      | ~ v1_relat_1(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1200,plain,(
    ! [A_169,B_23,A_22] :
      ( r1_tarski(k2_relat_1(A_169),B_23)
      | ~ r1_tarski(A_169,k2_zfmisc_1(A_22,B_23))
      | ~ v1_relat_1(k2_zfmisc_1(A_22,B_23))
      | ~ v1_relat_1(A_169)
      | B_23 = '#skF_2'
      | A_22 = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_1185])).

tff(c_8053,plain,(
    ! [A_446,B_447,A_448] :
      ( r1_tarski(k2_relat_1(A_446),B_447)
      | ~ r1_tarski(A_446,k2_zfmisc_1(A_448,B_447))
      | ~ v1_relat_1(A_446)
      | B_447 = '#skF_2'
      | A_448 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1200])).

tff(c_8067,plain,
    ( r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
    | ~ v1_relat_1('#skF_6')
    | '#skF_5' = '#skF_2'
    | '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_808,c_8053])).

tff(c_8089,plain,
    ( r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
    | '#skF_5' = '#skF_2'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_8067])).

tff(c_8090,plain,
    ( r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
    | '#skF_5' = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_7575,c_8089])).

tff(c_8096,plain,(
    '#skF_5' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_8090])).

tff(c_142,plain,(
    ! [B_47,A_48] :
      ( ~ r2_hidden(B_47,A_48)
      | ~ v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_146,plain,(
    ~ v1_xboole_0(k1_funct_2('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_80,c_142])).

tff(c_387,plain,(
    k1_funct_2(k1_funct_2('#skF_4','#skF_5'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_366,c_146])).

tff(c_487,plain,(
    ! [C_98,A_99,B_100] :
      ( v1_funct_2(C_98,A_99,B_100)
      | ~ r2_hidden(C_98,k1_funct_2(A_99,B_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_490,plain,(
    ! [C_98] :
      ( v1_funct_2(C_98,k1_funct_2('#skF_4','#skF_5'),'#skF_2')
      | ~ r2_hidden(C_98,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_387,c_487])).

tff(c_58,plain,(
    ! [C_33,A_31] :
      ( k1_xboole_0 = C_33
      | ~ v1_funct_2(C_33,A_31,k1_xboole_0)
      | k1_xboole_0 = A_31
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_88,plain,(
    ! [C_33,A_31] :
      ( k1_xboole_0 = C_33
      | ~ v1_funct_2(C_33,A_31,k1_xboole_0)
      | k1_xboole_0 = A_31
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_58])).

tff(c_865,plain,(
    ! [C_139,A_140] :
      ( C_139 = '#skF_2'
      | ~ v1_funct_2(C_139,A_140,'#skF_2')
      | A_140 = '#skF_2'
      | ~ m1_subset_1(C_139,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_130,c_130,c_130,c_88])).

tff(c_881,plain,(
    ! [C_98] :
      ( C_98 = '#skF_2'
      | k1_funct_2('#skF_4','#skF_5') = '#skF_2'
      | ~ m1_subset_1(C_98,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(C_98,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_490,c_865])).

tff(c_1294,plain,(
    k1_funct_2('#skF_4','#skF_5') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_881])).

tff(c_1298,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1294,c_146])).

tff(c_1304,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1298])).

tff(c_1306,plain,(
    k1_funct_2('#skF_4','#skF_5') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_881])).

tff(c_8113,plain,(
    k1_funct_2('#skF_4','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8096,c_1306])).

tff(c_8142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7630,c_8113])).

tff(c_8144,plain,(
    '#skF_5' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_8090])).

tff(c_515,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_487])).

tff(c_34,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_752,plain,(
    ! [A_131,B_132,C_133] :
      ( k1_relset_1(A_131,B_132,C_133) = k1_relat_1(C_133)
      | ~ m1_subset_1(C_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2407,plain,(
    ! [A_218,B_219,A_220] :
      ( k1_relset_1(A_218,B_219,A_220) = k1_relat_1(A_220)
      | ~ r1_tarski(A_220,k2_zfmisc_1(A_218,B_219)) ) ),
    inference(resolution,[status(thm)],[c_34,c_752])).

tff(c_2425,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_808,c_2407])).

tff(c_66,plain,(
    ! [B_32,A_31,C_33] :
      ( k1_xboole_0 = B_32
      | k1_relset_1(A_31,B_32,C_33) = A_31
      | ~ v1_funct_2(C_33,A_31,B_32)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_2353,plain,(
    ! [B_212,A_213,C_214] :
      ( B_212 = '#skF_2'
      | k1_relset_1(A_213,B_212,C_214) = A_213
      | ~ v1_funct_2(C_214,A_213,B_212)
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_zfmisc_1(A_213,B_212))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_66])).

tff(c_12453,plain,(
    ! [B_478,A_479,A_480] :
      ( B_478 = '#skF_2'
      | k1_relset_1(A_479,B_478,A_480) = A_479
      | ~ v1_funct_2(A_480,A_479,B_478)
      | ~ r1_tarski(A_480,k2_zfmisc_1(A_479,B_478)) ) ),
    inference(resolution,[status(thm)],[c_34,c_2353])).

tff(c_12474,plain,
    ( '#skF_5' = '#skF_2'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_808,c_12453])).

tff(c_12497,plain,
    ( '#skF_5' = '#skF_2'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_515,c_2425,c_12474])).

tff(c_12499,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_8144,c_12497])).

tff(c_12500,plain,(
    '#skF_5' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_7574])).

tff(c_12522,plain,(
    k4_xboole_0('#skF_6',k2_zfmisc_1('#skF_4','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12500,c_812])).

tff(c_12534,plain,(
    '#skF_6' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_134,c_12522])).

tff(c_12536,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1077,c_12534])).

tff(c_12538,plain,(
    k1_relat_1('#skF_6') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_253])).

tff(c_12543,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12538,c_156])).

tff(c_12932,plain,(
    ! [C_524,A_525,B_526] :
      ( m1_subset_1(C_524,k1_zfmisc_1(k2_zfmisc_1(A_525,B_526)))
      | ~ r2_hidden(C_524,k1_funct_2(A_525,B_526)) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_13055,plain,(
    ! [C_541,A_542,B_543] :
      ( r1_tarski(C_541,k2_zfmisc_1(A_542,B_543))
      | ~ r2_hidden(C_541,k1_funct_2(A_542,B_543)) ) ),
    inference(resolution,[status(thm)],[c_12932,c_32])).

tff(c_13086,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_80,c_13055])).

tff(c_13090,plain,(
    k4_xboole_0('#skF_6',k2_zfmisc_1('#skF_4','#skF_5')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_13086,c_203])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_3'(A_6,B_7),B_7)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_3'(A_6,B_7),A_6)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( r1_xboole_0(A_14,B_15)
      | k4_xboole_0(A_14,B_15) != A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_12881,plain,(
    ! [A_514,B_515,C_516] :
      ( ~ r1_xboole_0(A_514,B_515)
      | ~ r2_hidden(C_516,B_515)
      | ~ r2_hidden(C_516,A_514) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_13339,plain,(
    ! [C_555,B_556,A_557] :
      ( ~ r2_hidden(C_555,B_556)
      | ~ r2_hidden(C_555,A_557)
      | k4_xboole_0(A_557,B_556) != A_557 ) ),
    inference(resolution,[status(thm)],[c_24,c_12881])).

tff(c_16887,plain,(
    ! [A_2639,B_2640,A_2641] :
      ( ~ r2_hidden('#skF_3'(A_2639,B_2640),A_2641)
      | k4_xboole_0(A_2641,A_2639) != A_2641
      | r1_xboole_0(A_2639,B_2640) ) ),
    inference(resolution,[status(thm)],[c_14,c_13339])).

tff(c_16896,plain,(
    ! [B_2642,A_2643] :
      ( k4_xboole_0(B_2642,A_2643) != B_2642
      | r1_xboole_0(A_2643,B_2642) ) ),
    inference(resolution,[status(thm)],[c_12,c_16887])).

tff(c_16943,plain,(
    ! [A_2648,B_2649] :
      ( k4_xboole_0(A_2648,B_2649) = A_2648
      | k4_xboole_0(B_2649,A_2648) != B_2649 ) ),
    inference(resolution,[status(thm)],[c_16896,c_22])).

tff(c_16951,plain,
    ( k4_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'),'#skF_6') = k2_zfmisc_1('#skF_4','#skF_5')
    | '#skF_6' != '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_13090,c_16943])).

tff(c_17045,plain,(
    '#skF_6' != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_16951])).

tff(c_12565,plain,(
    ! [A_485,B_486] :
      ( r2_hidden('#skF_3'(A_485,B_486),B_486)
      | r1_xboole_0(A_485,B_486) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12575,plain,(
    ! [B_487,A_488] :
      ( ~ v1_xboole_0(B_487)
      | r1_xboole_0(A_488,B_487) ) ),
    inference(resolution,[status(thm)],[c_12565,c_2])).

tff(c_12580,plain,(
    ! [A_489,B_490] :
      ( k4_xboole_0(A_489,B_490) = A_489
      | ~ v1_xboole_0(B_490) ) ),
    inference(resolution,[status(thm)],[c_12575,c_22])).

tff(c_12583,plain,(
    ! [A_489] : k4_xboole_0(A_489,'#skF_2') = A_489 ),
    inference(resolution,[status(thm)],[c_8,c_12580])).

tff(c_12851,plain,(
    ! [C_510,A_511,B_512] :
      ( v1_funct_2(C_510,A_511,B_512)
      | ~ r2_hidden(C_510,k1_funct_2(A_511,B_512)) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_12879,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_80,c_12851])).

tff(c_13030,plain,(
    ! [A_537,B_538,C_539] :
      ( k1_relset_1(A_537,B_538,C_539) = k1_relat_1(C_539)
      | ~ m1_subset_1(C_539,k1_zfmisc_1(k2_zfmisc_1(A_537,B_538))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_14675,plain,(
    ! [A_620,B_621,A_622] :
      ( k1_relset_1(A_620,B_621,A_622) = k1_relat_1(A_622)
      | ~ r1_tarski(A_622,k2_zfmisc_1(A_620,B_621)) ) ),
    inference(resolution,[status(thm)],[c_34,c_13030])).

tff(c_14678,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_13086,c_14675])).

tff(c_14694,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12538,c_14678])).

tff(c_14732,plain,(
    ! [B_625,A_626,C_627] :
      ( B_625 = '#skF_2'
      | k1_relset_1(A_626,B_625,C_627) = A_626
      | ~ v1_funct_2(C_627,A_626,B_625)
      | ~ m1_subset_1(C_627,k1_zfmisc_1(k2_zfmisc_1(A_626,B_625))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_66])).

tff(c_23836,plain,(
    ! [B_2791,A_2792,A_2793] :
      ( B_2791 = '#skF_2'
      | k1_relset_1(A_2792,B_2791,A_2793) = A_2792
      | ~ v1_funct_2(A_2793,A_2792,B_2791)
      | ~ r1_tarski(A_2793,k2_zfmisc_1(A_2792,B_2791)) ) ),
    inference(resolution,[status(thm)],[c_34,c_14732])).

tff(c_23857,plain,
    ( '#skF_5' = '#skF_2'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_13086,c_23836])).

tff(c_23880,plain,
    ( '#skF_5' = '#skF_2'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12879,c_14694,c_23857])).

tff(c_23881,plain,(
    '#skF_5' = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_12543,c_23880])).

tff(c_23910,plain,(
    k4_xboole_0('#skF_6',k2_zfmisc_1('#skF_4','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23881,c_13090])).

tff(c_23923,plain,(
    '#skF_6' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12583,c_134,c_23910])).

tff(c_23925,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17045,c_23923])).

tff(c_23927,plain,(
    '#skF_6' = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_16951])).

tff(c_23942,plain,(
    v1_funct_2('#skF_2','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23927,c_12879])).

tff(c_20,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_137,plain,(
    ! [A_13] : r1_tarski('#skF_2',A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_20])).

tff(c_14692,plain,(
    ! [A_620,B_621] : k1_relset_1(A_620,B_621,'#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_137,c_14675])).

tff(c_14697,plain,(
    ! [A_620,B_621] : k1_relset_1(A_620,B_621,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_14692])).

tff(c_23945,plain,(
    r2_hidden('#skF_2',k1_funct_2('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_23927,c_80])).

tff(c_70,plain,(
    ! [C_38,A_36,B_37] :
      ( m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ r2_hidden(C_38,k1_funct_2(A_36,B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_29902,plain,(
    ! [B_2923,A_2924,C_2925] :
      ( B_2923 = '#skF_2'
      | k1_relset_1(A_2924,B_2923,C_2925) = A_2924
      | ~ v1_funct_2(C_2925,A_2924,B_2923)
      | ~ r2_hidden(C_2925,k1_funct_2(A_2924,B_2923)) ) ),
    inference(resolution,[status(thm)],[c_70,c_14732])).

tff(c_29932,plain,
    ( '#skF_5' = '#skF_2'
    | k1_relset_1('#skF_4','#skF_5','#skF_2') = '#skF_4'
    | ~ v1_funct_2('#skF_2','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_23945,c_29902])).

tff(c_29984,plain,
    ( '#skF_5' = '#skF_2'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_23942,c_14697,c_29932])).

tff(c_29985,plain,(
    '#skF_5' = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_12543,c_29984])).

tff(c_12584,plain,(
    ! [A_491,B_492] :
      ( v1_xboole_0(k1_funct_2(A_491,B_492))
      | ~ v1_xboole_0(B_492)
      | v1_xboole_0(A_491) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_12598,plain,
    ( ~ v1_xboole_0('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_12584,c_146])).

tff(c_12599,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_12598])).

tff(c_30024,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29985,c_12599])).

tff(c_30031,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_30024])).

tff(c_30032,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_12598])).

tff(c_30040,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_30032,c_131])).

tff(c_30046,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12543,c_30040])).

tff(c_30048,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_50,plain,(
    ! [A_27] :
      ( k1_relat_1(A_27) = k1_xboole_0
      | k2_relat_1(A_27) != k1_xboole_0
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_30225,plain,(
    ! [A_2963] :
      ( k1_relat_1(A_2963) = '#skF_2'
      | k2_relat_1(A_2963) != '#skF_2'
      | ~ v1_relat_1(A_2963) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_130,c_50])).

tff(c_30234,plain,
    ( k1_relat_1('#skF_6') = '#skF_2'
    | k2_relat_1('#skF_6') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_84,c_30225])).

tff(c_30240,plain,
    ( '#skF_2' = '#skF_4'
    | k2_relat_1('#skF_6') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30048,c_30234])).

tff(c_30241,plain,(
    k2_relat_1('#skF_6') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_30240])).

tff(c_30243,plain,(
    ! [A_2964] :
      ( k2_relat_1(A_2964) = '#skF_2'
      | k1_relat_1(A_2964) != '#skF_2'
      | ~ v1_relat_1(A_2964) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_130,c_52])).

tff(c_30252,plain,
    ( k2_relat_1('#skF_6') = '#skF_2'
    | k1_relat_1('#skF_6') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_84,c_30243])).

tff(c_30258,plain,
    ( k2_relat_1('#skF_6') = '#skF_2'
    | '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30048,c_30252])).

tff(c_30259,plain,(
    '#skF_2' != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_30241,c_30258])).

tff(c_30562,plain,(
    ! [C_2994,A_2995,B_2996] :
      ( m1_subset_1(C_2994,k1_zfmisc_1(k2_zfmisc_1(A_2995,B_2996)))
      | ~ r2_hidden(C_2994,k1_funct_2(A_2995,B_2996)) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_30684,plain,(
    ! [C_3011,A_3012,B_3013] :
      ( r1_tarski(C_3011,k2_zfmisc_1(A_3012,B_3013))
      | ~ r2_hidden(C_3011,k1_funct_2(A_3012,B_3013)) ) ),
    inference(resolution,[status(thm)],[c_30562,c_32])).

tff(c_30715,plain,(
    r1_tarski('#skF_6',k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_80,c_30684])).

tff(c_30489,plain,(
    ! [A_22,B_23] :
      ( k1_relat_1(k2_zfmisc_1(A_22,B_23)) = A_22
      | B_23 = '#skF_2'
      | A_22 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_130,c_40])).

tff(c_31092,plain,(
    ! [A_3045,B_3046] :
      ( r1_tarski(k1_relat_1(A_3045),k1_relat_1(B_3046))
      | ~ r1_tarski(A_3045,B_3046)
      | ~ v1_relat_1(B_3046)
      | ~ v1_relat_1(A_3045) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_31110,plain,(
    ! [B_3046] :
      ( r1_tarski('#skF_4',k1_relat_1(B_3046))
      | ~ r1_tarski('#skF_6',B_3046)
      | ~ v1_relat_1(B_3046)
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30048,c_31092])).

tff(c_31137,plain,(
    ! [B_3047] :
      ( r1_tarski('#skF_4',k1_relat_1(B_3047))
      | ~ r1_tarski('#skF_6',B_3047)
      | ~ v1_relat_1(B_3047) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_31110])).

tff(c_31146,plain,(
    ! [A_22,B_23] :
      ( r1_tarski('#skF_4',A_22)
      | ~ r1_tarski('#skF_6',k2_zfmisc_1(A_22,B_23))
      | ~ v1_relat_1(k2_zfmisc_1(A_22,B_23))
      | B_23 = '#skF_2'
      | A_22 = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30489,c_31137])).

tff(c_33627,plain,(
    ! [A_3145,B_3146] :
      ( r1_tarski('#skF_4',A_3145)
      | ~ r1_tarski('#skF_6',k2_zfmisc_1(A_3145,B_3146))
      | B_3146 = '#skF_2'
      | A_3145 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_31146])).

tff(c_33634,plain,
    ( r1_tarski('#skF_4','#skF_4')
    | '#skF_5' = '#skF_2'
    | '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_30715,c_33627])).

tff(c_33647,plain,
    ( r1_tarski('#skF_4','#skF_4')
    | '#skF_5' = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_30259,c_33634])).

tff(c_33649,plain,(
    '#skF_5' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_33647])).

tff(c_30170,plain,(
    ! [A_2954,B_2955] :
      ( r2_hidden('#skF_3'(A_2954,B_2955),B_2955)
      | r1_xboole_0(A_2954,B_2955) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_30193,plain,(
    ! [B_2958,A_2959] :
      ( ~ v1_xboole_0(B_2958)
      | r1_xboole_0(A_2959,B_2958) ) ),
    inference(resolution,[status(thm)],[c_30170,c_2])).

tff(c_30198,plain,(
    ! [A_2960,B_2961] :
      ( k4_xboole_0(A_2960,B_2961) = A_2960
      | ~ v1_xboole_0(B_2961) ) ),
    inference(resolution,[status(thm)],[c_30193,c_22])).

tff(c_30204,plain,(
    ! [A_2960] : k4_xboole_0(A_2960,'#skF_2') = A_2960 ),
    inference(resolution,[status(thm)],[c_8,c_30198])).

tff(c_30123,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | k4_xboole_0(A_11,B_12) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_16])).

tff(c_46,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_135,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_130,c_46])).

tff(c_30898,plain,(
    ! [A_3031,B_3032] :
      ( r1_tarski(k2_relat_1(A_3031),k2_relat_1(B_3032))
      | ~ r1_tarski(A_3031,B_3032)
      | ~ v1_relat_1(B_3032)
      | ~ v1_relat_1(A_3031) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_30913,plain,(
    ! [A_3031] :
      ( r1_tarski(k2_relat_1(A_3031),'#skF_2')
      | ~ r1_tarski(A_3031,'#skF_2')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(A_3031) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_30898])).

tff(c_30923,plain,(
    ! [A_3033] :
      ( r1_tarski(k2_relat_1(A_3033),'#skF_2')
      | ~ r1_tarski(A_3033,'#skF_2')
      | ~ v1_relat_1(A_3033) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_30913])).

tff(c_30110,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = '#skF_2'
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_18])).

tff(c_30928,plain,(
    ! [A_3033] :
      ( k4_xboole_0(k2_relat_1(A_3033),'#skF_2') = '#skF_2'
      | ~ r1_tarski(A_3033,'#skF_2')
      | ~ v1_relat_1(A_3033) ) ),
    inference(resolution,[status(thm)],[c_30923,c_30110])).

tff(c_30942,plain,(
    ! [A_3034] :
      ( k2_relat_1(A_3034) = '#skF_2'
      | ~ r1_tarski(A_3034,'#skF_2')
      | ~ v1_relat_1(A_3034) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30204,c_30928])).

tff(c_30955,plain,(
    ! [A_11] :
      ( k2_relat_1(A_11) = '#skF_2'
      | ~ v1_relat_1(A_11)
      | k4_xboole_0(A_11,'#skF_2') != '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_30123,c_30942])).

tff(c_30969,plain,(
    ! [A_3035] :
      ( k2_relat_1(A_3035) = '#skF_2'
      | ~ v1_relat_1(A_3035)
      | A_3035 != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30204,c_30955])).

tff(c_30985,plain,(
    ! [A_3036,B_3037] :
      ( k2_relat_1(k2_zfmisc_1(A_3036,B_3037)) = '#skF_2'
      | k2_zfmisc_1(A_3036,B_3037) != '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_36,c_30969])).

tff(c_30238,plain,(
    ! [A_20,B_21] :
      ( k1_relat_1(k2_zfmisc_1(A_20,B_21)) = '#skF_2'
      | k2_relat_1(k2_zfmisc_1(A_20,B_21)) != '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_36,c_30225])).

tff(c_31023,plain,(
    ! [A_3036,B_3037] :
      ( k1_relat_1(k2_zfmisc_1(A_3036,B_3037)) = '#skF_2'
      | k2_zfmisc_1(A_3036,B_3037) != '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30985,c_30238])).

tff(c_31504,plain,(
    ! [B_3069] :
      ( k4_xboole_0('#skF_4',k1_relat_1(B_3069)) = '#skF_2'
      | ~ r1_tarski('#skF_6',B_3069)
      | ~ v1_relat_1(B_3069) ) ),
    inference(resolution,[status(thm)],[c_31137,c_30110])).

tff(c_31519,plain,(
    ! [A_3036,B_3037] :
      ( k4_xboole_0('#skF_4','#skF_2') = '#skF_2'
      | ~ r1_tarski('#skF_6',k2_zfmisc_1(A_3036,B_3037))
      | ~ v1_relat_1(k2_zfmisc_1(A_3036,B_3037))
      | k2_zfmisc_1(A_3036,B_3037) != '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31023,c_31504])).

tff(c_31540,plain,(
    ! [A_3036,B_3037] :
      ( '#skF_2' = '#skF_4'
      | ~ r1_tarski('#skF_6',k2_zfmisc_1(A_3036,B_3037))
      | k2_zfmisc_1(A_3036,B_3037) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30204,c_31519])).

tff(c_31672,plain,(
    ! [A_3076,B_3077] :
      ( ~ r1_tarski('#skF_6',k2_zfmisc_1(A_3076,B_3077))
      | k2_zfmisc_1(A_3076,B_3077) != '#skF_2' ) ),
    inference(negUnitSimplification,[status(thm)],[c_30259,c_31540])).

tff(c_31685,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_30715,c_31672])).

tff(c_33659,plain,(
    k2_zfmisc_1('#skF_4','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33649,c_31685])).

tff(c_33682,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_33659])).

tff(c_33684,plain,(
    '#skF_5' != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_33647])).

tff(c_30047,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_30466,plain,(
    ! [A_22,B_23] :
      ( k2_relat_1(k2_zfmisc_1(A_22,B_23)) = B_23
      | B_23 = '#skF_2'
      | A_22 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_130,c_38])).

tff(c_30907,plain,(
    ! [A_3031,B_23,A_22] :
      ( r1_tarski(k2_relat_1(A_3031),B_23)
      | ~ r1_tarski(A_3031,k2_zfmisc_1(A_22,B_23))
      | ~ v1_relat_1(k2_zfmisc_1(A_22,B_23))
      | ~ v1_relat_1(A_3031)
      | B_23 = '#skF_2'
      | A_22 = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30466,c_30898])).

tff(c_42135,plain,(
    ! [A_3347,B_3348,A_3349] :
      ( r1_tarski(k2_relat_1(A_3347),B_3348)
      | ~ r1_tarski(A_3347,k2_zfmisc_1(A_3349,B_3348))
      | ~ v1_relat_1(A_3347)
      | B_3348 = '#skF_2'
      | A_3349 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_30907])).

tff(c_42151,plain,
    ( r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
    | ~ v1_relat_1('#skF_6')
    | '#skF_5' = '#skF_2'
    | '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_30715,c_42135])).

tff(c_42172,plain,
    ( r1_tarski(k2_relat_1('#skF_6'),'#skF_5')
    | '#skF_5' = '#skF_2'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_42151])).

tff(c_42174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30259,c_33684,c_30047,c_42172])).

tff(c_42175,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_30240])).

tff(c_42188,plain,(
    ! [A_13] : r1_tarski('#skF_4',A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42175,c_137])).

tff(c_42176,plain,(
    k2_relat_1('#skF_6') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_30240])).

tff(c_42201,plain,(
    k2_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42175,c_42176])).

tff(c_42202,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42201,c_30047])).

tff(c_42223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42188,c_42202])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:01:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.80/5.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.80/5.39  
% 12.80/5.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.80/5.40  %$ v1_funct_2 > r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k1_relset_1 > k4_xboole_0 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 12.80/5.40  
% 12.80/5.40  %Foreground sorts:
% 12.80/5.40  
% 12.80/5.40  
% 12.80/5.40  %Background operators:
% 12.80/5.40  
% 12.80/5.40  
% 12.80/5.40  %Foreground operators:
% 12.80/5.40  tff(k3_partfun1, type, k3_partfun1: ($i * $i * $i) > $i).
% 12.80/5.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.80/5.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.80/5.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.80/5.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.80/5.40  tff('#skF_1', type, '#skF_1': $i > $i).
% 12.80/5.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.80/5.40  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 12.80/5.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.80/5.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.80/5.40  tff('#skF_5', type, '#skF_5': $i).
% 12.80/5.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.80/5.40  tff('#skF_6', type, '#skF_6': $i).
% 12.80/5.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 12.80/5.40  tff('#skF_2', type, '#skF_2': $i).
% 12.80/5.40  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 12.80/5.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.80/5.40  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 12.80/5.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.80/5.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.80/5.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.80/5.40  tff('#skF_4', type, '#skF_4': $i).
% 12.80/5.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.80/5.40  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 12.80/5.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.80/5.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.80/5.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.80/5.40  
% 13.01/5.43  tff(f_159, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(C, k1_funct_2(A, B)) => ((k1_relat_1(C) = A) & r1_tarski(k2_relat_1(C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_funct_2)).
% 13.01/5.43  tff(f_37, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 13.01/5.43  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 13.01/5.43  tff(f_109, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 13.01/5.43  tff(f_55, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 13.01/5.43  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 13.01/5.43  tff(f_65, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 13.01/5.43  tff(f_59, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 13.01/5.43  tff(f_71, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 13.01/5.43  tff(f_77, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 13.01/5.43  tff(f_103, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 13.01/5.43  tff(f_100, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 13.01/5.43  tff(f_146, axiom, (![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t121_funct_2)).
% 13.01/5.43  tff(f_75, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 13.01/5.43  tff(f_89, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 13.01/5.43  tff(f_138, axiom, (![A, B]: ((~v1_xboole_0(A) & v1_xboole_0(B)) => v1_xboole_0(k1_funct_2(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_2)).
% 13.01/5.43  tff(f_131, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 13.01/5.43  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 13.01/5.43  tff(f_61, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 13.01/5.43  tff(c_84, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_159])).
% 13.01/5.43  tff(c_8, plain, (v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.01/5.43  tff(c_126, plain, (![A_46]: (k1_xboole_0=A_46 | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.01/5.43  tff(c_130, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_8, c_126])).
% 13.01/5.43  tff(c_52, plain, (![A_27]: (k2_relat_1(A_27)=k1_xboole_0 | k1_relat_1(A_27)!=k1_xboole_0 | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_109])).
% 13.01/5.43  tff(c_239, plain, (![A_70]: (k2_relat_1(A_70)='#skF_2' | k1_relat_1(A_70)!='#skF_2' | ~v1_relat_1(A_70))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_130, c_52])).
% 13.01/5.43  tff(c_253, plain, (k2_relat_1('#skF_6')='#skF_2' | k1_relat_1('#skF_6')!='#skF_2'), inference(resolution, [status(thm)], [c_84, c_239])).
% 13.01/5.43  tff(c_269, plain, (k1_relat_1('#skF_6')!='#skF_2'), inference(splitLeft, [status(thm)], [c_253])).
% 13.01/5.43  tff(c_287, plain, (![A_79, B_80]: (r2_hidden('#skF_3'(A_79, B_80), B_80) | r1_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.01/5.43  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.01/5.43  tff(c_297, plain, (![B_81, A_82]: (~v1_xboole_0(B_81) | r1_xboole_0(A_82, B_81))), inference(resolution, [status(thm)], [c_287, c_2])).
% 13.01/5.43  tff(c_22, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=A_14 | ~r1_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.01/5.43  tff(c_302, plain, (![A_83, B_84]: (k4_xboole_0(A_83, B_84)=A_83 | ~v1_xboole_0(B_84))), inference(resolution, [status(thm)], [c_297, c_22])).
% 13.01/5.43  tff(c_305, plain, (![A_83]: (k4_xboole_0(A_83, '#skF_2')=A_83)), inference(resolution, [status(thm)], [c_8, c_302])).
% 13.01/5.43  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | k4_xboole_0(A_11, B_12)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.01/5.43  tff(c_216, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | k4_xboole_0(A_11, B_12)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_16])).
% 13.01/5.43  tff(c_30, plain, (![B_17]: (k2_zfmisc_1(k1_xboole_0, B_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.01/5.43  tff(c_120, plain, (![A_44, B_45]: (v1_relat_1(k2_zfmisc_1(A_44, B_45)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 13.01/5.43  tff(c_122, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_120])).
% 13.01/5.43  tff(c_132, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_122])).
% 13.01/5.43  tff(c_48, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_103])).
% 13.01/5.43  tff(c_136, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_130, c_130, c_48])).
% 13.01/5.43  tff(c_991, plain, (![A_155, B_156]: (r1_tarski(k1_relat_1(A_155), k1_relat_1(B_156)) | ~r1_tarski(A_155, B_156) | ~v1_relat_1(B_156) | ~v1_relat_1(A_155))), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.01/5.43  tff(c_1006, plain, (![A_155]: (r1_tarski(k1_relat_1(A_155), '#skF_2') | ~r1_tarski(A_155, '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(A_155))), inference(superposition, [status(thm), theory('equality')], [c_136, c_991])).
% 13.01/5.43  tff(c_1016, plain, (![A_157]: (r1_tarski(k1_relat_1(A_157), '#skF_2') | ~r1_tarski(A_157, '#skF_2') | ~v1_relat_1(A_157))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_1006])).
% 13.01/5.43  tff(c_18, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=k1_xboole_0 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.01/5.43  tff(c_203, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)='#skF_2' | ~r1_tarski(A_11, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_18])).
% 13.01/5.43  tff(c_1021, plain, (![A_157]: (k4_xboole_0(k1_relat_1(A_157), '#skF_2')='#skF_2' | ~r1_tarski(A_157, '#skF_2') | ~v1_relat_1(A_157))), inference(resolution, [status(thm)], [c_1016, c_203])).
% 13.01/5.43  tff(c_1035, plain, (![A_158]: (k1_relat_1(A_158)='#skF_2' | ~r1_tarski(A_158, '#skF_2') | ~v1_relat_1(A_158))), inference(demodulation, [status(thm), theory('equality')], [c_305, c_1021])).
% 13.01/5.43  tff(c_1048, plain, (![A_11]: (k1_relat_1(A_11)='#skF_2' | ~v1_relat_1(A_11) | k4_xboole_0(A_11, '#skF_2')!='#skF_2')), inference(resolution, [status(thm)], [c_216, c_1035])).
% 13.01/5.43  tff(c_1062, plain, (![A_159]: (k1_relat_1(A_159)='#skF_2' | ~v1_relat_1(A_159) | A_159!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_305, c_1048])).
% 13.01/5.43  tff(c_1071, plain, (k1_relat_1('#skF_6')='#skF_2' | '#skF_6'!='#skF_2'), inference(resolution, [status(thm)], [c_84, c_1062])).
% 13.01/5.43  tff(c_1077, plain, ('#skF_6'!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_269, c_1071])).
% 13.01/5.43  tff(c_28, plain, (![A_16]: (k2_zfmisc_1(A_16, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.01/5.43  tff(c_134, plain, (![A_16]: (k2_zfmisc_1(A_16, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_130, c_28])).
% 13.01/5.43  tff(c_78, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | k1_relat_1('#skF_6')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_159])).
% 13.01/5.43  tff(c_156, plain, (k1_relat_1('#skF_6')!='#skF_4'), inference(splitLeft, [status(thm)], [c_78])).
% 13.01/5.43  tff(c_80, plain, (r2_hidden('#skF_6', k1_funct_2('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_159])).
% 13.01/5.43  tff(c_654, plain, (![C_118, A_119, B_120]: (m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))) | ~r2_hidden(C_118, k1_funct_2(A_119, B_120)))), inference(cnfTransformation, [status(thm)], [f_146])).
% 13.01/5.43  tff(c_32, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | ~m1_subset_1(A_18, k1_zfmisc_1(B_19)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.01/5.43  tff(c_777, plain, (![C_135, A_136, B_137]: (r1_tarski(C_135, k2_zfmisc_1(A_136, B_137)) | ~r2_hidden(C_135, k1_funct_2(A_136, B_137)))), inference(resolution, [status(thm)], [c_654, c_32])).
% 13.01/5.43  tff(c_808, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_80, c_777])).
% 13.01/5.43  tff(c_36, plain, (![A_20, B_21]: (v1_relat_1(k2_zfmisc_1(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 13.01/5.43  tff(c_40, plain, (![A_22, B_23]: (k1_relat_1(k2_zfmisc_1(A_22, B_23))=A_22 | k1_xboole_0=B_23 | k1_xboole_0=A_22)), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.01/5.43  tff(c_580, plain, (![A_22, B_23]: (k1_relat_1(k2_zfmisc_1(A_22, B_23))=A_22 | B_23='#skF_2' | A_22='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_130, c_40])).
% 13.01/5.43  tff(c_1000, plain, (![A_155, A_22, B_23]: (r1_tarski(k1_relat_1(A_155), A_22) | ~r1_tarski(A_155, k2_zfmisc_1(A_22, B_23)) | ~v1_relat_1(k2_zfmisc_1(A_22, B_23)) | ~v1_relat_1(A_155) | B_23='#skF_2' | A_22='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_580, c_991])).
% 13.01/5.43  tff(c_6740, plain, (![A_409, A_410, B_411]: (r1_tarski(k1_relat_1(A_409), A_410) | ~r1_tarski(A_409, k2_zfmisc_1(A_410, B_411)) | ~v1_relat_1(A_409) | B_411='#skF_2' | A_410='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1000])).
% 13.01/5.43  tff(c_6754, plain, (r1_tarski(k1_relat_1('#skF_6'), '#skF_4') | ~v1_relat_1('#skF_6') | '#skF_5'='#skF_2' | '#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_808, c_6740])).
% 13.01/5.43  tff(c_6776, plain, (r1_tarski(k1_relat_1('#skF_6'), '#skF_4') | '#skF_5'='#skF_2' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_6754])).
% 13.01/5.43  tff(c_6782, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_6776])).
% 13.01/5.43  tff(c_6875, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6782, c_1077])).
% 13.01/5.43  tff(c_6911, plain, (![A_83]: (k4_xboole_0(A_83, '#skF_4')=A_83)), inference(demodulation, [status(thm), theory('equality')], [c_6782, c_305])).
% 13.01/5.43  tff(c_133, plain, (![B_17]: (k2_zfmisc_1('#skF_2', B_17)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_130, c_30])).
% 13.01/5.43  tff(c_6918, plain, (![B_17]: (k2_zfmisc_1('#skF_4', B_17)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6782, c_6782, c_133])).
% 13.01/5.43  tff(c_812, plain, (k4_xboole_0('#skF_6', k2_zfmisc_1('#skF_4', '#skF_5'))='#skF_2'), inference(resolution, [status(thm)], [c_808, c_203])).
% 13.01/5.43  tff(c_6888, plain, (k4_xboole_0('#skF_6', k2_zfmisc_1('#skF_4', '#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6782, c_812])).
% 13.01/5.43  tff(c_7572, plain, ('#skF_6'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6911, c_6918, c_6888])).
% 13.01/5.43  tff(c_7573, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6875, c_7572])).
% 13.01/5.43  tff(c_7574, plain, ('#skF_5'='#skF_2' | r1_tarski(k1_relat_1('#skF_6'), '#skF_4')), inference(splitRight, [status(thm)], [c_6776])).
% 13.01/5.43  tff(c_7601, plain, (r1_tarski(k1_relat_1('#skF_6'), '#skF_4')), inference(splitLeft, [status(thm)], [c_7574])).
% 13.01/5.43  tff(c_7605, plain, (k4_xboole_0(k1_relat_1('#skF_6'), '#skF_4')='#skF_2'), inference(resolution, [status(thm)], [c_7601, c_203])).
% 13.01/5.43  tff(c_325, plain, (![A_86, B_87]: (v1_xboole_0(k1_funct_2(A_86, B_87)) | ~v1_xboole_0(B_87) | v1_xboole_0(A_86))), inference(cnfTransformation, [status(thm)], [f_138])).
% 13.01/5.43  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.01/5.43  tff(c_131, plain, (![A_5]: (A_5='#skF_2' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_6])).
% 13.01/5.43  tff(c_359, plain, (![A_89, B_90]: (k1_funct_2(A_89, B_90)='#skF_2' | ~v1_xboole_0(B_90) | v1_xboole_0(A_89))), inference(resolution, [status(thm)], [c_325, c_131])).
% 13.01/5.43  tff(c_366, plain, (![A_91]: (k1_funct_2(A_91, '#skF_2')='#skF_2' | v1_xboole_0(A_91))), inference(resolution, [status(thm)], [c_8, c_359])).
% 13.01/5.43  tff(c_301, plain, (![A_82, B_81]: (k4_xboole_0(A_82, B_81)=A_82 | ~v1_xboole_0(B_81))), inference(resolution, [status(thm)], [c_297, c_22])).
% 13.01/5.43  tff(c_384, plain, (![A_82, A_91]: (k4_xboole_0(A_82, A_91)=A_82 | k1_funct_2(A_91, '#skF_2')='#skF_2')), inference(resolution, [status(thm)], [c_366, c_301])).
% 13.01/5.43  tff(c_7614, plain, (k1_relat_1('#skF_6')='#skF_2' | k1_funct_2('#skF_4', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_7605, c_384])).
% 13.01/5.43  tff(c_7630, plain, (k1_funct_2('#skF_4', '#skF_2')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_269, c_7614])).
% 13.01/5.43  tff(c_7575, plain, ('#skF_2'!='#skF_4'), inference(splitRight, [status(thm)], [c_6776])).
% 13.01/5.43  tff(c_38, plain, (![A_22, B_23]: (k2_relat_1(k2_zfmisc_1(A_22, B_23))=B_23 | k1_xboole_0=B_23 | k1_xboole_0=A_22)), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.01/5.43  tff(c_442, plain, (![A_22, B_23]: (k2_relat_1(k2_zfmisc_1(A_22, B_23))=B_23 | B_23='#skF_2' | A_22='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_130, c_38])).
% 13.01/5.43  tff(c_1185, plain, (![A_169, B_170]: (r1_tarski(k2_relat_1(A_169), k2_relat_1(B_170)) | ~r1_tarski(A_169, B_170) | ~v1_relat_1(B_170) | ~v1_relat_1(A_169))), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.01/5.43  tff(c_1200, plain, (![A_169, B_23, A_22]: (r1_tarski(k2_relat_1(A_169), B_23) | ~r1_tarski(A_169, k2_zfmisc_1(A_22, B_23)) | ~v1_relat_1(k2_zfmisc_1(A_22, B_23)) | ~v1_relat_1(A_169) | B_23='#skF_2' | A_22='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_442, c_1185])).
% 13.01/5.43  tff(c_8053, plain, (![A_446, B_447, A_448]: (r1_tarski(k2_relat_1(A_446), B_447) | ~r1_tarski(A_446, k2_zfmisc_1(A_448, B_447)) | ~v1_relat_1(A_446) | B_447='#skF_2' | A_448='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1200])).
% 13.01/5.43  tff(c_8067, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | ~v1_relat_1('#skF_6') | '#skF_5'='#skF_2' | '#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_808, c_8053])).
% 13.01/5.43  tff(c_8089, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | '#skF_5'='#skF_2' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_8067])).
% 13.01/5.43  tff(c_8090, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | '#skF_5'='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_7575, c_8089])).
% 13.01/5.43  tff(c_8096, plain, ('#skF_5'='#skF_2'), inference(splitLeft, [status(thm)], [c_8090])).
% 13.01/5.43  tff(c_142, plain, (![B_47, A_48]: (~r2_hidden(B_47, A_48) | ~v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.01/5.43  tff(c_146, plain, (~v1_xboole_0(k1_funct_2('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_80, c_142])).
% 13.01/5.43  tff(c_387, plain, (k1_funct_2(k1_funct_2('#skF_4', '#skF_5'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_366, c_146])).
% 13.01/5.43  tff(c_487, plain, (![C_98, A_99, B_100]: (v1_funct_2(C_98, A_99, B_100) | ~r2_hidden(C_98, k1_funct_2(A_99, B_100)))), inference(cnfTransformation, [status(thm)], [f_146])).
% 13.01/5.43  tff(c_490, plain, (![C_98]: (v1_funct_2(C_98, k1_funct_2('#skF_4', '#skF_5'), '#skF_2') | ~r2_hidden(C_98, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_387, c_487])).
% 13.01/5.43  tff(c_58, plain, (![C_33, A_31]: (k1_xboole_0=C_33 | ~v1_funct_2(C_33, A_31, k1_xboole_0) | k1_xboole_0=A_31 | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 13.01/5.43  tff(c_88, plain, (![C_33, A_31]: (k1_xboole_0=C_33 | ~v1_funct_2(C_33, A_31, k1_xboole_0) | k1_xboole_0=A_31 | ~m1_subset_1(C_33, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_58])).
% 13.01/5.43  tff(c_865, plain, (![C_139, A_140]: (C_139='#skF_2' | ~v1_funct_2(C_139, A_140, '#skF_2') | A_140='#skF_2' | ~m1_subset_1(C_139, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_130, c_130, c_130, c_88])).
% 13.01/5.43  tff(c_881, plain, (![C_98]: (C_98='#skF_2' | k1_funct_2('#skF_4', '#skF_5')='#skF_2' | ~m1_subset_1(C_98, k1_zfmisc_1('#skF_2')) | ~r2_hidden(C_98, '#skF_2'))), inference(resolution, [status(thm)], [c_490, c_865])).
% 13.01/5.43  tff(c_1294, plain, (k1_funct_2('#skF_4', '#skF_5')='#skF_2'), inference(splitLeft, [status(thm)], [c_881])).
% 13.01/5.43  tff(c_1298, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1294, c_146])).
% 13.01/5.43  tff(c_1304, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_1298])).
% 13.01/5.43  tff(c_1306, plain, (k1_funct_2('#skF_4', '#skF_5')!='#skF_2'), inference(splitRight, [status(thm)], [c_881])).
% 13.01/5.43  tff(c_8113, plain, (k1_funct_2('#skF_4', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8096, c_1306])).
% 13.01/5.43  tff(c_8142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7630, c_8113])).
% 13.01/5.43  tff(c_8144, plain, ('#skF_5'!='#skF_2'), inference(splitRight, [status(thm)], [c_8090])).
% 13.01/5.43  tff(c_515, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_80, c_487])).
% 13.01/5.43  tff(c_34, plain, (![A_18, B_19]: (m1_subset_1(A_18, k1_zfmisc_1(B_19)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.01/5.43  tff(c_752, plain, (![A_131, B_132, C_133]: (k1_relset_1(A_131, B_132, C_133)=k1_relat_1(C_133) | ~m1_subset_1(C_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 13.01/5.43  tff(c_2407, plain, (![A_218, B_219, A_220]: (k1_relset_1(A_218, B_219, A_220)=k1_relat_1(A_220) | ~r1_tarski(A_220, k2_zfmisc_1(A_218, B_219)))), inference(resolution, [status(thm)], [c_34, c_752])).
% 13.01/5.43  tff(c_2425, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_808, c_2407])).
% 13.01/5.43  tff(c_66, plain, (![B_32, A_31, C_33]: (k1_xboole_0=B_32 | k1_relset_1(A_31, B_32, C_33)=A_31 | ~v1_funct_2(C_33, A_31, B_32) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 13.01/5.43  tff(c_2353, plain, (![B_212, A_213, C_214]: (B_212='#skF_2' | k1_relset_1(A_213, B_212, C_214)=A_213 | ~v1_funct_2(C_214, A_213, B_212) | ~m1_subset_1(C_214, k1_zfmisc_1(k2_zfmisc_1(A_213, B_212))))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_66])).
% 13.01/5.43  tff(c_12453, plain, (![B_478, A_479, A_480]: (B_478='#skF_2' | k1_relset_1(A_479, B_478, A_480)=A_479 | ~v1_funct_2(A_480, A_479, B_478) | ~r1_tarski(A_480, k2_zfmisc_1(A_479, B_478)))), inference(resolution, [status(thm)], [c_34, c_2353])).
% 13.01/5.43  tff(c_12474, plain, ('#skF_5'='#skF_2' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_808, c_12453])).
% 13.01/5.43  tff(c_12497, plain, ('#skF_5'='#skF_2' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_515, c_2425, c_12474])).
% 13.01/5.43  tff(c_12499, plain, $false, inference(negUnitSimplification, [status(thm)], [c_156, c_8144, c_12497])).
% 13.01/5.43  tff(c_12500, plain, ('#skF_5'='#skF_2'), inference(splitRight, [status(thm)], [c_7574])).
% 13.01/5.43  tff(c_12522, plain, (k4_xboole_0('#skF_6', k2_zfmisc_1('#skF_4', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12500, c_812])).
% 13.01/5.43  tff(c_12534, plain, ('#skF_6'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_305, c_134, c_12522])).
% 13.01/5.43  tff(c_12536, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1077, c_12534])).
% 13.01/5.43  tff(c_12538, plain, (k1_relat_1('#skF_6')='#skF_2'), inference(splitRight, [status(thm)], [c_253])).
% 13.01/5.43  tff(c_12543, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12538, c_156])).
% 13.01/5.43  tff(c_12932, plain, (![C_524, A_525, B_526]: (m1_subset_1(C_524, k1_zfmisc_1(k2_zfmisc_1(A_525, B_526))) | ~r2_hidden(C_524, k1_funct_2(A_525, B_526)))), inference(cnfTransformation, [status(thm)], [f_146])).
% 13.01/5.43  tff(c_13055, plain, (![C_541, A_542, B_543]: (r1_tarski(C_541, k2_zfmisc_1(A_542, B_543)) | ~r2_hidden(C_541, k1_funct_2(A_542, B_543)))), inference(resolution, [status(thm)], [c_12932, c_32])).
% 13.01/5.43  tff(c_13086, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_80, c_13055])).
% 13.01/5.43  tff(c_13090, plain, (k4_xboole_0('#skF_6', k2_zfmisc_1('#skF_4', '#skF_5'))='#skF_2'), inference(resolution, [status(thm)], [c_13086, c_203])).
% 13.01/5.43  tff(c_12, plain, (![A_6, B_7]: (r2_hidden('#skF_3'(A_6, B_7), B_7) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.01/5.43  tff(c_14, plain, (![A_6, B_7]: (r2_hidden('#skF_3'(A_6, B_7), A_6) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.01/5.43  tff(c_24, plain, (![A_14, B_15]: (r1_xboole_0(A_14, B_15) | k4_xboole_0(A_14, B_15)!=A_14)), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.01/5.43  tff(c_12881, plain, (![A_514, B_515, C_516]: (~r1_xboole_0(A_514, B_515) | ~r2_hidden(C_516, B_515) | ~r2_hidden(C_516, A_514))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.01/5.43  tff(c_13339, plain, (![C_555, B_556, A_557]: (~r2_hidden(C_555, B_556) | ~r2_hidden(C_555, A_557) | k4_xboole_0(A_557, B_556)!=A_557)), inference(resolution, [status(thm)], [c_24, c_12881])).
% 13.01/5.43  tff(c_16887, plain, (![A_2639, B_2640, A_2641]: (~r2_hidden('#skF_3'(A_2639, B_2640), A_2641) | k4_xboole_0(A_2641, A_2639)!=A_2641 | r1_xboole_0(A_2639, B_2640))), inference(resolution, [status(thm)], [c_14, c_13339])).
% 13.01/5.43  tff(c_16896, plain, (![B_2642, A_2643]: (k4_xboole_0(B_2642, A_2643)!=B_2642 | r1_xboole_0(A_2643, B_2642))), inference(resolution, [status(thm)], [c_12, c_16887])).
% 13.01/5.43  tff(c_16943, plain, (![A_2648, B_2649]: (k4_xboole_0(A_2648, B_2649)=A_2648 | k4_xboole_0(B_2649, A_2648)!=B_2649)), inference(resolution, [status(thm)], [c_16896, c_22])).
% 13.01/5.43  tff(c_16951, plain, (k4_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'), '#skF_6')=k2_zfmisc_1('#skF_4', '#skF_5') | '#skF_6'!='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_13090, c_16943])).
% 13.01/5.43  tff(c_17045, plain, ('#skF_6'!='#skF_2'), inference(splitLeft, [status(thm)], [c_16951])).
% 13.01/5.43  tff(c_12565, plain, (![A_485, B_486]: (r2_hidden('#skF_3'(A_485, B_486), B_486) | r1_xboole_0(A_485, B_486))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.01/5.43  tff(c_12575, plain, (![B_487, A_488]: (~v1_xboole_0(B_487) | r1_xboole_0(A_488, B_487))), inference(resolution, [status(thm)], [c_12565, c_2])).
% 13.01/5.43  tff(c_12580, plain, (![A_489, B_490]: (k4_xboole_0(A_489, B_490)=A_489 | ~v1_xboole_0(B_490))), inference(resolution, [status(thm)], [c_12575, c_22])).
% 13.01/5.43  tff(c_12583, plain, (![A_489]: (k4_xboole_0(A_489, '#skF_2')=A_489)), inference(resolution, [status(thm)], [c_8, c_12580])).
% 13.01/5.43  tff(c_12851, plain, (![C_510, A_511, B_512]: (v1_funct_2(C_510, A_511, B_512) | ~r2_hidden(C_510, k1_funct_2(A_511, B_512)))), inference(cnfTransformation, [status(thm)], [f_146])).
% 13.01/5.43  tff(c_12879, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_80, c_12851])).
% 13.01/5.43  tff(c_13030, plain, (![A_537, B_538, C_539]: (k1_relset_1(A_537, B_538, C_539)=k1_relat_1(C_539) | ~m1_subset_1(C_539, k1_zfmisc_1(k2_zfmisc_1(A_537, B_538))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 13.01/5.43  tff(c_14675, plain, (![A_620, B_621, A_622]: (k1_relset_1(A_620, B_621, A_622)=k1_relat_1(A_622) | ~r1_tarski(A_622, k2_zfmisc_1(A_620, B_621)))), inference(resolution, [status(thm)], [c_34, c_13030])).
% 13.01/5.43  tff(c_14678, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_13086, c_14675])).
% 13.01/5.43  tff(c_14694, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12538, c_14678])).
% 13.01/5.43  tff(c_14732, plain, (![B_625, A_626, C_627]: (B_625='#skF_2' | k1_relset_1(A_626, B_625, C_627)=A_626 | ~v1_funct_2(C_627, A_626, B_625) | ~m1_subset_1(C_627, k1_zfmisc_1(k2_zfmisc_1(A_626, B_625))))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_66])).
% 13.01/5.43  tff(c_23836, plain, (![B_2791, A_2792, A_2793]: (B_2791='#skF_2' | k1_relset_1(A_2792, B_2791, A_2793)=A_2792 | ~v1_funct_2(A_2793, A_2792, B_2791) | ~r1_tarski(A_2793, k2_zfmisc_1(A_2792, B_2791)))), inference(resolution, [status(thm)], [c_34, c_14732])).
% 13.01/5.43  tff(c_23857, plain, ('#skF_5'='#skF_2' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_13086, c_23836])).
% 13.01/5.43  tff(c_23880, plain, ('#skF_5'='#skF_2' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12879, c_14694, c_23857])).
% 13.01/5.43  tff(c_23881, plain, ('#skF_5'='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_12543, c_23880])).
% 13.01/5.43  tff(c_23910, plain, (k4_xboole_0('#skF_6', k2_zfmisc_1('#skF_4', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_23881, c_13090])).
% 13.01/5.43  tff(c_23923, plain, ('#skF_6'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12583, c_134, c_23910])).
% 13.01/5.43  tff(c_23925, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17045, c_23923])).
% 13.01/5.43  tff(c_23927, plain, ('#skF_6'='#skF_2'), inference(splitRight, [status(thm)], [c_16951])).
% 13.01/5.43  tff(c_23942, plain, (v1_funct_2('#skF_2', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_23927, c_12879])).
% 13.01/5.43  tff(c_20, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.01/5.43  tff(c_137, plain, (![A_13]: (r1_tarski('#skF_2', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_20])).
% 13.01/5.43  tff(c_14692, plain, (![A_620, B_621]: (k1_relset_1(A_620, B_621, '#skF_2')=k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_137, c_14675])).
% 13.01/5.43  tff(c_14697, plain, (![A_620, B_621]: (k1_relset_1(A_620, B_621, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_14692])).
% 13.01/5.43  tff(c_23945, plain, (r2_hidden('#skF_2', k1_funct_2('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_23927, c_80])).
% 13.01/5.43  tff(c_70, plain, (![C_38, A_36, B_37]: (m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~r2_hidden(C_38, k1_funct_2(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_146])).
% 13.01/5.43  tff(c_29902, plain, (![B_2923, A_2924, C_2925]: (B_2923='#skF_2' | k1_relset_1(A_2924, B_2923, C_2925)=A_2924 | ~v1_funct_2(C_2925, A_2924, B_2923) | ~r2_hidden(C_2925, k1_funct_2(A_2924, B_2923)))), inference(resolution, [status(thm)], [c_70, c_14732])).
% 13.01/5.43  tff(c_29932, plain, ('#skF_5'='#skF_2' | k1_relset_1('#skF_4', '#skF_5', '#skF_2')='#skF_4' | ~v1_funct_2('#skF_2', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_23945, c_29902])).
% 13.01/5.43  tff(c_29984, plain, ('#skF_5'='#skF_2' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_23942, c_14697, c_29932])).
% 13.01/5.43  tff(c_29985, plain, ('#skF_5'='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_12543, c_29984])).
% 13.01/5.43  tff(c_12584, plain, (![A_491, B_492]: (v1_xboole_0(k1_funct_2(A_491, B_492)) | ~v1_xboole_0(B_492) | v1_xboole_0(A_491))), inference(cnfTransformation, [status(thm)], [f_138])).
% 13.01/5.43  tff(c_12598, plain, (~v1_xboole_0('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_12584, c_146])).
% 13.01/5.43  tff(c_12599, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_12598])).
% 13.01/5.43  tff(c_30024, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_29985, c_12599])).
% 13.01/5.43  tff(c_30031, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_30024])).
% 13.01/5.43  tff(c_30032, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_12598])).
% 13.01/5.43  tff(c_30040, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_30032, c_131])).
% 13.01/5.43  tff(c_30046, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12543, c_30040])).
% 13.01/5.43  tff(c_30048, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitRight, [status(thm)], [c_78])).
% 13.01/5.43  tff(c_50, plain, (![A_27]: (k1_relat_1(A_27)=k1_xboole_0 | k2_relat_1(A_27)!=k1_xboole_0 | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_109])).
% 13.01/5.43  tff(c_30225, plain, (![A_2963]: (k1_relat_1(A_2963)='#skF_2' | k2_relat_1(A_2963)!='#skF_2' | ~v1_relat_1(A_2963))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_130, c_50])).
% 13.01/5.43  tff(c_30234, plain, (k1_relat_1('#skF_6')='#skF_2' | k2_relat_1('#skF_6')!='#skF_2'), inference(resolution, [status(thm)], [c_84, c_30225])).
% 13.01/5.43  tff(c_30240, plain, ('#skF_2'='#skF_4' | k2_relat_1('#skF_6')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30048, c_30234])).
% 13.01/5.43  tff(c_30241, plain, (k2_relat_1('#skF_6')!='#skF_2'), inference(splitLeft, [status(thm)], [c_30240])).
% 13.01/5.43  tff(c_30243, plain, (![A_2964]: (k2_relat_1(A_2964)='#skF_2' | k1_relat_1(A_2964)!='#skF_2' | ~v1_relat_1(A_2964))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_130, c_52])).
% 13.01/5.43  tff(c_30252, plain, (k2_relat_1('#skF_6')='#skF_2' | k1_relat_1('#skF_6')!='#skF_2'), inference(resolution, [status(thm)], [c_84, c_30243])).
% 13.01/5.43  tff(c_30258, plain, (k2_relat_1('#skF_6')='#skF_2' | '#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_30048, c_30252])).
% 13.01/5.43  tff(c_30259, plain, ('#skF_2'!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_30241, c_30258])).
% 13.01/5.43  tff(c_30562, plain, (![C_2994, A_2995, B_2996]: (m1_subset_1(C_2994, k1_zfmisc_1(k2_zfmisc_1(A_2995, B_2996))) | ~r2_hidden(C_2994, k1_funct_2(A_2995, B_2996)))), inference(cnfTransformation, [status(thm)], [f_146])).
% 13.01/5.43  tff(c_30684, plain, (![C_3011, A_3012, B_3013]: (r1_tarski(C_3011, k2_zfmisc_1(A_3012, B_3013)) | ~r2_hidden(C_3011, k1_funct_2(A_3012, B_3013)))), inference(resolution, [status(thm)], [c_30562, c_32])).
% 13.01/5.43  tff(c_30715, plain, (r1_tarski('#skF_6', k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_80, c_30684])).
% 13.01/5.43  tff(c_30489, plain, (![A_22, B_23]: (k1_relat_1(k2_zfmisc_1(A_22, B_23))=A_22 | B_23='#skF_2' | A_22='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_130, c_40])).
% 13.01/5.43  tff(c_31092, plain, (![A_3045, B_3046]: (r1_tarski(k1_relat_1(A_3045), k1_relat_1(B_3046)) | ~r1_tarski(A_3045, B_3046) | ~v1_relat_1(B_3046) | ~v1_relat_1(A_3045))), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.01/5.43  tff(c_31110, plain, (![B_3046]: (r1_tarski('#skF_4', k1_relat_1(B_3046)) | ~r1_tarski('#skF_6', B_3046) | ~v1_relat_1(B_3046) | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_30048, c_31092])).
% 13.01/5.43  tff(c_31137, plain, (![B_3047]: (r1_tarski('#skF_4', k1_relat_1(B_3047)) | ~r1_tarski('#skF_6', B_3047) | ~v1_relat_1(B_3047))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_31110])).
% 13.01/5.43  tff(c_31146, plain, (![A_22, B_23]: (r1_tarski('#skF_4', A_22) | ~r1_tarski('#skF_6', k2_zfmisc_1(A_22, B_23)) | ~v1_relat_1(k2_zfmisc_1(A_22, B_23)) | B_23='#skF_2' | A_22='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_30489, c_31137])).
% 13.01/5.43  tff(c_33627, plain, (![A_3145, B_3146]: (r1_tarski('#skF_4', A_3145) | ~r1_tarski('#skF_6', k2_zfmisc_1(A_3145, B_3146)) | B_3146='#skF_2' | A_3145='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_31146])).
% 13.01/5.43  tff(c_33634, plain, (r1_tarski('#skF_4', '#skF_4') | '#skF_5'='#skF_2' | '#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_30715, c_33627])).
% 13.01/5.43  tff(c_33647, plain, (r1_tarski('#skF_4', '#skF_4') | '#skF_5'='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_30259, c_33634])).
% 13.01/5.43  tff(c_33649, plain, ('#skF_5'='#skF_2'), inference(splitLeft, [status(thm)], [c_33647])).
% 13.01/5.43  tff(c_30170, plain, (![A_2954, B_2955]: (r2_hidden('#skF_3'(A_2954, B_2955), B_2955) | r1_xboole_0(A_2954, B_2955))), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.01/5.43  tff(c_30193, plain, (![B_2958, A_2959]: (~v1_xboole_0(B_2958) | r1_xboole_0(A_2959, B_2958))), inference(resolution, [status(thm)], [c_30170, c_2])).
% 13.01/5.43  tff(c_30198, plain, (![A_2960, B_2961]: (k4_xboole_0(A_2960, B_2961)=A_2960 | ~v1_xboole_0(B_2961))), inference(resolution, [status(thm)], [c_30193, c_22])).
% 13.01/5.43  tff(c_30204, plain, (![A_2960]: (k4_xboole_0(A_2960, '#skF_2')=A_2960)), inference(resolution, [status(thm)], [c_8, c_30198])).
% 13.01/5.43  tff(c_30123, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | k4_xboole_0(A_11, B_12)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_16])).
% 13.01/5.43  tff(c_46, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_103])).
% 13.01/5.43  tff(c_135, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_130, c_130, c_46])).
% 13.01/5.43  tff(c_30898, plain, (![A_3031, B_3032]: (r1_tarski(k2_relat_1(A_3031), k2_relat_1(B_3032)) | ~r1_tarski(A_3031, B_3032) | ~v1_relat_1(B_3032) | ~v1_relat_1(A_3031))), inference(cnfTransformation, [status(thm)], [f_100])).
% 13.01/5.43  tff(c_30913, plain, (![A_3031]: (r1_tarski(k2_relat_1(A_3031), '#skF_2') | ~r1_tarski(A_3031, '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(A_3031))), inference(superposition, [status(thm), theory('equality')], [c_135, c_30898])).
% 13.01/5.43  tff(c_30923, plain, (![A_3033]: (r1_tarski(k2_relat_1(A_3033), '#skF_2') | ~r1_tarski(A_3033, '#skF_2') | ~v1_relat_1(A_3033))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_30913])).
% 13.01/5.43  tff(c_30110, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)='#skF_2' | ~r1_tarski(A_11, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_18])).
% 13.01/5.43  tff(c_30928, plain, (![A_3033]: (k4_xboole_0(k2_relat_1(A_3033), '#skF_2')='#skF_2' | ~r1_tarski(A_3033, '#skF_2') | ~v1_relat_1(A_3033))), inference(resolution, [status(thm)], [c_30923, c_30110])).
% 13.01/5.43  tff(c_30942, plain, (![A_3034]: (k2_relat_1(A_3034)='#skF_2' | ~r1_tarski(A_3034, '#skF_2') | ~v1_relat_1(A_3034))), inference(demodulation, [status(thm), theory('equality')], [c_30204, c_30928])).
% 13.01/5.43  tff(c_30955, plain, (![A_11]: (k2_relat_1(A_11)='#skF_2' | ~v1_relat_1(A_11) | k4_xboole_0(A_11, '#skF_2')!='#skF_2')), inference(resolution, [status(thm)], [c_30123, c_30942])).
% 13.01/5.43  tff(c_30969, plain, (![A_3035]: (k2_relat_1(A_3035)='#skF_2' | ~v1_relat_1(A_3035) | A_3035!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30204, c_30955])).
% 13.01/5.43  tff(c_30985, plain, (![A_3036, B_3037]: (k2_relat_1(k2_zfmisc_1(A_3036, B_3037))='#skF_2' | k2_zfmisc_1(A_3036, B_3037)!='#skF_2')), inference(resolution, [status(thm)], [c_36, c_30969])).
% 13.01/5.43  tff(c_30238, plain, (![A_20, B_21]: (k1_relat_1(k2_zfmisc_1(A_20, B_21))='#skF_2' | k2_relat_1(k2_zfmisc_1(A_20, B_21))!='#skF_2')), inference(resolution, [status(thm)], [c_36, c_30225])).
% 13.01/5.43  tff(c_31023, plain, (![A_3036, B_3037]: (k1_relat_1(k2_zfmisc_1(A_3036, B_3037))='#skF_2' | k2_zfmisc_1(A_3036, B_3037)!='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_30985, c_30238])).
% 13.01/5.43  tff(c_31504, plain, (![B_3069]: (k4_xboole_0('#skF_4', k1_relat_1(B_3069))='#skF_2' | ~r1_tarski('#skF_6', B_3069) | ~v1_relat_1(B_3069))), inference(resolution, [status(thm)], [c_31137, c_30110])).
% 13.01/5.43  tff(c_31519, plain, (![A_3036, B_3037]: (k4_xboole_0('#skF_4', '#skF_2')='#skF_2' | ~r1_tarski('#skF_6', k2_zfmisc_1(A_3036, B_3037)) | ~v1_relat_1(k2_zfmisc_1(A_3036, B_3037)) | k2_zfmisc_1(A_3036, B_3037)!='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_31023, c_31504])).
% 13.01/5.43  tff(c_31540, plain, (![A_3036, B_3037]: ('#skF_2'='#skF_4' | ~r1_tarski('#skF_6', k2_zfmisc_1(A_3036, B_3037)) | k2_zfmisc_1(A_3036, B_3037)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30204, c_31519])).
% 13.01/5.43  tff(c_31672, plain, (![A_3076, B_3077]: (~r1_tarski('#skF_6', k2_zfmisc_1(A_3076, B_3077)) | k2_zfmisc_1(A_3076, B_3077)!='#skF_2')), inference(negUnitSimplification, [status(thm)], [c_30259, c_31540])).
% 13.01/5.43  tff(c_31685, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!='#skF_2'), inference(resolution, [status(thm)], [c_30715, c_31672])).
% 13.01/5.43  tff(c_33659, plain, (k2_zfmisc_1('#skF_4', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_33649, c_31685])).
% 13.01/5.43  tff(c_33682, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_33659])).
% 13.01/5.43  tff(c_33684, plain, ('#skF_5'!='#skF_2'), inference(splitRight, [status(thm)], [c_33647])).
% 13.01/5.43  tff(c_30047, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_78])).
% 13.01/5.43  tff(c_30466, plain, (![A_22, B_23]: (k2_relat_1(k2_zfmisc_1(A_22, B_23))=B_23 | B_23='#skF_2' | A_22='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_130, c_130, c_38])).
% 13.01/5.43  tff(c_30907, plain, (![A_3031, B_23, A_22]: (r1_tarski(k2_relat_1(A_3031), B_23) | ~r1_tarski(A_3031, k2_zfmisc_1(A_22, B_23)) | ~v1_relat_1(k2_zfmisc_1(A_22, B_23)) | ~v1_relat_1(A_3031) | B_23='#skF_2' | A_22='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_30466, c_30898])).
% 13.01/5.43  tff(c_42135, plain, (![A_3347, B_3348, A_3349]: (r1_tarski(k2_relat_1(A_3347), B_3348) | ~r1_tarski(A_3347, k2_zfmisc_1(A_3349, B_3348)) | ~v1_relat_1(A_3347) | B_3348='#skF_2' | A_3349='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_30907])).
% 13.01/5.43  tff(c_42151, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | ~v1_relat_1('#skF_6') | '#skF_5'='#skF_2' | '#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_30715, c_42135])).
% 13.01/5.43  tff(c_42172, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_5') | '#skF_5'='#skF_2' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_42151])).
% 13.01/5.43  tff(c_42174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30259, c_33684, c_30047, c_42172])).
% 13.01/5.43  tff(c_42175, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_30240])).
% 13.01/5.43  tff(c_42188, plain, (![A_13]: (r1_tarski('#skF_4', A_13))), inference(demodulation, [status(thm), theory('equality')], [c_42175, c_137])).
% 13.01/5.43  tff(c_42176, plain, (k2_relat_1('#skF_6')='#skF_2'), inference(splitRight, [status(thm)], [c_30240])).
% 13.01/5.43  tff(c_42201, plain, (k2_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42175, c_42176])).
% 13.01/5.43  tff(c_42202, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_42201, c_30047])).
% 13.01/5.43  tff(c_42223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42188, c_42202])).
% 13.01/5.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.01/5.43  
% 13.01/5.43  Inference rules
% 13.01/5.43  ----------------------
% 13.01/5.43  #Ref     : 0
% 13.01/5.43  #Sup     : 9209
% 13.01/5.43  #Fact    : 6
% 13.01/5.43  #Define  : 0
% 13.01/5.43  #Split   : 37
% 13.01/5.43  #Chain   : 0
% 13.01/5.43  #Close   : 0
% 13.01/5.43  
% 13.01/5.43  Ordering : KBO
% 13.01/5.43  
% 13.01/5.43  Simplification rules
% 13.01/5.43  ----------------------
% 13.01/5.43  #Subsume      : 1999
% 13.01/5.43  #Demod        : 6392
% 13.01/5.43  #Tautology    : 4815
% 13.01/5.43  #SimpNegUnit  : 381
% 13.01/5.43  #BackRed      : 349
% 13.01/5.43  
% 13.01/5.43  #Partial instantiations: 89
% 13.01/5.43  #Strategies tried      : 1
% 13.01/5.43  
% 13.01/5.43  Timing (in seconds)
% 13.01/5.43  ----------------------
% 13.01/5.44  Preprocessing        : 0.35
% 13.01/5.44  Parsing              : 0.18
% 13.01/5.44  CNF conversion       : 0.02
% 13.01/5.44  Main loop            : 4.27
% 13.01/5.44  Inferencing          : 1.16
% 13.01/5.44  Reduction            : 1.35
% 13.01/5.44  Demodulation         : 0.95
% 13.01/5.44  BG Simplification    : 0.12
% 13.01/5.44  Subsumption          : 1.40
% 13.01/5.44  Abstraction          : 0.14
% 13.01/5.44  MUC search           : 0.00
% 13.01/5.44  Cooper               : 0.00
% 13.01/5.44  Total                : 4.70
% 13.01/5.44  Index Insertion      : 0.00
% 13.01/5.44  Index Deletion       : 0.00
% 13.01/5.44  Index Matching       : 0.00
% 13.01/5.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
