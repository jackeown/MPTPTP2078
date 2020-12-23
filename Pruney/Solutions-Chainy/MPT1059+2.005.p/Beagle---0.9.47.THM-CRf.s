%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:33 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 351 expanded)
%              Number of leaves         :   36 ( 132 expanded)
%              Depth                    :   14
%              Number of atoms          :  163 ( 758 expanded)
%              Number of equality atoms :   60 ( 221 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_146,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,A,B)
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
               => ! [D] :
                    ( m1_subset_1(D,A)
                   => k7_partfun1(B,C,D) = k3_funct_2(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_2)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_102,axiom,(
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

tff(f_113,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_126,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_63,plain,(
    ! [A_44] :
      ( k1_xboole_0 = A_44
      | ~ v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_67,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_63])).

tff(c_8,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_73,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_67,c_8])).

tff(c_48,plain,(
    m1_subset_1('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_132,plain,(
    ! [C_58,B_59,A_60] :
      ( v5_relat_1(C_58,B_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_60,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_142,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_132])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( r2_hidden(A_7,B_8)
      | v1_xboole_0(B_8)
      | ~ m1_subset_1(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_122,plain,(
    ! [C_54,A_55,B_56] :
      ( v1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_130,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_122])).

tff(c_54,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_52,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_156,plain,(
    ! [A_67,B_68,C_69] :
      ( k1_relset_1(A_67,B_68,C_69) = k1_relat_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_166,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_156])).

tff(c_40,plain,(
    ! [B_23,A_22,C_24] :
      ( k1_xboole_0 = B_23
      | k1_relset_1(A_22,B_23,C_24) = A_22
      | ~ v1_funct_2(C_24,A_22,B_23)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_183,plain,(
    ! [B_82,A_83,C_84] :
      ( B_82 = '#skF_1'
      | k1_relset_1(A_83,B_82,C_84) = A_83
      | ~ v1_funct_2(C_84,A_83,B_82)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_83,B_82))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_40])).

tff(c_186,plain,
    ( '#skF_3' = '#skF_1'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_183])).

tff(c_195,plain,
    ( '#skF_3' = '#skF_1'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_166,c_186])).

tff(c_197,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_195])).

tff(c_238,plain,(
    ! [A_91,B_92,C_93] :
      ( k7_partfun1(A_91,B_92,C_93) = k1_funct_1(B_92,C_93)
      | ~ r2_hidden(C_93,k1_relat_1(B_92))
      | ~ v1_funct_1(B_92)
      | ~ v5_relat_1(B_92,A_91)
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_240,plain,(
    ! [A_91,C_93] :
      ( k7_partfun1(A_91,'#skF_4',C_93) = k1_funct_1('#skF_4',C_93)
      | ~ r2_hidden(C_93,'#skF_2')
      | ~ v1_funct_1('#skF_4')
      | ~ v5_relat_1('#skF_4',A_91)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_238])).

tff(c_247,plain,(
    ! [A_94,C_95] :
      ( k7_partfun1(A_94,'#skF_4',C_95) = k1_funct_1('#skF_4',C_95)
      | ~ r2_hidden(C_95,'#skF_2')
      | ~ v5_relat_1('#skF_4',A_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_54,c_240])).

tff(c_250,plain,(
    ! [A_94,A_7] :
      ( k7_partfun1(A_94,'#skF_4',A_7) = k1_funct_1('#skF_4',A_7)
      | ~ v5_relat_1('#skF_4',A_94)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_7,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_14,c_247])).

tff(c_254,plain,(
    ! [A_96,A_97] :
      ( k7_partfun1(A_96,'#skF_4',A_97) = k1_funct_1('#skF_4',A_97)
      | ~ v5_relat_1('#skF_4',A_96)
      | ~ m1_subset_1(A_97,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_250])).

tff(c_258,plain,(
    ! [A_98] :
      ( k7_partfun1('#skF_3','#skF_4',A_98) = k1_funct_1('#skF_4',A_98)
      | ~ m1_subset_1(A_98,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_142,c_254])).

tff(c_262,plain,(
    k7_partfun1('#skF_3','#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_258])).

tff(c_46,plain,(
    k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') != k7_partfun1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_263,plain,(
    k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') != k1_funct_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_46])).

tff(c_275,plain,(
    ! [A_102,B_103,C_104,D_105] :
      ( k3_funct_2(A_102,B_103,C_104,D_105) = k1_funct_1(C_104,D_105)
      | ~ m1_subset_1(D_105,A_102)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103)))
      | ~ v1_funct_2(C_104,A_102,B_103)
      | ~ v1_funct_1(C_104)
      | v1_xboole_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_279,plain,(
    ! [B_103,C_104] :
      ( k3_funct_2('#skF_2',B_103,C_104,'#skF_5') = k1_funct_1(C_104,'#skF_5')
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_103)))
      | ~ v1_funct_2(C_104,'#skF_2',B_103)
      | ~ v1_funct_1(C_104)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_48,c_275])).

tff(c_284,plain,(
    ! [B_106,C_107] :
      ( k3_funct_2('#skF_2',B_106,C_107,'#skF_5') = k1_funct_1(C_107,'#skF_5')
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_106)))
      | ~ v1_funct_2(C_107,'#skF_2',B_106)
      | ~ v1_funct_1(C_107) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_279])).

tff(c_287,plain,
    ( k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_5')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_284])).

tff(c_294,plain,(
    k3_funct_2('#skF_2','#skF_3','#skF_4','#skF_5') = k1_funct_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_287])).

tff(c_296,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_263,c_294])).

tff(c_297,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_104,plain,(
    ! [B_50,A_51] :
      ( v1_xboole_0(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51))
      | ~ v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_108,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_104])).

tff(c_109,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_316,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_109])).

tff(c_322,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_73,c_316])).

tff(c_323,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_324,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_68,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_2])).

tff(c_328,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_323,c_68])).

tff(c_350,plain,(
    ! [A_112] :
      ( A_112 = '#skF_4'
      | ~ v1_xboole_0(A_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_68])).

tff(c_357,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_324,c_350])).

tff(c_332,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_328,c_67])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( k1_xboole_0 = B_3
      | k1_xboole_0 = A_2
      | k2_zfmisc_1(A_2,B_3) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_406,plain,(
    ! [B_118,A_119] :
      ( B_118 = '#skF_4'
      | A_119 = '#skF_4'
      | k2_zfmisc_1(A_119,B_118) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_332,c_332,c_6])).

tff(c_416,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_406])).

tff(c_421,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_416])).

tff(c_426,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_421,c_58])).

tff(c_430,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_426])).

tff(c_431,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_416])).

tff(c_56,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_446,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_56])).

tff(c_450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_446])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:07:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.40  
% 2.73/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.41  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k7_partfun1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.73/1.41  
% 2.73/1.41  %Foreground sorts:
% 2.73/1.41  
% 2.73/1.41  
% 2.73/1.41  %Background operators:
% 2.73/1.41  
% 2.73/1.41  
% 2.73/1.41  %Foreground operators:
% 2.73/1.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.73/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.73/1.41  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 2.73/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.73/1.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.73/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.73/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.73/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.73/1.41  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.73/1.41  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.73/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.73/1.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.73/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.73/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.73/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.73/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.41  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.73/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.73/1.41  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.73/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.73/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.73/1.41  
% 2.73/1.42  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 2.73/1.42  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.73/1.42  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.73/1.42  tff(f_146, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (m1_subset_1(D, A) => (k7_partfun1(B, C, D) = k3_funct_2(A, B, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_funct_2)).
% 2.73/1.42  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.73/1.42  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.73/1.42  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.73/1.42  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.73/1.42  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.73/1.42  tff(f_113, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 2.73/1.42  tff(f_126, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 2.73/1.42  tff(f_44, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.73/1.42  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.73/1.42  tff(c_63, plain, (![A_44]: (k1_xboole_0=A_44 | ~v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.73/1.42  tff(c_67, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_63])).
% 2.73/1.42  tff(c_8, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.73/1.42  tff(c_73, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_67, c_67, c_8])).
% 2.73/1.42  tff(c_48, plain, (m1_subset_1('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.73/1.42  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.73/1.42  tff(c_132, plain, (![C_58, B_59, A_60]: (v5_relat_1(C_58, B_59) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_60, B_59))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.73/1.42  tff(c_142, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_132])).
% 2.73/1.42  tff(c_58, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.73/1.42  tff(c_14, plain, (![A_7, B_8]: (r2_hidden(A_7, B_8) | v1_xboole_0(B_8) | ~m1_subset_1(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.73/1.42  tff(c_122, plain, (![C_54, A_55, B_56]: (v1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.73/1.42  tff(c_130, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_122])).
% 2.73/1.42  tff(c_54, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.73/1.42  tff(c_52, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.73/1.42  tff(c_156, plain, (![A_67, B_68, C_69]: (k1_relset_1(A_67, B_68, C_69)=k1_relat_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.73/1.42  tff(c_166, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_156])).
% 2.73/1.42  tff(c_40, plain, (![B_23, A_22, C_24]: (k1_xboole_0=B_23 | k1_relset_1(A_22, B_23, C_24)=A_22 | ~v1_funct_2(C_24, A_22, B_23) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.73/1.42  tff(c_183, plain, (![B_82, A_83, C_84]: (B_82='#skF_1' | k1_relset_1(A_83, B_82, C_84)=A_83 | ~v1_funct_2(C_84, A_83, B_82) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_83, B_82))))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_40])).
% 2.73/1.42  tff(c_186, plain, ('#skF_3'='#skF_1' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_183])).
% 2.73/1.42  tff(c_195, plain, ('#skF_3'='#skF_1' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_166, c_186])).
% 2.73/1.42  tff(c_197, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_195])).
% 2.73/1.42  tff(c_238, plain, (![A_91, B_92, C_93]: (k7_partfun1(A_91, B_92, C_93)=k1_funct_1(B_92, C_93) | ~r2_hidden(C_93, k1_relat_1(B_92)) | ~v1_funct_1(B_92) | ~v5_relat_1(B_92, A_91) | ~v1_relat_1(B_92))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.73/1.42  tff(c_240, plain, (![A_91, C_93]: (k7_partfun1(A_91, '#skF_4', C_93)=k1_funct_1('#skF_4', C_93) | ~r2_hidden(C_93, '#skF_2') | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', A_91) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_197, c_238])).
% 2.73/1.42  tff(c_247, plain, (![A_94, C_95]: (k7_partfun1(A_94, '#skF_4', C_95)=k1_funct_1('#skF_4', C_95) | ~r2_hidden(C_95, '#skF_2') | ~v5_relat_1('#skF_4', A_94))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_54, c_240])).
% 2.73/1.42  tff(c_250, plain, (![A_94, A_7]: (k7_partfun1(A_94, '#skF_4', A_7)=k1_funct_1('#skF_4', A_7) | ~v5_relat_1('#skF_4', A_94) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_7, '#skF_2'))), inference(resolution, [status(thm)], [c_14, c_247])).
% 2.73/1.42  tff(c_254, plain, (![A_96, A_97]: (k7_partfun1(A_96, '#skF_4', A_97)=k1_funct_1('#skF_4', A_97) | ~v5_relat_1('#skF_4', A_96) | ~m1_subset_1(A_97, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_58, c_250])).
% 2.73/1.42  tff(c_258, plain, (![A_98]: (k7_partfun1('#skF_3', '#skF_4', A_98)=k1_funct_1('#skF_4', A_98) | ~m1_subset_1(A_98, '#skF_2'))), inference(resolution, [status(thm)], [c_142, c_254])).
% 2.73/1.42  tff(c_262, plain, (k7_partfun1('#skF_3', '#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_258])).
% 2.73/1.42  tff(c_46, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k7_partfun1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.73/1.42  tff(c_263, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')!=k1_funct_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_262, c_46])).
% 2.73/1.42  tff(c_275, plain, (![A_102, B_103, C_104, D_105]: (k3_funct_2(A_102, B_103, C_104, D_105)=k1_funct_1(C_104, D_105) | ~m1_subset_1(D_105, A_102) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))) | ~v1_funct_2(C_104, A_102, B_103) | ~v1_funct_1(C_104) | v1_xboole_0(A_102))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.73/1.42  tff(c_279, plain, (![B_103, C_104]: (k3_funct_2('#skF_2', B_103, C_104, '#skF_5')=k1_funct_1(C_104, '#skF_5') | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_103))) | ~v1_funct_2(C_104, '#skF_2', B_103) | ~v1_funct_1(C_104) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_48, c_275])).
% 2.73/1.42  tff(c_284, plain, (![B_106, C_107]: (k3_funct_2('#skF_2', B_106, C_107, '#skF_5')=k1_funct_1(C_107, '#skF_5') | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_106))) | ~v1_funct_2(C_107, '#skF_2', B_106) | ~v1_funct_1(C_107))), inference(negUnitSimplification, [status(thm)], [c_58, c_279])).
% 2.73/1.42  tff(c_287, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_5') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_284])).
% 2.73/1.42  tff(c_294, plain, (k3_funct_2('#skF_2', '#skF_3', '#skF_4', '#skF_5')=k1_funct_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_287])).
% 2.73/1.42  tff(c_296, plain, $false, inference(negUnitSimplification, [status(thm)], [c_263, c_294])).
% 2.73/1.42  tff(c_297, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_195])).
% 2.73/1.42  tff(c_104, plain, (![B_50, A_51]: (v1_xboole_0(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)) | ~v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.73/1.42  tff(c_108, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_50, c_104])).
% 2.73/1.42  tff(c_109, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_108])).
% 2.73/1.42  tff(c_316, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_297, c_109])).
% 2.73/1.42  tff(c_322, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_73, c_316])).
% 2.73/1.42  tff(c_323, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_108])).
% 2.73/1.42  tff(c_324, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_108])).
% 2.73/1.42  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.73/1.42  tff(c_68, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_2])).
% 2.73/1.42  tff(c_328, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_323, c_68])).
% 2.73/1.42  tff(c_350, plain, (![A_112]: (A_112='#skF_4' | ~v1_xboole_0(A_112))), inference(demodulation, [status(thm), theory('equality')], [c_328, c_68])).
% 2.73/1.42  tff(c_357, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_324, c_350])).
% 2.73/1.42  tff(c_332, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_328, c_67])).
% 2.73/1.42  tff(c_6, plain, (![B_3, A_2]: (k1_xboole_0=B_3 | k1_xboole_0=A_2 | k2_zfmisc_1(A_2, B_3)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.73/1.42  tff(c_406, plain, (![B_118, A_119]: (B_118='#skF_4' | A_119='#skF_4' | k2_zfmisc_1(A_119, B_118)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_332, c_332, c_332, c_6])).
% 2.73/1.42  tff(c_416, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_357, c_406])).
% 2.73/1.42  tff(c_421, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_416])).
% 2.73/1.42  tff(c_426, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_421, c_58])).
% 2.73/1.42  tff(c_430, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_323, c_426])).
% 2.73/1.42  tff(c_431, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_416])).
% 2.73/1.42  tff(c_56, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_146])).
% 2.73/1.42  tff(c_446, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_431, c_56])).
% 2.73/1.42  tff(c_450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_323, c_446])).
% 2.73/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/1.42  
% 2.73/1.42  Inference rules
% 2.73/1.42  ----------------------
% 2.73/1.42  #Ref     : 0
% 2.73/1.42  #Sup     : 82
% 2.73/1.42  #Fact    : 0
% 2.73/1.42  #Define  : 0
% 2.73/1.42  #Split   : 4
% 2.73/1.42  #Chain   : 0
% 2.73/1.42  #Close   : 0
% 2.73/1.42  
% 2.73/1.42  Ordering : KBO
% 2.73/1.42  
% 2.73/1.42  Simplification rules
% 2.73/1.42  ----------------------
% 2.73/1.42  #Subsume      : 9
% 2.73/1.42  #Demod        : 93
% 2.73/1.42  #Tautology    : 49
% 2.73/1.42  #SimpNegUnit  : 5
% 2.73/1.42  #BackRed      : 26
% 2.73/1.42  
% 2.73/1.42  #Partial instantiations: 0
% 2.73/1.42  #Strategies tried      : 1
% 2.73/1.42  
% 2.73/1.42  Timing (in seconds)
% 2.73/1.42  ----------------------
% 2.73/1.43  Preprocessing        : 0.33
% 2.73/1.43  Parsing              : 0.17
% 2.73/1.43  CNF conversion       : 0.02
% 2.73/1.43  Main loop            : 0.27
% 2.73/1.43  Inferencing          : 0.09
% 2.73/1.43  Reduction            : 0.09
% 2.73/1.43  Demodulation         : 0.06
% 2.73/1.43  BG Simplification    : 0.02
% 2.73/1.43  Subsumption          : 0.05
% 2.73/1.43  Abstraction          : 0.01
% 2.73/1.43  MUC search           : 0.00
% 2.73/1.43  Cooper               : 0.00
% 2.73/1.43  Total                : 0.63
% 2.73/1.43  Index Insertion      : 0.00
% 2.73/1.43  Index Deletion       : 0.00
% 2.73/1.43  Index Matching       : 0.00
% 2.73/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
