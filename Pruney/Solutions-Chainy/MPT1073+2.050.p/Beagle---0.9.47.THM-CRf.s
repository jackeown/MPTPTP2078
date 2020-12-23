%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:04 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :  102 (1453 expanded)
%              Number of leaves         :   38 ( 520 expanded)
%              Depth                    :   14
%              Number of atoms          :  161 (4590 expanded)
%              Number of equality atoms :   51 (1894 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff(f_45,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_120,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_86,axiom,(
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

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ! [D] :
            ~ ( r2_hidden(D,B)
              & ! [E] :
                  ~ ( r2_hidden(E,A)
                    & D = k1_funct_1(C,E) ) )
       => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_12,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_56,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_89,plain,(
    ! [B_80,A_81] :
      ( v1_relat_1(B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_81))
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_96,plain,
    ( v1_relat_1('#skF_10')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_56,c_89])).

tff(c_100,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_96])).

tff(c_60,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_16,plain,(
    ! [A_12,C_48] :
      ( k1_funct_1(A_12,'#skF_5'(A_12,k2_relat_1(A_12),C_48)) = C_48
      | ~ r2_hidden(C_48,k2_relat_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_58,plain,(
    v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_128,plain,(
    ! [A_86,B_87,C_88] :
      ( k1_relset_1(A_86,B_87,C_88) = k1_relat_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_137,plain,(
    k1_relset_1('#skF_8','#skF_9','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_56,c_128])).

tff(c_246,plain,(
    ! [B_117,A_118,C_119] :
      ( k1_xboole_0 = B_117
      | k1_relset_1(A_118,B_117,C_119) = A_118
      | ~ v1_funct_2(C_119,A_118,B_117)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_118,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_253,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relset_1('#skF_8','#skF_9','#skF_10') = '#skF_8'
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_56,c_246])).

tff(c_257,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_137,c_253])).

tff(c_258,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_257])).

tff(c_193,plain,(
    ! [A_105,C_106] :
      ( r2_hidden('#skF_5'(A_105,k2_relat_1(A_105),C_106),k1_relat_1(A_105))
      | ~ r2_hidden(C_106,k2_relat_1(A_105))
      | ~ v1_funct_1(A_105)
      | ~ v1_relat_1(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_204,plain,(
    ! [A_105,C_106] :
      ( m1_subset_1('#skF_5'(A_105,k2_relat_1(A_105),C_106),k1_relat_1(A_105))
      | ~ r2_hidden(C_106,k2_relat_1(A_105))
      | ~ v1_funct_1(A_105)
      | ~ v1_relat_1(A_105) ) ),
    inference(resolution,[status(thm)],[c_193,c_8])).

tff(c_264,plain,(
    ! [C_106] :
      ( m1_subset_1('#skF_5'('#skF_10',k2_relat_1('#skF_10'),C_106),'#skF_8')
      | ~ r2_hidden(C_106,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_204])).

tff(c_320,plain,(
    ! [C_122] :
      ( m1_subset_1('#skF_5'('#skF_10',k2_relat_1('#skF_10'),C_122),'#skF_8')
      | ~ r2_hidden(C_122,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_60,c_264])).

tff(c_52,plain,(
    ! [E_70] :
      ( k1_funct_1('#skF_10',E_70) != '#skF_7'
      | ~ m1_subset_1(E_70,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_334,plain,(
    ! [C_124] :
      ( k1_funct_1('#skF_10','#skF_5'('#skF_10',k2_relat_1('#skF_10'),C_124)) != '#skF_7'
      | ~ r2_hidden(C_124,k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_320,c_52])).

tff(c_338,plain,(
    ! [C_48] :
      ( C_48 != '#skF_7'
      | ~ r2_hidden(C_48,k2_relat_1('#skF_10'))
      | ~ r2_hidden(C_48,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_334])).

tff(c_341,plain,(
    ~ r2_hidden('#skF_7',k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_60,c_338])).

tff(c_102,plain,(
    ! [A_83,B_84,C_85] :
      ( k2_relset_1(A_83,B_84,C_85) = k2_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_111,plain,(
    k2_relset_1('#skF_8','#skF_9','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_56,c_102])).

tff(c_54,plain,(
    r2_hidden('#skF_7',k2_relset_1('#skF_8','#skF_9','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_114,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_54])).

tff(c_343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_341,c_114])).

tff(c_344,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_352,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_6])).

tff(c_345,plain,(
    k1_relat_1('#skF_10') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_38,plain,(
    ! [C_60,A_58] :
      ( k1_xboole_0 = C_60
      | ~ v1_funct_2(C_60,A_58,k1_xboole_0)
      | k1_xboole_0 = A_58
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_389,plain,(
    ! [C_128,A_129] :
      ( C_128 = '#skF_9'
      | ~ v1_funct_2(C_128,A_129,'#skF_9')
      | A_129 = '#skF_9'
      | ~ m1_subset_1(C_128,k1_zfmisc_1(k2_zfmisc_1(A_129,'#skF_9'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_344,c_344,c_344,c_38])).

tff(c_396,plain,
    ( '#skF_10' = '#skF_9'
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_9')
    | '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_56,c_389])).

tff(c_400,plain,
    ( '#skF_10' = '#skF_9'
    | '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_396])).

tff(c_401,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_400])).

tff(c_409,plain,(
    v1_funct_2('#skF_10','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_58])).

tff(c_406,plain,(
    k1_relset_1('#skF_8','#skF_8','#skF_10') = k1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_137])).

tff(c_408,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_56])).

tff(c_44,plain,(
    ! [B_59,C_60] :
      ( k1_relset_1(k1_xboole_0,B_59,C_60) = k1_xboole_0
      | ~ v1_funct_2(C_60,k1_xboole_0,B_59)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_348,plain,(
    ! [B_59,C_60] :
      ( k1_relset_1('#skF_9',B_59,C_60) = '#skF_9'
      | ~ v1_funct_2(C_60,'#skF_9',B_59)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1('#skF_9',B_59))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_344,c_344,c_344,c_44])).

tff(c_490,plain,(
    ! [B_135,C_136] :
      ( k1_relset_1('#skF_8',B_135,C_136) = '#skF_8'
      | ~ v1_funct_2(C_136,'#skF_8',B_135)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1('#skF_8',B_135))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_401,c_401,c_401,c_348])).

tff(c_493,plain,
    ( k1_relset_1('#skF_8','#skF_8','#skF_10') = '#skF_8'
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_408,c_490])).

tff(c_500,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_406,c_493])).

tff(c_502,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_345,c_500])).

tff(c_503,plain,(
    '#skF_10' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_400])).

tff(c_517,plain,(
    v1_funct_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_60])).

tff(c_516,plain,(
    v1_funct_2('#skF_9','#skF_8','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_58])).

tff(c_511,plain,(
    k2_relset_1('#skF_8','#skF_9','#skF_9') = k2_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_503,c_111])).

tff(c_515,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_56])).

tff(c_665,plain,(
    ! [A_155,B_156,C_157] :
      ( r2_hidden('#skF_6'(A_155,B_156,C_157),B_156)
      | k2_relset_1(A_155,B_156,C_157) = B_156
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156)))
      | ~ v1_funct_2(C_157,A_155,B_156)
      | ~ v1_funct_1(C_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_667,plain,
    ( r2_hidden('#skF_6'('#skF_8','#skF_9','#skF_9'),'#skF_9')
    | k2_relset_1('#skF_8','#skF_9','#skF_9') = '#skF_9'
    | ~ v1_funct_2('#skF_9','#skF_8','#skF_9')
    | ~ v1_funct_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_515,c_665])).

tff(c_673,plain,
    ( r2_hidden('#skF_6'('#skF_8','#skF_9','#skF_9'),'#skF_9')
    | k2_relat_1('#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_516,c_511,c_667])).

tff(c_675,plain,(
    k2_relat_1('#skF_9') = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_673])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_66,plain,(
    ~ v1_xboole_0(k2_relset_1('#skF_8','#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_54,c_2])).

tff(c_113,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_66])).

tff(c_510,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_503,c_113])).

tff(c_679,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_675,c_510])).

tff(c_682,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_679])).

tff(c_683,plain,(
    r2_hidden('#skF_6'('#skF_8','#skF_9','#skF_9'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_673])).

tff(c_690,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_683,c_2])).

tff(c_695,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_690])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:25:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.47  
% 3.02/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.47  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4
% 3.02/1.47  
% 3.02/1.47  %Foreground sorts:
% 3.02/1.47  
% 3.02/1.47  
% 3.02/1.47  %Background operators:
% 3.02/1.47  
% 3.02/1.47  
% 3.02/1.47  %Foreground operators:
% 3.02/1.47  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.02/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.02/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.02/1.47  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.02/1.47  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.02/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.02/1.47  tff('#skF_7', type, '#skF_7': $i).
% 3.02/1.47  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.02/1.47  tff('#skF_10', type, '#skF_10': $i).
% 3.02/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.02/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.02/1.47  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.02/1.47  tff('#skF_9', type, '#skF_9': $i).
% 3.02/1.47  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.02/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.02/1.47  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.02/1.47  tff('#skF_8', type, '#skF_8': $i).
% 3.02/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.02/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.02/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.02/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.02/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.02/1.47  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.02/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.02/1.47  
% 3.20/1.49  tff(f_45, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.20/1.49  tff(f_120, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 3.20/1.49  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.20/1.49  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 3.20/1.49  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.20/1.49  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.20/1.49  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.20/1.49  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.20/1.49  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.20/1.49  tff(f_104, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 3.20/1.49  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.20/1.49  tff(c_12, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.20/1.49  tff(c_56, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.20/1.49  tff(c_89, plain, (![B_80, A_81]: (v1_relat_1(B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(A_81)) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.20/1.49  tff(c_96, plain, (v1_relat_1('#skF_10') | ~v1_relat_1(k2_zfmisc_1('#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_56, c_89])).
% 3.20/1.49  tff(c_100, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_96])).
% 3.20/1.49  tff(c_60, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.20/1.49  tff(c_16, plain, (![A_12, C_48]: (k1_funct_1(A_12, '#skF_5'(A_12, k2_relat_1(A_12), C_48))=C_48 | ~r2_hidden(C_48, k2_relat_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.20/1.49  tff(c_58, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.20/1.49  tff(c_128, plain, (![A_86, B_87, C_88]: (k1_relset_1(A_86, B_87, C_88)=k1_relat_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.20/1.49  tff(c_137, plain, (k1_relset_1('#skF_8', '#skF_9', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_56, c_128])).
% 3.20/1.49  tff(c_246, plain, (![B_117, A_118, C_119]: (k1_xboole_0=B_117 | k1_relset_1(A_118, B_117, C_119)=A_118 | ~v1_funct_2(C_119, A_118, B_117) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_118, B_117))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.20/1.49  tff(c_253, plain, (k1_xboole_0='#skF_9' | k1_relset_1('#skF_8', '#skF_9', '#skF_10')='#skF_8' | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_56, c_246])).
% 3.20/1.49  tff(c_257, plain, (k1_xboole_0='#skF_9' | k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_137, c_253])).
% 3.20/1.49  tff(c_258, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(splitLeft, [status(thm)], [c_257])).
% 3.20/1.49  tff(c_193, plain, (![A_105, C_106]: (r2_hidden('#skF_5'(A_105, k2_relat_1(A_105), C_106), k1_relat_1(A_105)) | ~r2_hidden(C_106, k2_relat_1(A_105)) | ~v1_funct_1(A_105) | ~v1_relat_1(A_105))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.20/1.49  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(A_5, B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.20/1.49  tff(c_204, plain, (![A_105, C_106]: (m1_subset_1('#skF_5'(A_105, k2_relat_1(A_105), C_106), k1_relat_1(A_105)) | ~r2_hidden(C_106, k2_relat_1(A_105)) | ~v1_funct_1(A_105) | ~v1_relat_1(A_105))), inference(resolution, [status(thm)], [c_193, c_8])).
% 3.20/1.49  tff(c_264, plain, (![C_106]: (m1_subset_1('#skF_5'('#skF_10', k2_relat_1('#skF_10'), C_106), '#skF_8') | ~r2_hidden(C_106, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_258, c_204])).
% 3.20/1.49  tff(c_320, plain, (![C_122]: (m1_subset_1('#skF_5'('#skF_10', k2_relat_1('#skF_10'), C_122), '#skF_8') | ~r2_hidden(C_122, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_60, c_264])).
% 3.20/1.49  tff(c_52, plain, (![E_70]: (k1_funct_1('#skF_10', E_70)!='#skF_7' | ~m1_subset_1(E_70, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.20/1.49  tff(c_334, plain, (![C_124]: (k1_funct_1('#skF_10', '#skF_5'('#skF_10', k2_relat_1('#skF_10'), C_124))!='#skF_7' | ~r2_hidden(C_124, k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_320, c_52])).
% 3.20/1.49  tff(c_338, plain, (![C_48]: (C_48!='#skF_7' | ~r2_hidden(C_48, k2_relat_1('#skF_10')) | ~r2_hidden(C_48, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_334])).
% 3.20/1.49  tff(c_341, plain, (~r2_hidden('#skF_7', k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_60, c_338])).
% 3.20/1.49  tff(c_102, plain, (![A_83, B_84, C_85]: (k2_relset_1(A_83, B_84, C_85)=k2_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.20/1.49  tff(c_111, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_56, c_102])).
% 3.20/1.49  tff(c_54, plain, (r2_hidden('#skF_7', k2_relset_1('#skF_8', '#skF_9', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.20/1.49  tff(c_114, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_54])).
% 3.20/1.49  tff(c_343, plain, $false, inference(negUnitSimplification, [status(thm)], [c_341, c_114])).
% 3.20/1.49  tff(c_344, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_257])).
% 3.20/1.49  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.20/1.49  tff(c_352, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_344, c_6])).
% 3.20/1.49  tff(c_345, plain, (k1_relat_1('#skF_10')!='#skF_8'), inference(splitRight, [status(thm)], [c_257])).
% 3.20/1.49  tff(c_38, plain, (![C_60, A_58]: (k1_xboole_0=C_60 | ~v1_funct_2(C_60, A_58, k1_xboole_0) | k1_xboole_0=A_58 | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.20/1.49  tff(c_389, plain, (![C_128, A_129]: (C_128='#skF_9' | ~v1_funct_2(C_128, A_129, '#skF_9') | A_129='#skF_9' | ~m1_subset_1(C_128, k1_zfmisc_1(k2_zfmisc_1(A_129, '#skF_9'))))), inference(demodulation, [status(thm), theory('equality')], [c_344, c_344, c_344, c_344, c_38])).
% 3.20/1.49  tff(c_396, plain, ('#skF_10'='#skF_9' | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9') | '#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_56, c_389])).
% 3.20/1.49  tff(c_400, plain, ('#skF_10'='#skF_9' | '#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_396])).
% 3.20/1.49  tff(c_401, plain, ('#skF_9'='#skF_8'), inference(splitLeft, [status(thm)], [c_400])).
% 3.20/1.49  tff(c_409, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_401, c_58])).
% 3.20/1.49  tff(c_406, plain, (k1_relset_1('#skF_8', '#skF_8', '#skF_10')=k1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_401, c_137])).
% 3.20/1.49  tff(c_408, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_401, c_56])).
% 3.20/1.49  tff(c_44, plain, (![B_59, C_60]: (k1_relset_1(k1_xboole_0, B_59, C_60)=k1_xboole_0 | ~v1_funct_2(C_60, k1_xboole_0, B_59) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_59))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.20/1.49  tff(c_348, plain, (![B_59, C_60]: (k1_relset_1('#skF_9', B_59, C_60)='#skF_9' | ~v1_funct_2(C_60, '#skF_9', B_59) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1('#skF_9', B_59))))), inference(demodulation, [status(thm), theory('equality')], [c_344, c_344, c_344, c_344, c_44])).
% 3.20/1.49  tff(c_490, plain, (![B_135, C_136]: (k1_relset_1('#skF_8', B_135, C_136)='#skF_8' | ~v1_funct_2(C_136, '#skF_8', B_135) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1('#skF_8', B_135))))), inference(demodulation, [status(thm), theory('equality')], [c_401, c_401, c_401, c_401, c_348])).
% 3.20/1.49  tff(c_493, plain, (k1_relset_1('#skF_8', '#skF_8', '#skF_10')='#skF_8' | ~v1_funct_2('#skF_10', '#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_408, c_490])).
% 3.20/1.49  tff(c_500, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_409, c_406, c_493])).
% 3.20/1.49  tff(c_502, plain, $false, inference(negUnitSimplification, [status(thm)], [c_345, c_500])).
% 3.20/1.49  tff(c_503, plain, ('#skF_10'='#skF_9'), inference(splitRight, [status(thm)], [c_400])).
% 3.20/1.49  tff(c_517, plain, (v1_funct_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_503, c_60])).
% 3.20/1.49  tff(c_516, plain, (v1_funct_2('#skF_9', '#skF_8', '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_503, c_58])).
% 3.20/1.49  tff(c_511, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_9')=k2_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_503, c_503, c_111])).
% 3.20/1.49  tff(c_515, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_503, c_56])).
% 3.20/1.49  tff(c_665, plain, (![A_155, B_156, C_157]: (r2_hidden('#skF_6'(A_155, B_156, C_157), B_156) | k2_relset_1(A_155, B_156, C_157)=B_156 | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))) | ~v1_funct_2(C_157, A_155, B_156) | ~v1_funct_1(C_157))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.20/1.49  tff(c_667, plain, (r2_hidden('#skF_6'('#skF_8', '#skF_9', '#skF_9'), '#skF_9') | k2_relset_1('#skF_8', '#skF_9', '#skF_9')='#skF_9' | ~v1_funct_2('#skF_9', '#skF_8', '#skF_9') | ~v1_funct_1('#skF_9')), inference(resolution, [status(thm)], [c_515, c_665])).
% 3.20/1.49  tff(c_673, plain, (r2_hidden('#skF_6'('#skF_8', '#skF_9', '#skF_9'), '#skF_9') | k2_relat_1('#skF_9')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_517, c_516, c_511, c_667])).
% 3.20/1.49  tff(c_675, plain, (k2_relat_1('#skF_9')='#skF_9'), inference(splitLeft, [status(thm)], [c_673])).
% 3.20/1.49  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.49  tff(c_66, plain, (~v1_xboole_0(k2_relset_1('#skF_8', '#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_54, c_2])).
% 3.20/1.49  tff(c_113, plain, (~v1_xboole_0(k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_66])).
% 3.20/1.49  tff(c_510, plain, (~v1_xboole_0(k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_503, c_113])).
% 3.20/1.49  tff(c_679, plain, (~v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_675, c_510])).
% 3.20/1.49  tff(c_682, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_352, c_679])).
% 3.20/1.49  tff(c_683, plain, (r2_hidden('#skF_6'('#skF_8', '#skF_9', '#skF_9'), '#skF_9')), inference(splitRight, [status(thm)], [c_673])).
% 3.20/1.49  tff(c_690, plain, (~v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_683, c_2])).
% 3.20/1.49  tff(c_695, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_352, c_690])).
% 3.20/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.49  
% 3.20/1.49  Inference rules
% 3.20/1.49  ----------------------
% 3.20/1.49  #Ref     : 0
% 3.20/1.49  #Sup     : 130
% 3.20/1.49  #Fact    : 0
% 3.20/1.49  #Define  : 0
% 3.20/1.49  #Split   : 4
% 3.20/1.49  #Chain   : 0
% 3.20/1.49  #Close   : 0
% 3.20/1.49  
% 3.20/1.49  Ordering : KBO
% 3.20/1.49  
% 3.20/1.49  Simplification rules
% 3.20/1.49  ----------------------
% 3.20/1.49  #Subsume      : 12
% 3.20/1.49  #Demod        : 107
% 3.20/1.49  #Tautology    : 45
% 3.20/1.49  #SimpNegUnit  : 4
% 3.20/1.49  #BackRed      : 38
% 3.20/1.49  
% 3.20/1.49  #Partial instantiations: 0
% 3.20/1.49  #Strategies tried      : 1
% 3.20/1.49  
% 3.20/1.49  Timing (in seconds)
% 3.20/1.49  ----------------------
% 3.20/1.49  Preprocessing        : 0.32
% 3.20/1.49  Parsing              : 0.16
% 3.20/1.49  CNF conversion       : 0.03
% 3.20/1.49  Main loop            : 0.39
% 3.20/1.49  Inferencing          : 0.15
% 3.20/1.49  Reduction            : 0.11
% 3.20/1.49  Demodulation         : 0.08
% 3.20/1.49  BG Simplification    : 0.02
% 3.20/1.49  Subsumption          : 0.07
% 3.20/1.49  Abstraction          : 0.02
% 3.20/1.49  MUC search           : 0.00
% 3.20/1.49  Cooper               : 0.00
% 3.20/1.49  Total                : 0.76
% 3.20/1.49  Index Insertion      : 0.00
% 3.20/1.50  Index Deletion       : 0.00
% 3.20/1.50  Index Matching       : 0.00
% 3.20/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
