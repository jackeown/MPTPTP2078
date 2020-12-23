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
% DateTime   : Thu Dec  3 10:11:34 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   99 (1252 expanded)
%              Number of leaves         :   37 ( 450 expanded)
%              Depth                    :   14
%              Number of atoms          :  151 (3929 expanded)
%              Number of equality atoms :   51 (1615 expanded)
%              Maximal formula depth    :   12 (   3 average)
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

tff(f_41,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_116,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ~ ( r2_hidden(C,k2_relset_1(A,B,D))
            & ! [E] :
                ~ ( r2_hidden(E,A)
                  & k1_funct_1(D,E) = C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_funct_2)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_56,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_82,axiom,(
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

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_100,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_10,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_54,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_77,plain,(
    ! [B_75,A_76] :
      ( v1_relat_1(B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_76))
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_80,plain,
    ( v1_relat_1('#skF_10')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_54,c_77])).

tff(c_83,plain,(
    v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_80])).

tff(c_58,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_14,plain,(
    ! [A_10,C_46] :
      ( k1_funct_1(A_10,'#skF_5'(A_10,k2_relat_1(A_10),C_46)) = C_46
      | ~ r2_hidden(C_46,k2_relat_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_56,plain,(
    v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_100,plain,(
    ! [A_81,B_82,C_83] :
      ( k1_relset_1(A_81,B_82,C_83) = k1_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_104,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_54,c_100])).

tff(c_145,plain,(
    ! [B_99,A_100,C_101] :
      ( k1_xboole_0 = B_99
      | k1_relset_1(A_100,B_99,C_101) = A_100
      | ~ v1_funct_2(C_101,A_100,B_99)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_100,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_148,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_10') = '#skF_7'
    | ~ v1_funct_2('#skF_10','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_54,c_145])).

tff(c_151,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_10') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_104,c_148])).

tff(c_152,plain,(
    k1_relat_1('#skF_10') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_16,plain,(
    ! [A_10,C_46] :
      ( r2_hidden('#skF_5'(A_10,k2_relat_1(A_10),C_46),k1_relat_1(A_10))
      | ~ r2_hidden(C_46,k2_relat_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_157,plain,(
    ! [C_46] :
      ( r2_hidden('#skF_5'('#skF_10',k2_relat_1('#skF_10'),C_46),'#skF_7')
      | ~ r2_hidden(C_46,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_16])).

tff(c_206,plain,(
    ! [C_108] :
      ( r2_hidden('#skF_5'('#skF_10',k2_relat_1('#skF_10'),C_108),'#skF_7')
      | ~ r2_hidden(C_108,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_58,c_157])).

tff(c_50,plain,(
    ! [E_68] :
      ( k1_funct_1('#skF_10',E_68) != '#skF_9'
      | ~ r2_hidden(E_68,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_215,plain,(
    ! [C_109] :
      ( k1_funct_1('#skF_10','#skF_5'('#skF_10',k2_relat_1('#skF_10'),C_109)) != '#skF_9'
      | ~ r2_hidden(C_109,k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_206,c_50])).

tff(c_219,plain,(
    ! [C_46] :
      ( C_46 != '#skF_9'
      | ~ r2_hidden(C_46,k2_relat_1('#skF_10'))
      | ~ r2_hidden(C_46,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_215])).

tff(c_222,plain,(
    ~ r2_hidden('#skF_9',k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_58,c_219])).

tff(c_84,plain,(
    ! [A_77,B_78,C_79] :
      ( k2_relset_1(A_77,B_78,C_79) = k2_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_88,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_54,c_84])).

tff(c_52,plain,(
    r2_hidden('#skF_9',k2_relset_1('#skF_7','#skF_8','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_91,plain,(
    r2_hidden('#skF_9',k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_52])).

tff(c_224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_222,c_91])).

tff(c_225,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_232,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_6])).

tff(c_36,plain,(
    ! [C_58,A_56] :
      ( k1_xboole_0 = C_58
      | ~ v1_funct_2(C_58,A_56,k1_xboole_0)
      | k1_xboole_0 = A_56
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_272,plain,(
    ! [C_117,A_118] :
      ( C_117 = '#skF_8'
      | ~ v1_funct_2(C_117,A_118,'#skF_8')
      | A_118 = '#skF_8'
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_118,'#skF_8'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_225,c_225,c_225,c_36])).

tff(c_275,plain,
    ( '#skF_10' = '#skF_8'
    | ~ v1_funct_2('#skF_10','#skF_7','#skF_8')
    | '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_54,c_272])).

tff(c_278,plain,
    ( '#skF_10' = '#skF_8'
    | '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_275])).

tff(c_279,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_278])).

tff(c_226,plain,(
    k1_relat_1('#skF_10') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_280,plain,(
    k1_relat_1('#skF_10') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_226])).

tff(c_286,plain,(
    v1_funct_2('#skF_10','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_56])).

tff(c_281,plain,(
    k1_relset_1('#skF_8','#skF_8','#skF_10') = k1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_104])).

tff(c_285,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_54])).

tff(c_42,plain,(
    ! [B_57,C_58] :
      ( k1_relset_1(k1_xboole_0,B_57,C_58) = k1_xboole_0
      | ~ v1_funct_2(C_58,k1_xboole_0,B_57)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_336,plain,(
    ! [B_122,C_123] :
      ( k1_relset_1('#skF_8',B_122,C_123) = '#skF_8'
      | ~ v1_funct_2(C_123,'#skF_8',B_122)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1('#skF_8',B_122))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_225,c_225,c_225,c_225,c_42])).

tff(c_339,plain,
    ( k1_relset_1('#skF_8','#skF_8','#skF_10') = '#skF_8'
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_285,c_336])).

tff(c_342,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_281,c_339])).

tff(c_344,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_280,c_342])).

tff(c_345,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_278])).

tff(c_358,plain,(
    v1_funct_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_58])).

tff(c_357,plain,(
    v1_funct_2('#skF_8','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_56])).

tff(c_352,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_8') = k2_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_345,c_88])).

tff(c_356,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_54])).

tff(c_583,plain,(
    ! [A_159,B_160,C_161] :
      ( r2_hidden('#skF_6'(A_159,B_160,C_161),B_160)
      | k2_relset_1(A_159,B_160,C_161) = B_160
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160)))
      | ~ v1_funct_2(C_161,A_159,B_160)
      | ~ v1_funct_1(C_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_585,plain,
    ( r2_hidden('#skF_6'('#skF_7','#skF_8','#skF_8'),'#skF_8')
    | k2_relset_1('#skF_7','#skF_8','#skF_8') = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_7','#skF_8')
    | ~ v1_funct_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_356,c_583])).

tff(c_588,plain,
    ( r2_hidden('#skF_6'('#skF_7','#skF_8','#skF_8'),'#skF_8')
    | k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_357,c_352,c_585])).

tff(c_589,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_588])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    ~ v1_xboole_0(k2_relset_1('#skF_7','#skF_8','#skF_10')) ),
    inference(resolution,[status(thm)],[c_52,c_2])).

tff(c_90,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64])).

tff(c_351,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_90])).

tff(c_592,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_589,c_351])).

tff(c_595,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_592])).

tff(c_596,plain,(
    r2_hidden('#skF_6'('#skF_7','#skF_8','#skF_8'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_588])).

tff(c_601,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_596,c_2])).

tff(c_605,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_232,c_601])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:03:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.39  
% 2.81/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.39  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4
% 2.81/1.39  
% 2.81/1.39  %Foreground sorts:
% 2.81/1.39  
% 2.81/1.39  
% 2.81/1.39  %Background operators:
% 2.81/1.39  
% 2.81/1.39  
% 2.81/1.39  %Foreground operators:
% 2.81/1.39  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.81/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.81/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.81/1.39  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.81/1.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.81/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.81/1.39  tff('#skF_7', type, '#skF_7': $i).
% 2.81/1.39  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.81/1.39  tff('#skF_10', type, '#skF_10': $i).
% 2.81/1.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.81/1.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.81/1.39  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.81/1.39  tff('#skF_9', type, '#skF_9': $i).
% 2.81/1.39  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.81/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.81/1.39  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.81/1.39  tff('#skF_8', type, '#skF_8': $i).
% 2.81/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.81/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.81/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.81/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.81/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.81/1.39  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.81/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.81/1.39  
% 2.81/1.41  tff(f_41, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.81/1.41  tff(f_116, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ~(r2_hidden(C, k2_relset_1(A, B, D)) & (![E]: ~(r2_hidden(E, A) & (k1_funct_1(D, E) = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_funct_2)).
% 2.81/1.41  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.81/1.41  tff(f_56, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 2.81/1.41  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.81/1.41  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.81/1.41  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.81/1.41  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.81/1.41  tff(f_100, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 2.81/1.41  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.81/1.41  tff(c_10, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.81/1.41  tff(c_54, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.81/1.41  tff(c_77, plain, (![B_75, A_76]: (v1_relat_1(B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(A_76)) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.81/1.41  tff(c_80, plain, (v1_relat_1('#skF_10') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_54, c_77])).
% 2.81/1.41  tff(c_83, plain, (v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_80])).
% 2.81/1.41  tff(c_58, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.81/1.41  tff(c_14, plain, (![A_10, C_46]: (k1_funct_1(A_10, '#skF_5'(A_10, k2_relat_1(A_10), C_46))=C_46 | ~r2_hidden(C_46, k2_relat_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.81/1.41  tff(c_56, plain, (v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.81/1.41  tff(c_100, plain, (![A_81, B_82, C_83]: (k1_relset_1(A_81, B_82, C_83)=k1_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.81/1.41  tff(c_104, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_54, c_100])).
% 2.81/1.41  tff(c_145, plain, (![B_99, A_100, C_101]: (k1_xboole_0=B_99 | k1_relset_1(A_100, B_99, C_101)=A_100 | ~v1_funct_2(C_101, A_100, B_99) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_100, B_99))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.81/1.41  tff(c_148, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_10')='#skF_7' | ~v1_funct_2('#skF_10', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_54, c_145])).
% 2.81/1.41  tff(c_151, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_10')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_104, c_148])).
% 2.81/1.41  tff(c_152, plain, (k1_relat_1('#skF_10')='#skF_7'), inference(splitLeft, [status(thm)], [c_151])).
% 2.81/1.41  tff(c_16, plain, (![A_10, C_46]: (r2_hidden('#skF_5'(A_10, k2_relat_1(A_10), C_46), k1_relat_1(A_10)) | ~r2_hidden(C_46, k2_relat_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.81/1.41  tff(c_157, plain, (![C_46]: (r2_hidden('#skF_5'('#skF_10', k2_relat_1('#skF_10'), C_46), '#skF_7') | ~r2_hidden(C_46, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_152, c_16])).
% 2.81/1.41  tff(c_206, plain, (![C_108]: (r2_hidden('#skF_5'('#skF_10', k2_relat_1('#skF_10'), C_108), '#skF_7') | ~r2_hidden(C_108, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_58, c_157])).
% 2.81/1.41  tff(c_50, plain, (![E_68]: (k1_funct_1('#skF_10', E_68)!='#skF_9' | ~r2_hidden(E_68, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.81/1.41  tff(c_215, plain, (![C_109]: (k1_funct_1('#skF_10', '#skF_5'('#skF_10', k2_relat_1('#skF_10'), C_109))!='#skF_9' | ~r2_hidden(C_109, k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_206, c_50])).
% 2.81/1.41  tff(c_219, plain, (![C_46]: (C_46!='#skF_9' | ~r2_hidden(C_46, k2_relat_1('#skF_10')) | ~r2_hidden(C_46, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_215])).
% 2.81/1.41  tff(c_222, plain, (~r2_hidden('#skF_9', k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_58, c_219])).
% 2.81/1.41  tff(c_84, plain, (![A_77, B_78, C_79]: (k2_relset_1(A_77, B_78, C_79)=k2_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.81/1.41  tff(c_88, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_54, c_84])).
% 2.81/1.41  tff(c_52, plain, (r2_hidden('#skF_9', k2_relset_1('#skF_7', '#skF_8', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.81/1.41  tff(c_91, plain, (r2_hidden('#skF_9', k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_52])).
% 2.81/1.41  tff(c_224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_222, c_91])).
% 2.81/1.41  tff(c_225, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_151])).
% 2.81/1.41  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.81/1.41  tff(c_232, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_225, c_6])).
% 2.81/1.41  tff(c_36, plain, (![C_58, A_56]: (k1_xboole_0=C_58 | ~v1_funct_2(C_58, A_56, k1_xboole_0) | k1_xboole_0=A_56 | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.81/1.41  tff(c_272, plain, (![C_117, A_118]: (C_117='#skF_8' | ~v1_funct_2(C_117, A_118, '#skF_8') | A_118='#skF_8' | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_118, '#skF_8'))))), inference(demodulation, [status(thm), theory('equality')], [c_225, c_225, c_225, c_225, c_36])).
% 2.81/1.41  tff(c_275, plain, ('#skF_10'='#skF_8' | ~v1_funct_2('#skF_10', '#skF_7', '#skF_8') | '#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_54, c_272])).
% 2.81/1.41  tff(c_278, plain, ('#skF_10'='#skF_8' | '#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_275])).
% 2.81/1.41  tff(c_279, plain, ('#skF_7'='#skF_8'), inference(splitLeft, [status(thm)], [c_278])).
% 2.81/1.41  tff(c_226, plain, (k1_relat_1('#skF_10')!='#skF_7'), inference(splitRight, [status(thm)], [c_151])).
% 2.81/1.41  tff(c_280, plain, (k1_relat_1('#skF_10')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_279, c_226])).
% 2.81/1.41  tff(c_286, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_279, c_56])).
% 2.81/1.41  tff(c_281, plain, (k1_relset_1('#skF_8', '#skF_8', '#skF_10')=k1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_279, c_104])).
% 2.81/1.41  tff(c_285, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_279, c_54])).
% 2.81/1.41  tff(c_42, plain, (![B_57, C_58]: (k1_relset_1(k1_xboole_0, B_57, C_58)=k1_xboole_0 | ~v1_funct_2(C_58, k1_xboole_0, B_57) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_57))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.81/1.41  tff(c_336, plain, (![B_122, C_123]: (k1_relset_1('#skF_8', B_122, C_123)='#skF_8' | ~v1_funct_2(C_123, '#skF_8', B_122) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1('#skF_8', B_122))))), inference(demodulation, [status(thm), theory('equality')], [c_225, c_225, c_225, c_225, c_42])).
% 2.81/1.41  tff(c_339, plain, (k1_relset_1('#skF_8', '#skF_8', '#skF_10')='#skF_8' | ~v1_funct_2('#skF_10', '#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_285, c_336])).
% 2.81/1.41  tff(c_342, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_286, c_281, c_339])).
% 2.81/1.41  tff(c_344, plain, $false, inference(negUnitSimplification, [status(thm)], [c_280, c_342])).
% 2.81/1.41  tff(c_345, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_278])).
% 2.81/1.41  tff(c_358, plain, (v1_funct_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_345, c_58])).
% 2.81/1.41  tff(c_357, plain, (v1_funct_2('#skF_8', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_345, c_56])).
% 2.81/1.41  tff(c_352, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_8')=k2_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_345, c_345, c_88])).
% 2.81/1.41  tff(c_356, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_345, c_54])).
% 2.81/1.41  tff(c_583, plain, (![A_159, B_160, C_161]: (r2_hidden('#skF_6'(A_159, B_160, C_161), B_160) | k2_relset_1(A_159, B_160, C_161)=B_160 | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))) | ~v1_funct_2(C_161, A_159, B_160) | ~v1_funct_1(C_161))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.81/1.41  tff(c_585, plain, (r2_hidden('#skF_6'('#skF_7', '#skF_8', '#skF_8'), '#skF_8') | k2_relset_1('#skF_7', '#skF_8', '#skF_8')='#skF_8' | ~v1_funct_2('#skF_8', '#skF_7', '#skF_8') | ~v1_funct_1('#skF_8')), inference(resolution, [status(thm)], [c_356, c_583])).
% 2.81/1.41  tff(c_588, plain, (r2_hidden('#skF_6'('#skF_7', '#skF_8', '#skF_8'), '#skF_8') | k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_358, c_357, c_352, c_585])).
% 2.81/1.41  tff(c_589, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(splitLeft, [status(thm)], [c_588])).
% 2.81/1.41  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.81/1.41  tff(c_64, plain, (~v1_xboole_0(k2_relset_1('#skF_7', '#skF_8', '#skF_10'))), inference(resolution, [status(thm)], [c_52, c_2])).
% 2.81/1.41  tff(c_90, plain, (~v1_xboole_0(k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64])).
% 2.81/1.41  tff(c_351, plain, (~v1_xboole_0(k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_345, c_90])).
% 2.81/1.41  tff(c_592, plain, (~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_589, c_351])).
% 2.81/1.41  tff(c_595, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_232, c_592])).
% 2.81/1.41  tff(c_596, plain, (r2_hidden('#skF_6'('#skF_7', '#skF_8', '#skF_8'), '#skF_8')), inference(splitRight, [status(thm)], [c_588])).
% 2.81/1.41  tff(c_601, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_596, c_2])).
% 2.81/1.41  tff(c_605, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_232, c_601])).
% 2.81/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.41  
% 2.81/1.41  Inference rules
% 2.81/1.41  ----------------------
% 2.81/1.41  #Ref     : 0
% 2.81/1.41  #Sup     : 105
% 2.81/1.41  #Fact    : 0
% 2.81/1.41  #Define  : 0
% 2.81/1.41  #Split   : 4
% 2.81/1.41  #Chain   : 0
% 2.81/1.41  #Close   : 0
% 2.81/1.41  
% 2.81/1.41  Ordering : KBO
% 2.81/1.41  
% 2.81/1.41  Simplification rules
% 2.81/1.41  ----------------------
% 2.81/1.41  #Subsume      : 20
% 2.81/1.41  #Demod        : 98
% 2.81/1.41  #Tautology    : 47
% 2.81/1.41  #SimpNegUnit  : 5
% 2.81/1.41  #BackRed      : 32
% 2.81/1.41  
% 2.81/1.41  #Partial instantiations: 0
% 2.81/1.41  #Strategies tried      : 1
% 2.81/1.41  
% 2.81/1.41  Timing (in seconds)
% 2.81/1.41  ----------------------
% 2.81/1.41  Preprocessing        : 0.33
% 2.81/1.41  Parsing              : 0.16
% 2.81/1.41  CNF conversion       : 0.03
% 2.81/1.41  Main loop            : 0.32
% 2.81/1.41  Inferencing          : 0.12
% 2.81/1.41  Reduction            : 0.09
% 2.81/1.41  Demodulation         : 0.07
% 2.81/1.41  BG Simplification    : 0.02
% 2.81/1.41  Subsumption          : 0.06
% 2.81/1.41  Abstraction          : 0.02
% 2.81/1.41  MUC search           : 0.00
% 2.81/1.41  Cooper               : 0.00
% 2.81/1.41  Total                : 0.68
% 2.81/1.41  Index Insertion      : 0.00
% 2.81/1.41  Index Deletion       : 0.00
% 2.81/1.41  Index Matching       : 0.00
% 2.81/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
