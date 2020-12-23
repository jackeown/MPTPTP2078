%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:21 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 467 expanded)
%              Number of leaves         :   35 ( 173 expanded)
%              Depth                    :   15
%              Number of atoms          :  173 (1246 expanded)
%              Number of equality atoms :   34 ( 199 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

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

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_53,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_141,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( v1_funct_1(B)
              & v1_funct_2(B,A,A)
              & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( ! [C] :
                  ( m1_subset_1(C,A)
                 => k3_funct_2(A,A,B,C) = C )
             => r2_funct_2(A,A,B,k6_partfun1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t201_funct_2)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_109,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( B = k6_relat_1(A)
      <=> ( k1_relat_1(B) = A
          & ! [C] :
              ( r2_hidden(C,A)
             => k1_funct_1(B,C) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

tff(f_123,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_107,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_16,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_97,plain,(
    ! [B_53,A_54] :
      ( v1_relat_1(B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54))
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_104,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_97])).

tff(c_108,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_104])).

tff(c_52,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_154,plain,(
    ! [C_61,A_62,B_63] :
      ( v4_relat_1(C_61,A_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_168,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_154])).

tff(c_174,plain,(
    ! [B_68,A_69] :
      ( k1_relat_1(B_68) = A_69
      | ~ v1_partfun1(B_68,A_69)
      | ~ v4_relat_1(B_68,A_69)
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_177,plain,
    ( k1_relat_1('#skF_4') = '#skF_3'
    | ~ v1_partfun1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_168,c_174])).

tff(c_180,plain,
    ( k1_relat_1('#skF_4') = '#skF_3'
    | ~ v1_partfun1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_177])).

tff(c_181,plain,(
    ~ v1_partfun1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_180])).

tff(c_50,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_201,plain,(
    ! [C_84,A_85,B_86] :
      ( v1_partfun1(C_84,A_85)
      | ~ v1_funct_2(C_84,A_85,B_86)
      | ~ v1_funct_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86)))
      | v1_xboole_0(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_212,plain,
    ( v1_partfun1('#skF_4','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_201])).

tff(c_217,plain,
    ( v1_partfun1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_212])).

tff(c_219,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_181,c_217])).

tff(c_220,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_40,plain,(
    ! [A_30] : k6_relat_1(A_30) = k6_partfun1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_20,plain,(
    ! [B_13] :
      ( r2_hidden('#skF_2'(k1_relat_1(B_13),B_13),k1_relat_1(B_13))
      | k6_relat_1(k1_relat_1(B_13)) = B_13
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_241,plain,(
    ! [B_99] :
      ( r2_hidden('#skF_2'(k1_relat_1(B_99),B_99),k1_relat_1(B_99))
      | k6_partfun1(k1_relat_1(B_99)) = B_99
      | ~ v1_funct_1(B_99)
      | ~ v1_relat_1(B_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_20])).

tff(c_250,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),k1_relat_1('#skF_4'))
    | k6_partfun1(k1_relat_1('#skF_4')) = '#skF_4'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_241])).

tff(c_257,plain,
    ( r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | k6_partfun1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_52,c_220,c_220,c_250])).

tff(c_260,plain,(
    k6_partfun1('#skF_3') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_257])).

tff(c_44,plain,(
    ~ r2_funct_2('#skF_3','#skF_3','#skF_4',k6_partfun1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_261,plain,(
    ~ r2_funct_2('#skF_3','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_44])).

tff(c_394,plain,(
    ! [A_123,B_124,C_125,D_126] :
      ( r2_funct_2(A_123,B_124,C_125,C_125)
      | ~ m1_subset_1(D_126,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124)))
      | ~ v1_funct_2(D_126,A_123,B_124)
      | ~ v1_funct_1(D_126)
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1(A_123,B_124)))
      | ~ v1_funct_2(C_125,A_123,B_124)
      | ~ v1_funct_1(C_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_402,plain,(
    ! [C_125] :
      ( r2_funct_2('#skF_3','#skF_3',C_125,C_125)
      | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
      | ~ v1_funct_2(C_125,'#skF_3','#skF_3')
      | ~ v1_funct_1(C_125) ) ),
    inference(resolution,[status(thm)],[c_48,c_394])).

tff(c_408,plain,(
    ! [C_127] :
      ( r2_funct_2('#skF_3','#skF_3',C_127,C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
      | ~ v1_funct_2(C_127,'#skF_3','#skF_3')
      | ~ v1_funct_1(C_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_402])).

tff(c_416,plain,
    ( r2_funct_2('#skF_3','#skF_3','#skF_4','#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_408])).

tff(c_423,plain,(
    r2_funct_2('#skF_3','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_416])).

tff(c_425,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_261,c_423])).

tff(c_427,plain,(
    k6_partfun1('#skF_3') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_18,plain,(
    ! [B_13] :
      ( k1_funct_1(B_13,'#skF_2'(k1_relat_1(B_13),B_13)) != '#skF_2'(k1_relat_1(B_13),B_13)
      | k6_relat_1(k1_relat_1(B_13)) = B_13
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_477,plain,(
    ! [B_132] :
      ( k1_funct_1(B_132,'#skF_2'(k1_relat_1(B_132),B_132)) != '#skF_2'(k1_relat_1(B_132),B_132)
      | k6_partfun1(k1_relat_1(B_132)) = B_132
      | ~ v1_funct_1(B_132)
      | ~ v1_relat_1(B_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_18])).

tff(c_480,plain,
    ( k1_funct_1('#skF_4','#skF_2'('#skF_3','#skF_4')) != '#skF_2'(k1_relat_1('#skF_4'),'#skF_4')
    | k6_partfun1(k1_relat_1('#skF_4')) = '#skF_4'
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_477])).

tff(c_482,plain,
    ( k1_funct_1('#skF_4','#skF_2'('#skF_3','#skF_4')) != '#skF_2'('#skF_3','#skF_4')
    | k6_partfun1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_52,c_220,c_220,c_480])).

tff(c_483,plain,(
    k1_funct_1('#skF_4','#skF_2'('#skF_3','#skF_4')) != '#skF_2'('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_427,c_482])).

tff(c_426,plain,(
    r2_hidden('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ r2_hidden(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_430,plain,
    ( m1_subset_1('#skF_2'('#skF_3','#skF_4'),'#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_426,c_6])).

tff(c_436,plain,(
    m1_subset_1('#skF_2'('#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_430])).

tff(c_46,plain,(
    ! [C_39] :
      ( k3_funct_2('#skF_3','#skF_3','#skF_4',C_39) = C_39
      | ~ m1_subset_1(C_39,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_445,plain,(
    k3_funct_2('#skF_3','#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4')) = '#skF_2'('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_436,c_46])).

tff(c_484,plain,(
    ! [A_133,B_134,C_135,D_136] :
      ( k3_funct_2(A_133,B_134,C_135,D_136) = k1_funct_1(C_135,D_136)
      | ~ m1_subset_1(D_136,A_133)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134)))
      | ~ v1_funct_2(C_135,A_133,B_134)
      | ~ v1_funct_1(C_135)
      | v1_xboole_0(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_486,plain,(
    ! [B_134,C_135] :
      ( k3_funct_2('#skF_3',B_134,C_135,'#skF_2'('#skF_3','#skF_4')) = k1_funct_1(C_135,'#skF_2'('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_134)))
      | ~ v1_funct_2(C_135,'#skF_3',B_134)
      | ~ v1_funct_1(C_135)
      | v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_436,c_484])).

tff(c_528,plain,(
    ! [B_141,C_142] :
      ( k3_funct_2('#skF_3',B_141,C_142,'#skF_2'('#skF_3','#skF_4')) = k1_funct_1(C_142,'#skF_2'('#skF_3','#skF_4'))
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_141)))
      | ~ v1_funct_2(C_142,'#skF_3',B_141)
      | ~ v1_funct_1(C_142) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_486])).

tff(c_539,plain,
    ( k3_funct_2('#skF_3','#skF_3','#skF_4','#skF_2'('#skF_3','#skF_4')) = k1_funct_1('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_528])).

tff(c_544,plain,(
    k1_funct_1('#skF_4','#skF_2'('#skF_3','#skF_4')) = '#skF_2'('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_445,c_539])).

tff(c_546,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_483,c_544])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:23:08 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.42  
% 2.77/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.42  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.77/1.42  
% 2.77/1.42  %Foreground sorts:
% 2.77/1.42  
% 2.77/1.42  
% 2.77/1.42  %Background operators:
% 2.77/1.42  
% 2.77/1.42  
% 2.77/1.42  %Foreground operators:
% 2.77/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.77/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.42  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.77/1.42  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.77/1.42  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.77/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.77/1.42  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.77/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.77/1.42  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.77/1.42  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.77/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.77/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.77/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.77/1.42  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.77/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.77/1.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.77/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.77/1.42  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.77/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.77/1.42  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 2.77/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.77/1.42  
% 3.09/1.44  tff(f_53, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.09/1.44  tff(f_141, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((![C]: (m1_subset_1(C, A) => (k3_funct_2(A, A, B, C) = C))) => r2_funct_2(A, A, B, k6_partfun1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t201_funct_2)).
% 3.09/1.44  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.09/1.44  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.09/1.44  tff(f_94, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_partfun1)).
% 3.09/1.44  tff(f_86, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.09/1.44  tff(f_109, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 3.09/1.44  tff(f_66, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((B = k6_relat_1(A)) <=> ((k1_relat_1(B) = A) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_funct_1)).
% 3.09/1.44  tff(f_123, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 3.09/1.44  tff(f_44, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.09/1.44  tff(f_107, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 3.09/1.44  tff(c_16, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.09/1.44  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.09/1.44  tff(c_97, plain, (![B_53, A_54]: (v1_relat_1(B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.09/1.44  tff(c_104, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_48, c_97])).
% 3.09/1.44  tff(c_108, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_104])).
% 3.09/1.44  tff(c_52, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.09/1.44  tff(c_54, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.09/1.44  tff(c_154, plain, (![C_61, A_62, B_63]: (v4_relat_1(C_61, A_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.09/1.44  tff(c_168, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_154])).
% 3.09/1.44  tff(c_174, plain, (![B_68, A_69]: (k1_relat_1(B_68)=A_69 | ~v1_partfun1(B_68, A_69) | ~v4_relat_1(B_68, A_69) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.09/1.44  tff(c_177, plain, (k1_relat_1('#skF_4')='#skF_3' | ~v1_partfun1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_168, c_174])).
% 3.09/1.44  tff(c_180, plain, (k1_relat_1('#skF_4')='#skF_3' | ~v1_partfun1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_177])).
% 3.09/1.44  tff(c_181, plain, (~v1_partfun1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_180])).
% 3.09/1.44  tff(c_50, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.09/1.44  tff(c_201, plain, (![C_84, A_85, B_86]: (v1_partfun1(C_84, A_85) | ~v1_funct_2(C_84, A_85, B_86) | ~v1_funct_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))) | v1_xboole_0(B_86))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.09/1.44  tff(c_212, plain, (v1_partfun1('#skF_4', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_201])).
% 3.09/1.44  tff(c_217, plain, (v1_partfun1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_212])).
% 3.09/1.44  tff(c_219, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_181, c_217])).
% 3.09/1.44  tff(c_220, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_180])).
% 3.09/1.44  tff(c_40, plain, (![A_30]: (k6_relat_1(A_30)=k6_partfun1(A_30))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.09/1.44  tff(c_20, plain, (![B_13]: (r2_hidden('#skF_2'(k1_relat_1(B_13), B_13), k1_relat_1(B_13)) | k6_relat_1(k1_relat_1(B_13))=B_13 | ~v1_funct_1(B_13) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.09/1.44  tff(c_241, plain, (![B_99]: (r2_hidden('#skF_2'(k1_relat_1(B_99), B_99), k1_relat_1(B_99)) | k6_partfun1(k1_relat_1(B_99))=B_99 | ~v1_funct_1(B_99) | ~v1_relat_1(B_99))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_20])).
% 3.09/1.44  tff(c_250, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), k1_relat_1('#skF_4')) | k6_partfun1(k1_relat_1('#skF_4'))='#skF_4' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_220, c_241])).
% 3.09/1.44  tff(c_257, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | k6_partfun1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_52, c_220, c_220, c_250])).
% 3.09/1.44  tff(c_260, plain, (k6_partfun1('#skF_3')='#skF_4'), inference(splitLeft, [status(thm)], [c_257])).
% 3.09/1.44  tff(c_44, plain, (~r2_funct_2('#skF_3', '#skF_3', '#skF_4', k6_partfun1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.09/1.44  tff(c_261, plain, (~r2_funct_2('#skF_3', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_260, c_44])).
% 3.09/1.44  tff(c_394, plain, (![A_123, B_124, C_125, D_126]: (r2_funct_2(A_123, B_124, C_125, C_125) | ~m1_subset_1(D_126, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))) | ~v1_funct_2(D_126, A_123, B_124) | ~v1_funct_1(D_126) | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1(A_123, B_124))) | ~v1_funct_2(C_125, A_123, B_124) | ~v1_funct_1(C_125))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.09/1.44  tff(c_402, plain, (![C_125]: (r2_funct_2('#skF_3', '#skF_3', C_125, C_125) | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_2(C_125, '#skF_3', '#skF_3') | ~v1_funct_1(C_125))), inference(resolution, [status(thm)], [c_48, c_394])).
% 3.09/1.44  tff(c_408, plain, (![C_127]: (r2_funct_2('#skF_3', '#skF_3', C_127, C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_2(C_127, '#skF_3', '#skF_3') | ~v1_funct_1(C_127))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_402])).
% 3.09/1.44  tff(c_416, plain, (r2_funct_2('#skF_3', '#skF_3', '#skF_4', '#skF_4') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_408])).
% 3.09/1.44  tff(c_423, plain, (r2_funct_2('#skF_3', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_416])).
% 3.09/1.44  tff(c_425, plain, $false, inference(negUnitSimplification, [status(thm)], [c_261, c_423])).
% 3.09/1.44  tff(c_427, plain, (k6_partfun1('#skF_3')!='#skF_4'), inference(splitRight, [status(thm)], [c_257])).
% 3.09/1.44  tff(c_18, plain, (![B_13]: (k1_funct_1(B_13, '#skF_2'(k1_relat_1(B_13), B_13))!='#skF_2'(k1_relat_1(B_13), B_13) | k6_relat_1(k1_relat_1(B_13))=B_13 | ~v1_funct_1(B_13) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.09/1.44  tff(c_477, plain, (![B_132]: (k1_funct_1(B_132, '#skF_2'(k1_relat_1(B_132), B_132))!='#skF_2'(k1_relat_1(B_132), B_132) | k6_partfun1(k1_relat_1(B_132))=B_132 | ~v1_funct_1(B_132) | ~v1_relat_1(B_132))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_18])).
% 3.09/1.44  tff(c_480, plain, (k1_funct_1('#skF_4', '#skF_2'('#skF_3', '#skF_4'))!='#skF_2'(k1_relat_1('#skF_4'), '#skF_4') | k6_partfun1(k1_relat_1('#skF_4'))='#skF_4' | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_220, c_477])).
% 3.09/1.44  tff(c_482, plain, (k1_funct_1('#skF_4', '#skF_2'('#skF_3', '#skF_4'))!='#skF_2'('#skF_3', '#skF_4') | k6_partfun1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_108, c_52, c_220, c_220, c_480])).
% 3.09/1.44  tff(c_483, plain, (k1_funct_1('#skF_4', '#skF_2'('#skF_3', '#skF_4'))!='#skF_2'('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_427, c_482])).
% 3.09/1.44  tff(c_426, plain, (r2_hidden('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_257])).
% 3.09/1.44  tff(c_6, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~r2_hidden(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.09/1.44  tff(c_430, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4'), '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_426, c_6])).
% 3.09/1.44  tff(c_436, plain, (m1_subset_1('#skF_2'('#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_54, c_430])).
% 3.09/1.44  tff(c_46, plain, (![C_39]: (k3_funct_2('#skF_3', '#skF_3', '#skF_4', C_39)=C_39 | ~m1_subset_1(C_39, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 3.09/1.44  tff(c_445, plain, (k3_funct_2('#skF_3', '#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4'))='#skF_2'('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_436, c_46])).
% 3.09/1.44  tff(c_484, plain, (![A_133, B_134, C_135, D_136]: (k3_funct_2(A_133, B_134, C_135, D_136)=k1_funct_1(C_135, D_136) | ~m1_subset_1(D_136, A_133) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))) | ~v1_funct_2(C_135, A_133, B_134) | ~v1_funct_1(C_135) | v1_xboole_0(A_133))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.09/1.44  tff(c_486, plain, (![B_134, C_135]: (k3_funct_2('#skF_3', B_134, C_135, '#skF_2'('#skF_3', '#skF_4'))=k1_funct_1(C_135, '#skF_2'('#skF_3', '#skF_4')) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_134))) | ~v1_funct_2(C_135, '#skF_3', B_134) | ~v1_funct_1(C_135) | v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_436, c_484])).
% 3.09/1.44  tff(c_528, plain, (![B_141, C_142]: (k3_funct_2('#skF_3', B_141, C_142, '#skF_2'('#skF_3', '#skF_4'))=k1_funct_1(C_142, '#skF_2'('#skF_3', '#skF_4')) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_141))) | ~v1_funct_2(C_142, '#skF_3', B_141) | ~v1_funct_1(C_142))), inference(negUnitSimplification, [status(thm)], [c_54, c_486])).
% 3.09/1.44  tff(c_539, plain, (k3_funct_2('#skF_3', '#skF_3', '#skF_4', '#skF_2'('#skF_3', '#skF_4'))=k1_funct_1('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_528])).
% 3.09/1.44  tff(c_544, plain, (k1_funct_1('#skF_4', '#skF_2'('#skF_3', '#skF_4'))='#skF_2'('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_445, c_539])).
% 3.09/1.44  tff(c_546, plain, $false, inference(negUnitSimplification, [status(thm)], [c_483, c_544])).
% 3.09/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.44  
% 3.09/1.44  Inference rules
% 3.09/1.44  ----------------------
% 3.09/1.44  #Ref     : 0
% 3.09/1.44  #Sup     : 92
% 3.09/1.44  #Fact    : 0
% 3.09/1.44  #Define  : 0
% 3.09/1.44  #Split   : 4
% 3.09/1.44  #Chain   : 0
% 3.09/1.44  #Close   : 0
% 3.09/1.44  
% 3.09/1.44  Ordering : KBO
% 3.09/1.44  
% 3.09/1.44  Simplification rules
% 3.09/1.44  ----------------------
% 3.09/1.44  #Subsume      : 11
% 3.09/1.44  #Demod        : 98
% 3.09/1.44  #Tautology    : 33
% 3.09/1.44  #SimpNegUnit  : 24
% 3.09/1.44  #BackRed      : 1
% 3.09/1.44  
% 3.09/1.44  #Partial instantiations: 0
% 3.09/1.44  #Strategies tried      : 1
% 3.09/1.44  
% 3.09/1.44  Timing (in seconds)
% 3.09/1.44  ----------------------
% 3.09/1.45  Preprocessing        : 0.35
% 3.09/1.45  Parsing              : 0.18
% 3.09/1.45  CNF conversion       : 0.03
% 3.09/1.45  Main loop            : 0.35
% 3.09/1.45  Inferencing          : 0.13
% 3.09/1.45  Reduction            : 0.11
% 3.09/1.45  Demodulation         : 0.08
% 3.09/1.45  BG Simplification    : 0.02
% 3.09/1.45  Subsumption          : 0.06
% 3.09/1.45  Abstraction          : 0.02
% 3.09/1.45  MUC search           : 0.00
% 3.09/1.45  Cooper               : 0.00
% 3.09/1.45  Total                : 0.74
% 3.09/1.45  Index Insertion      : 0.00
% 3.09/1.45  Index Deletion       : 0.00
% 3.09/1.45  Index Matching       : 0.00
% 3.09/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
