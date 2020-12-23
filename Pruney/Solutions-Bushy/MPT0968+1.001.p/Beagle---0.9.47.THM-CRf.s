%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0968+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:09 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 181 expanded)
%              Number of leaves         :   32 (  73 expanded)
%              Depth                    :   10
%              Number of atoms          :  116 ( 426 expanded)
%              Number of equality atoms :   38 ( 175 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => r2_hidden(C,k1_funct_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_funct_2)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_46,axiom,(
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

tff(f_62,axiom,(
    ! [A,B,C] :
      ( C = k1_funct_2(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E] :
              ( v1_relat_1(E)
              & v1_funct_1(E)
              & D = E
              & k1_relat_1(E) = A
              & r1_tarski(k2_relat_1(E),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_funct_2)).

tff(c_66,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_104,plain,(
    ! [A_50,B_51,C_52] :
      ( k2_relset_1(A_50,B_51,C_52) = k2_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_113,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_104])).

tff(c_138,plain,(
    ! [A_59,B_60,C_61] :
      ( m1_subset_1(k2_relset_1(A_59,B_60,C_61),k1_zfmisc_1(B_60))
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_156,plain,
    ( m1_subset_1(k2_relat_1('#skF_7'),k1_zfmisc_1('#skF_6'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_138])).

tff(c_162,plain,(
    m1_subset_1(k2_relat_1('#skF_7'),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_156])).

tff(c_58,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | ~ m1_subset_1(A_36,k1_zfmisc_1(B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_166,plain,(
    r1_tarski(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_162,c_58])).

tff(c_82,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_91,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_82])).

tff(c_70,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_64,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_71,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_68,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_114,plain,(
    ! [A_53,B_54,C_55] :
      ( k1_relset_1(A_53,B_54,C_55) = k1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_123,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_66,c_114])).

tff(c_346,plain,(
    ! [B_120,A_121,C_122] :
      ( k1_xboole_0 = B_120
      | k1_relset_1(A_121,B_120,C_122) = A_121
      | ~ v1_funct_2(C_122,A_121,B_120)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_121,B_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_357,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_346])).

tff(c_362,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_123,c_357])).

tff(c_363,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_362])).

tff(c_16,plain,(
    ! [E_26,B_8] :
      ( r2_hidden(E_26,k1_funct_2(k1_relat_1(E_26),B_8))
      | ~ r1_tarski(k2_relat_1(E_26),B_8)
      | ~ v1_funct_1(E_26)
      | ~ v1_relat_1(E_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_368,plain,(
    ! [B_8] :
      ( r2_hidden('#skF_7',k1_funct_2('#skF_5',B_8))
      | ~ r1_tarski(k2_relat_1('#skF_7'),B_8)
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_16])).

tff(c_395,plain,(
    ! [B_126] :
      ( r2_hidden('#skF_7',k1_funct_2('#skF_5',B_126))
      | ~ r1_tarski(k2_relat_1('#skF_7'),B_126) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_70,c_368])).

tff(c_62,plain,(
    ~ r2_hidden('#skF_7',k1_funct_2('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_400,plain,(
    ~ r1_tarski(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_395,c_62])).

tff(c_405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_400])).

tff(c_407,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_406,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_412,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_406])).

tff(c_423,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_66])).

tff(c_471,plain,(
    ! [A_142,B_143,C_144] :
      ( k2_relset_1(A_142,B_143,C_144) = k2_relat_1(C_144)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_142,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_480,plain,(
    k2_relset_1('#skF_6','#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_423,c_471])).

tff(c_499,plain,(
    ! [A_157,B_158,C_159] :
      ( m1_subset_1(k2_relset_1(A_157,B_158,C_159),k1_zfmisc_1(B_158))
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_517,plain,
    ( m1_subset_1(k2_relat_1('#skF_7'),k1_zfmisc_1('#skF_6'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_499])).

tff(c_523,plain,(
    m1_subset_1(k2_relat_1('#skF_7'),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_517])).

tff(c_527,plain,(
    r1_tarski(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_523,c_58])).

tff(c_434,plain,(
    ! [C_131,A_132,B_133] :
      ( v1_relat_1(C_131)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_443,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_423,c_434])).

tff(c_418,plain,(
    v1_funct_2('#skF_7','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_68])).

tff(c_457,plain,(
    ! [A_139,B_140,C_141] :
      ( k1_relset_1(A_139,B_140,C_141) = k1_relat_1(C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_466,plain,(
    k1_relset_1('#skF_6','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_423,c_457])).

tff(c_12,plain,(
    ! [B_5,C_6] :
      ( k1_relset_1(k1_xboole_0,B_5,C_6) = k1_xboole_0
      | ~ v1_funct_2(C_6,k1_xboole_0,B_5)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_628,plain,(
    ! [B_188,C_189] :
      ( k1_relset_1('#skF_6',B_188,C_189) = '#skF_6'
      | ~ v1_funct_2(C_189,'#skF_6',B_188)
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1('#skF_6',B_188))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_407,c_407,c_407,c_12])).

tff(c_639,plain,
    ( k1_relset_1('#skF_6','#skF_6','#skF_7') = '#skF_6'
    | ~ v1_funct_2('#skF_7','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_423,c_628])).

tff(c_644,plain,(
    k1_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_466,c_639])).

tff(c_666,plain,(
    ! [B_8] :
      ( r2_hidden('#skF_7',k1_funct_2('#skF_6',B_8))
      | ~ r1_tarski(k2_relat_1('#skF_7'),B_8)
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_644,c_16])).

tff(c_676,plain,(
    ! [B_192] :
      ( r2_hidden('#skF_7',k1_funct_2('#skF_6',B_192))
      | ~ r1_tarski(k2_relat_1('#skF_7'),B_192) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_70,c_666])).

tff(c_417,plain,(
    ~ r2_hidden('#skF_7',k1_funct_2('#skF_6','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_62])).

tff(c_681,plain,(
    ~ r1_tarski(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_676,c_417])).

tff(c_686,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_527,c_681])).

%------------------------------------------------------------------------------
