%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:51 EST 2020

% Result     : Theorem 7.32s
% Output     : CNFRefutation 7.87s
% Verified   : 
% Statistics : Number of formulae       :  421 (6951 expanded)
%              Number of leaves         :   33 (2073 expanded)
%              Depth                    :   19
%              Number of atoms          :  779 (18144 expanded)
%              Number of equality atoms :  282 (6953 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_123,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_96,axiom,(
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

tff(f_106,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_22,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_116,plain,(
    ! [B_37,A_38] :
      ( v1_relat_1(B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38))
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_122,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_116])).

tff(c_126,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_122])).

tff(c_64,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_58,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_56,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_239,plain,(
    ! [A_50,B_51,C_52] :
      ( k2_relset_1(A_50,B_51,C_52) = k2_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_246,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_239])).

tff(c_255,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_246])).

tff(c_30,plain,(
    ! [A_14] :
      ( k1_relat_1(k2_funct_1(A_14)) = k2_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_24,plain,(
    ! [A_13] :
      ( v1_funct_1(k2_funct_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_54,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_143,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_146,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_143])).

tff(c_150,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_64,c_146])).

tff(c_151,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_273,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_284,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_18,c_273])).

tff(c_62,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_359,plain,(
    ! [A_68,B_69,C_70] :
      ( k1_relset_1(A_68,B_69,C_70) = k1_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_374,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_359])).

tff(c_713,plain,(
    ! [B_102,A_103,C_104] :
      ( k1_xboole_0 = B_102
      | k1_relset_1(A_103,B_102,C_104) = A_103
      | ~ v1_funct_2(C_104,A_103,B_102)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_103,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_726,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_713])).

tff(c_740,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_374,c_726])).

tff(c_742,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_740])).

tff(c_28,plain,(
    ! [A_14] :
      ( k2_relat_1(k2_funct_1(A_14)) = k1_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_26,plain,(
    ! [A_13] :
      ( v1_relat_1(k2_funct_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_152,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_215,plain,(
    ! [A_48] :
      ( k1_relat_1(k2_funct_1(A_48)) = k2_relat_1(A_48)
      | ~ v2_funct_1(A_48)
      | ~ v1_funct_1(A_48)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_50,plain,(
    ! [A_24] :
      ( v1_funct_2(A_24,k1_relat_1(A_24),k2_relat_1(A_24))
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1025,plain,(
    ! [A_126] :
      ( v1_funct_2(k2_funct_1(A_126),k2_relat_1(A_126),k2_relat_1(k2_funct_1(A_126)))
      | ~ v1_funct_1(k2_funct_1(A_126))
      | ~ v1_relat_1(k2_funct_1(A_126))
      | ~ v2_funct_1(A_126)
      | ~ v1_funct_1(A_126)
      | ~ v1_relat_1(A_126) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_50])).

tff(c_1028,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_1025])).

tff(c_1036,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_64,c_58,c_152,c_1028])).

tff(c_1037,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1036])).

tff(c_1040,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_1037])).

tff(c_1044,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_64,c_1040])).

tff(c_1046,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1036])).

tff(c_414,plain,(
    ! [A_78] :
      ( m1_subset_1(A_78,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_78),k2_relat_1(A_78))))
      | ~ v1_funct_1(A_78)
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_536,plain,(
    ! [A_86] :
      ( r1_tarski(A_86,k2_zfmisc_1(k1_relat_1(A_86),k2_relat_1(A_86)))
      | ~ v1_funct_1(A_86)
      | ~ v1_relat_1(A_86) ) ),
    inference(resolution,[status(thm)],[c_414,c_16])).

tff(c_1069,plain,(
    ! [A_128] :
      ( r1_tarski(k2_funct_1(A_128),k2_zfmisc_1(k2_relat_1(A_128),k2_relat_1(k2_funct_1(A_128))))
      | ~ v1_funct_1(k2_funct_1(A_128))
      | ~ v1_relat_1(k2_funct_1(A_128))
      | ~ v2_funct_1(A_128)
      | ~ v1_funct_1(A_128)
      | ~ v1_relat_1(A_128) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_536])).

tff(c_1089,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_1069])).

tff(c_1105,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_64,c_58,c_1046,c_152,c_1089])).

tff(c_1125,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2',k1_relat_1('#skF_3')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1105])).

tff(c_1138,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_64,c_58,c_742,c_1125])).

tff(c_1140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_284,c_1138])).

tff(c_1141,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_740])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1195,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1141,c_8])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1194,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1141,c_1141,c_12])).

tff(c_429,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_414])).

tff(c_443,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_64,c_429])).

tff(c_462,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_443,c_16])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_477,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_462,c_2])).

tff(c_626,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_477])).

tff(c_1262,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1194,c_626])).

tff(c_1270,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1195,c_1262])).

tff(c_1271,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_477])).

tff(c_1432,plain,(
    ! [B_139,C_140,A_141] :
      ( k1_xboole_0 = B_139
      | v1_funct_2(C_140,A_141,B_139)
      | k1_relset_1(A_141,B_139,C_140) != A_141
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_141,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1435,plain,(
    ! [C_140] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_2(C_140,k1_relat_1('#skF_3'),'#skF_2')
      | k1_relset_1(k1_relat_1('#skF_3'),'#skF_2',C_140) != k1_relat_1('#skF_3')
      | ~ m1_subset_1(C_140,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1271,c_1432])).

tff(c_1510,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1435])).

tff(c_1535,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1510,c_8])).

tff(c_1534,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1510,c_1510,c_12])).

tff(c_104,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | ~ m1_subset_1(A_31,k1_zfmisc_1(B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_108,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_104])).

tff(c_164,plain,(
    ! [B_43,A_44] :
      ( B_43 = A_44
      | ~ r1_tarski(B_43,A_44)
      | ~ r1_tarski(A_44,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_171,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_108,c_164])).

tff(c_191,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_171])).

tff(c_1581,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1534,c_191])).

tff(c_1586,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1535,c_1581])).

tff(c_1588,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1435])).

tff(c_1703,plain,(
    ! [B_159,A_160,C_161] :
      ( k1_xboole_0 = B_159
      | k1_relset_1(A_160,B_159,C_161) = A_160
      | ~ v1_funct_2(C_161,A_160,B_159)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_160,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1716,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_1703])).

tff(c_1728,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_374,c_1716])).

tff(c_1729,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_1588,c_1728])).

tff(c_1736,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1729,c_1271])).

tff(c_1772,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1736,c_191])).

tff(c_1777,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1772])).

tff(c_1778,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_1779,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_1825,plain,(
    ! [A_165,B_166,C_167] :
      ( k1_relset_1(A_165,B_166,C_167) = k1_relat_1(C_167)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1842,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1779,c_1825])).

tff(c_2302,plain,(
    ! [B_211,C_212,A_213] :
      ( k1_xboole_0 = B_211
      | v1_funct_2(C_212,A_213,B_211)
      | k1_relset_1(A_213,B_211,C_212) != A_213
      | ~ m1_subset_1(C_212,k1_zfmisc_1(k2_zfmisc_1(A_213,B_211))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2308,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_1779,c_2302])).

tff(c_2324,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1842,c_2308])).

tff(c_2325,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_1778,c_2324])).

tff(c_2331,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2325])).

tff(c_2334,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2331])).

tff(c_2337,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_64,c_58,c_255,c_2334])).

tff(c_2338,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2325])).

tff(c_2364,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2338,c_8])).

tff(c_2363,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2338,c_2338,c_12])).

tff(c_1793,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_1779,c_16])).

tff(c_1799,plain,
    ( k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3')
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1793,c_2])).

tff(c_1861,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1799])).

tff(c_2423,plain,(
    ~ r1_tarski('#skF_1',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2363,c_1861])).

tff(c_2428,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2364,c_2423])).

tff(c_2429,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1799])).

tff(c_2432,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2429,c_1779])).

tff(c_2918,plain,(
    ! [B_258,C_259,A_260] :
      ( k1_xboole_0 = B_258
      | v1_funct_2(C_259,A_260,B_258)
      | k1_relset_1(A_260,B_258,C_259) != A_260
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_zfmisc_1(A_260,B_258))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2949,plain,(
    ! [B_261,A_262,A_263] :
      ( k1_xboole_0 = B_261
      | v1_funct_2(A_262,A_263,B_261)
      | k1_relset_1(A_263,B_261,A_262) != A_263
      | ~ r1_tarski(A_262,k2_zfmisc_1(A_263,B_261)) ) ),
    inference(resolution,[status(thm)],[c_18,c_2918])).

tff(c_2958,plain,(
    ! [A_262] :
      ( k1_xboole_0 = '#skF_1'
      | v1_funct_2(A_262,'#skF_2','#skF_1')
      | k1_relset_1('#skF_2','#skF_1',A_262) != '#skF_2'
      | ~ r1_tarski(A_262,k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2429,c_2949])).

tff(c_3003,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2958])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2443,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k2_funct_1('#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2429,c_10])).

tff(c_2476,plain,(
    k2_funct_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2443])).

tff(c_3018,plain,(
    k2_funct_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3003,c_2476])).

tff(c_3029,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3003,c_3003,c_12])).

tff(c_3102,plain,(
    k2_funct_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3029,c_2429])).

tff(c_3104,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3018,c_3102])).

tff(c_3106,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2958])).

tff(c_2927,plain,(
    ! [C_259] :
      ( k1_xboole_0 = '#skF_1'
      | v1_funct_2(C_259,'#skF_2','#skF_1')
      | k1_relset_1('#skF_2','#skF_1',C_259) != '#skF_2'
      | ~ m1_subset_1(C_259,k1_zfmisc_1(k2_funct_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2429,c_2918])).

tff(c_3108,plain,(
    ! [C_270] :
      ( v1_funct_2(C_270,'#skF_2','#skF_1')
      | k1_relset_1('#skF_2','#skF_1',C_270) != '#skF_2'
      | ~ m1_subset_1(C_270,k1_zfmisc_1(k2_funct_1('#skF_3'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3106,c_2927])).

tff(c_3111,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_2432,c_3108])).

tff(c_3117,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1842,c_3111])).

tff(c_3118,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_1778,c_3117])).

tff(c_3122,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_3118])).

tff(c_3125,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_64,c_58,c_255,c_3122])).

tff(c_3126,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2443])).

tff(c_3207,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3126])).

tff(c_3224,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3207,c_8])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3221,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3207,c_3207,c_14])).

tff(c_3308,plain,(
    ~ r1_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3221,c_191])).

tff(c_3313,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3224,c_3308])).

tff(c_3314,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3126])).

tff(c_3338,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3314,c_8])).

tff(c_3337,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3314,c_3314,c_12])).

tff(c_3412,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3337,c_191])).

tff(c_3417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3338,c_3412])).

tff(c_3418,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_3421,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3418,c_60])).

tff(c_7144,plain,(
    ! [A_582,B_583,C_584] :
      ( k2_relset_1(A_582,B_583,C_584) = k2_relat_1(C_584)
      | ~ m1_subset_1(C_584,k1_zfmisc_1(k2_zfmisc_1(A_582,B_583))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_7182,plain,(
    ! [C_588] :
      ( k2_relset_1('#skF_1','#skF_2',C_588) = k2_relat_1(C_588)
      | ~ m1_subset_1(C_588,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3418,c_7144])).

tff(c_7185,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3421,c_7182])).

tff(c_7191,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_7185])).

tff(c_3467,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_3472,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_18,c_3467])).

tff(c_3643,plain,(
    ! [A_300,B_301,C_302] :
      ( k2_relset_1(A_300,B_301,C_302) = k2_relat_1(C_302)
      | ~ m1_subset_1(C_302,k1_zfmisc_1(k2_zfmisc_1(A_300,B_301))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_3760,plain,(
    ! [C_319] :
      ( k2_relset_1('#skF_1','#skF_2',C_319) = k2_relat_1(C_319)
      | ~ m1_subset_1(C_319,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3418,c_3643])).

tff(c_3763,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3421,c_3760])).

tff(c_3769,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3763])).

tff(c_3473,plain,(
    ! [A_279] :
      ( k1_relat_1(k2_funct_1(A_279)) = k2_relat_1(A_279)
      | ~ v2_funct_1(A_279)
      | ~ v1_funct_1(A_279)
      | ~ v1_relat_1(A_279) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_5012,plain,(
    ! [A_394] :
      ( v1_funct_2(k2_funct_1(A_394),k2_relat_1(A_394),k2_relat_1(k2_funct_1(A_394)))
      | ~ v1_funct_1(k2_funct_1(A_394))
      | ~ v1_relat_1(k2_funct_1(A_394))
      | ~ v2_funct_1(A_394)
      | ~ v1_funct_1(A_394)
      | ~ v1_relat_1(A_394) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3473,c_50])).

tff(c_5015,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3769,c_5012])).

tff(c_5023,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_64,c_58,c_152,c_5015])).

tff(c_5024,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_5023])).

tff(c_5027,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_5024])).

tff(c_5031,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_64,c_5027])).

tff(c_5033,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_5023])).

tff(c_3497,plain,(
    ! [A_281,B_282,C_283] :
      ( k1_relset_1(A_281,B_282,C_283) = k1_relat_1(C_283)
      | ~ m1_subset_1(C_283,k1_zfmisc_1(k2_zfmisc_1(A_281,B_282))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_3527,plain,(
    ! [C_287] :
      ( k1_relset_1('#skF_1','#skF_2',C_287) = k1_relat_1(C_287)
      | ~ m1_subset_1(C_287,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3418,c_3497])).

tff(c_3535,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3421,c_3527])).

tff(c_4492,plain,(
    ! [B_363,C_364,A_365] :
      ( k1_xboole_0 = B_363
      | v1_funct_2(C_364,A_365,B_363)
      | k1_relset_1(A_365,B_363,C_364) != A_365
      | ~ m1_subset_1(C_364,k1_zfmisc_1(k2_zfmisc_1(A_365,B_363))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4501,plain,(
    ! [C_364] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_2(C_364,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',C_364) != '#skF_1'
      | ~ m1_subset_1(C_364,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3418,c_4492])).

tff(c_4515,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4501])).

tff(c_3426,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_3418,c_10])).

tff(c_3468,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3426])).

tff(c_4532,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4515,c_3468])).

tff(c_4606,plain,(
    ! [A_368] : k2_zfmisc_1(A_368,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4515,c_4515,c_12])).

tff(c_3946,plain,(
    ! [B_333,A_334,C_335] :
      ( k1_xboole_0 = B_333
      | k1_relset_1(A_334,B_333,C_335) = A_334
      | ~ v1_funct_2(C_335,A_334,B_333)
      | ~ m1_subset_1(C_335,k1_zfmisc_1(k2_zfmisc_1(A_334,B_333))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_3955,plain,(
    ! [C_335] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_335) = '#skF_1'
      | ~ v1_funct_2(C_335,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_335,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3418,c_3946])).

tff(c_4074,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3955])).

tff(c_4100,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4074,c_8])).

tff(c_4099,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4074,c_4074,c_12])).

tff(c_48,plain,(
    ! [A_24] :
      ( m1_subset_1(A_24,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_24),k2_relat_1(A_24))))
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_3774,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3769,c_48])).

tff(c_3781,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_64,c_3774])).

tff(c_3803,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_3781,c_16])).

tff(c_3817,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_3803,c_2])).

tff(c_3935,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3817])).

tff(c_4146,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4099,c_3935])).

tff(c_4151,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4100,c_4146])).

tff(c_4233,plain,(
    ! [C_352] :
      ( k1_relset_1('#skF_1','#skF_2',C_352) = '#skF_1'
      | ~ v1_funct_2(C_352,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_352,k1_zfmisc_1('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_3955])).

tff(c_4236,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_3421,c_4233])).

tff(c_4243,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_3535,c_4236])).

tff(c_4245,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4243,c_3935])).

tff(c_4254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3418,c_4245])).

tff(c_4255,plain,(
    k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3817])).

tff(c_4613,plain,(
    '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_4606,c_4255])).

tff(c_4648,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4532,c_4613])).

tff(c_4650,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4501])).

tff(c_4651,plain,(
    ! [B_369,A_370,C_371] :
      ( k1_xboole_0 = B_369
      | k1_relset_1(A_370,B_369,C_371) = A_370
      | ~ v1_funct_2(C_371,A_370,B_369)
      | ~ m1_subset_1(C_371,k1_zfmisc_1(k2_zfmisc_1(A_370,B_369))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4660,plain,(
    ! [C_371] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_371) = '#skF_1'
      | ~ v1_funct_2(C_371,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_371,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3418,c_4651])).

tff(c_4687,plain,(
    ! [C_374] :
      ( k1_relset_1('#skF_1','#skF_2',C_374) = '#skF_1'
      | ~ v1_funct_2(C_374,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_374,k1_zfmisc_1('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_4650,c_4660])).

tff(c_4690,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_3421,c_4687])).

tff(c_4697,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_3535,c_4690])).

tff(c_3576,plain,(
    ! [A_293] :
      ( m1_subset_1(A_293,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_293),k2_relat_1(A_293))))
      | ~ v1_funct_1(A_293)
      | ~ v1_relat_1(A_293) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_3906,plain,(
    ! [A_330] :
      ( r1_tarski(A_330,k2_zfmisc_1(k1_relat_1(A_330),k2_relat_1(A_330)))
      | ~ v1_funct_1(A_330)
      | ~ v1_relat_1(A_330) ) ),
    inference(resolution,[status(thm)],[c_3576,c_16])).

tff(c_5058,plain,(
    ! [A_396] :
      ( r1_tarski(k2_funct_1(A_396),k2_zfmisc_1(k1_relat_1(k2_funct_1(A_396)),k1_relat_1(A_396)))
      | ~ v1_funct_1(k2_funct_1(A_396))
      | ~ v1_relat_1(k2_funct_1(A_396))
      | ~ v2_funct_1(A_396)
      | ~ v1_funct_1(A_396)
      | ~ v1_relat_1(A_396) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_3906])).

tff(c_5078,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4697,c_5058])).

tff(c_5094,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')),'#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_64,c_58,c_5033,c_152,c_5078])).

tff(c_5152,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_5094])).

tff(c_5165,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_64,c_58,c_3769,c_5152])).

tff(c_5167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3472,c_5165])).

tff(c_5169,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3426])).

tff(c_5174,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5169,c_5169,c_14])).

tff(c_5168,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3426])).

tff(c_5197,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5169,c_5169,c_5168])).

tff(c_5198,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5197])).

tff(c_5196,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_18,c_3467])).

tff(c_5265,plain,(
    ~ r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5174,c_5198,c_5196])).

tff(c_5176,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5169,c_5169,c_12])).

tff(c_5342,plain,(
    ! [A_411,B_412,C_413] :
      ( k2_relset_1(A_411,B_412,C_413) = k2_relat_1(C_413)
      | ~ m1_subset_1(C_413,k1_zfmisc_1(k2_zfmisc_1(A_411,B_412))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_5487,plain,(
    ! [A_437,C_438] :
      ( k2_relset_1(A_437,'#skF_3',C_438) = k2_relat_1(C_438)
      | ~ m1_subset_1(C_438,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5176,c_5342])).

tff(c_5495,plain,(
    ! [A_439] : k2_relset_1(A_439,'#skF_3','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3421,c_5487])).

tff(c_5201,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5198,c_5198,c_56])).

tff(c_5502,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_5495,c_5201])).

tff(c_5283,plain,(
    ! [A_406] :
      ( k1_relat_1(k2_funct_1(A_406)) = k2_relat_1(A_406)
      | ~ v2_funct_1(A_406)
      | ~ v1_funct_1(A_406)
      | ~ v1_relat_1(A_406) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_5774,plain,(
    ! [A_467] :
      ( v1_funct_2(k2_funct_1(A_467),k2_relat_1(A_467),k2_relat_1(k2_funct_1(A_467)))
      | ~ v1_funct_1(k2_funct_1(A_467))
      | ~ v1_relat_1(k2_funct_1(A_467))
      | ~ v2_funct_1(A_467)
      | ~ v1_funct_1(A_467)
      | ~ v1_relat_1(A_467) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5283,c_50])).

tff(c_5777,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5502,c_5774])).

tff(c_5785,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_3',k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_64,c_58,c_152,c_5777])).

tff(c_5786,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_5785])).

tff(c_5789,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_5786])).

tff(c_5793,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_64,c_5789])).

tff(c_5795,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_5785])).

tff(c_5295,plain,(
    ! [A_407] :
      ( m1_subset_1(A_407,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_407),k2_relat_1(A_407))))
      | ~ v1_funct_1(A_407)
      | ~ v1_relat_1(A_407) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_5312,plain,(
    ! [A_408] :
      ( r1_tarski(A_408,k2_zfmisc_1(k1_relat_1(A_408),k2_relat_1(A_408)))
      | ~ v1_funct_1(A_408)
      | ~ v1_relat_1(A_408) ) ),
    inference(resolution,[status(thm)],[c_5295,c_16])).

tff(c_6061,plain,(
    ! [A_488] :
      ( r1_tarski(k2_funct_1(A_488),k2_zfmisc_1(k2_relat_1(A_488),k2_relat_1(k2_funct_1(A_488))))
      | ~ v1_funct_1(k2_funct_1(A_488))
      | ~ v1_relat_1(k2_funct_1(A_488))
      | ~ v2_funct_1(A_488)
      | ~ v1_funct_1(A_488)
      | ~ v1_relat_1(A_488) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_5312])).

tff(c_6081,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3',k2_relat_1(k2_funct_1('#skF_3'))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5502,c_6061])).

tff(c_6097,plain,(
    r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_64,c_58,c_5795,c_152,c_5174,c_6081])).

tff(c_6099,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5265,c_6097])).

tff(c_6100,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5197])).

tff(c_6143,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6100,c_6100,c_5176])).

tff(c_6102,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6100,c_3467])).

tff(c_6219,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6143,c_6102])).

tff(c_6108,plain,(
    v1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6100,c_126])).

tff(c_6112,plain,(
    v1_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6100,c_64])).

tff(c_6111,plain,(
    v2_funct_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6100,c_58])).

tff(c_6105,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6100,c_6100,c_3421])).

tff(c_6177,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6100,c_6100,c_5174])).

tff(c_6269,plain,(
    ! [A_500,B_501,C_502] :
      ( k1_relset_1(A_500,B_501,C_502) = k1_relat_1(C_502)
      | ~ m1_subset_1(C_502,k1_zfmisc_1(k2_zfmisc_1(A_500,B_501))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6301,plain,(
    ! [B_506,C_507] :
      ( k1_relset_1('#skF_1',B_506,C_507) = k1_relat_1(C_507)
      | ~ m1_subset_1(C_507,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6177,c_6269])).

tff(c_6307,plain,(
    ! [B_506] : k1_relset_1('#skF_1',B_506,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6105,c_6301])).

tff(c_6110,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6100,c_62])).

tff(c_6104,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6100,c_5169])).

tff(c_44,plain,(
    ! [B_22,C_23] :
      ( k1_relset_1(k1_xboole_0,B_22,C_23) = k1_xboole_0
      | ~ v1_funct_2(C_23,k1_xboole_0,B_22)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_65,plain,(
    ! [B_22,C_23] :
      ( k1_relset_1(k1_xboole_0,B_22,C_23) = k1_xboole_0
      | ~ v1_funct_2(C_23,k1_xboole_0,B_22)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_44])).

tff(c_6454,plain,(
    ! [B_523,C_524] :
      ( k1_relset_1('#skF_1',B_523,C_524) = '#skF_1'
      | ~ v1_funct_2(C_524,'#skF_1',B_523)
      | ~ m1_subset_1(C_524,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6104,c_6104,c_6104,c_6104,c_65])).

tff(c_6459,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_1'
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_6110,c_6454])).

tff(c_6466,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6105,c_6307,c_6459])).

tff(c_6107,plain,(
    v1_funct_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6100,c_152])).

tff(c_6118,plain,(
    ! [A_489] :
      ( k2_relat_1(k2_funct_1(A_489)) = k1_relat_1(A_489)
      | ~ v2_funct_1(A_489)
      | ~ v1_funct_1(A_489)
      | ~ v1_relat_1(A_489) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6922,plain,(
    ! [A_574] :
      ( v1_funct_2(k2_funct_1(A_574),k1_relat_1(k2_funct_1(A_574)),k1_relat_1(A_574))
      | ~ v1_funct_1(k2_funct_1(A_574))
      | ~ v1_relat_1(k2_funct_1(A_574))
      | ~ v2_funct_1(A_574)
      | ~ v1_funct_1(A_574)
      | ~ v1_relat_1(A_574) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6118,c_50])).

tff(c_6925,plain,
    ( v1_funct_2(k2_funct_1('#skF_1'),k1_relat_1(k2_funct_1('#skF_1')),'#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6466,c_6922])).

tff(c_6933,plain,
    ( v1_funct_2(k2_funct_1('#skF_1'),k1_relat_1(k2_funct_1('#skF_1')),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6108,c_6112,c_6111,c_6107,c_6925])).

tff(c_6934,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_6933])).

tff(c_6937,plain,
    ( ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_6934])).

tff(c_6941,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6108,c_6112,c_6937])).

tff(c_6943,plain,(
    v1_relat_1(k2_funct_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_6933])).

tff(c_6285,plain,(
    ! [A_503,B_504,C_505] :
      ( k2_relset_1(A_503,B_504,C_505) = k2_relat_1(C_505)
      | ~ m1_subset_1(C_505,k1_zfmisc_1(k2_zfmisc_1(A_503,B_504))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6361,plain,(
    ! [B_518,C_519] :
      ( k2_relset_1('#skF_1',B_518,C_519) = k2_relat_1(C_519)
      | ~ m1_subset_1(C_519,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6177,c_6285])).

tff(c_6369,plain,(
    ! [B_520] : k2_relset_1('#skF_1',B_520,'#skF_1') = k2_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6105,c_6361])).

tff(c_6109,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6100,c_56])).

tff(c_6376,plain,(
    k2_relat_1('#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_6369,c_6109])).

tff(c_6224,plain,(
    ! [A_496] :
      ( m1_subset_1(A_496,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_496),k2_relat_1(A_496))))
      | ~ v1_funct_1(A_496)
      | ~ v1_relat_1(A_496) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_7024,plain,(
    ! [A_579] :
      ( m1_subset_1(k2_funct_1(A_579),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_579),k2_relat_1(k2_funct_1(A_579)))))
      | ~ v1_funct_1(k2_funct_1(A_579))
      | ~ v1_relat_1(k2_funct_1(A_579))
      | ~ v2_funct_1(A_579)
      | ~ v1_funct_1(A_579)
      | ~ v1_relat_1(A_579) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_6224])).

tff(c_7045,plain,
    ( m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_1')))))
    | ~ v1_funct_1(k2_funct_1('#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_1'))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6376,c_7024])).

tff(c_7061,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1(k2_funct_1('#skF_1'))))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6108,c_6112,c_6111,c_6943,c_6107,c_7045])).

tff(c_7082,plain,
    ( m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',k1_relat_1('#skF_1'))))
    | ~ v2_funct_1('#skF_1')
    | ~ v1_funct_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_7061])).

tff(c_7095,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6108,c_6112,c_6111,c_6143,c_6466,c_7082])).

tff(c_7097,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6219,c_7095])).

tff(c_7098,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_7099,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_7339,plain,(
    ! [A_599,B_600,C_601] :
      ( k1_relset_1(A_599,B_600,C_601) = k1_relat_1(C_601)
      | ~ m1_subset_1(C_601,k1_zfmisc_1(k2_zfmisc_1(A_599,B_600))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_7364,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_7099,c_7339])).

tff(c_7591,plain,(
    ! [B_630,C_631,A_632] :
      ( k1_xboole_0 = B_630
      | v1_funct_2(C_631,A_632,B_630)
      | k1_relset_1(A_632,B_630,C_631) != A_632
      | ~ m1_subset_1(C_631,k1_zfmisc_1(k2_zfmisc_1(A_632,B_630))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_7600,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_7099,c_7591])).

tff(c_7619,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7364,c_7600])).

tff(c_7620,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_7098,c_7619])).

tff(c_7623,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_7620])).

tff(c_7626,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_7623])).

tff(c_7629,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_64,c_58,c_7191,c_7626])).

tff(c_7630,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_7620])).

tff(c_7654,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7630,c_8])).

tff(c_7653,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7630,c_7630,c_12])).

tff(c_7110,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_7099,c_16])).

tff(c_7116,plain,
    ( k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3')
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_7110,c_2])).

tff(c_7283,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_7116])).

tff(c_7694,plain,(
    ~ r1_tarski('#skF_1',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7653,c_7283])).

tff(c_7699,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7654,c_7694])).

tff(c_7700,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_7116])).

tff(c_7739,plain,(
    ! [A_638,B_639,C_640] :
      ( k1_relset_1(A_638,B_639,C_640) = k1_relat_1(C_640)
      | ~ m1_subset_1(C_640,k1_zfmisc_1(k2_zfmisc_1(A_638,B_639))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_7919,plain,(
    ! [A_660,B_661,A_662] :
      ( k1_relset_1(A_660,B_661,A_662) = k1_relat_1(A_662)
      | ~ r1_tarski(A_662,k2_zfmisc_1(A_660,B_661)) ) ),
    inference(resolution,[status(thm)],[c_18,c_7739])).

tff(c_7945,plain,(
    ! [A_660,B_661] : k1_relset_1(A_660,B_661,k2_zfmisc_1(A_660,B_661)) = k1_relat_1(k2_zfmisc_1(A_660,B_661)) ),
    inference(resolution,[status(thm)],[c_6,c_7919])).

tff(c_8776,plain,(
    ! [B_711,C_712,A_713] :
      ( k1_xboole_0 = B_711
      | v1_funct_2(C_712,A_713,B_711)
      | k1_relset_1(A_713,B_711,C_712) != A_713
      | ~ m1_subset_1(C_712,k1_zfmisc_1(k2_zfmisc_1(A_713,B_711))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_8824,plain,(
    ! [B_717,A_718,A_719] :
      ( k1_xboole_0 = B_717
      | v1_funct_2(A_718,A_719,B_717)
      | k1_relset_1(A_719,B_717,A_718) != A_719
      | ~ r1_tarski(A_718,k2_zfmisc_1(A_719,B_717)) ) ),
    inference(resolution,[status(thm)],[c_18,c_8776])).

tff(c_8843,plain,(
    ! [B_717,A_719] :
      ( k1_xboole_0 = B_717
      | v1_funct_2(k2_zfmisc_1(A_719,B_717),A_719,B_717)
      | k1_relset_1(A_719,B_717,k2_zfmisc_1(A_719,B_717)) != A_719 ) ),
    inference(resolution,[status(thm)],[c_6,c_8824])).

tff(c_8879,plain,(
    ! [B_722,A_723] :
      ( k1_xboole_0 = B_722
      | v1_funct_2(k2_zfmisc_1(A_723,B_722),A_723,B_722)
      | k1_relat_1(k2_zfmisc_1(A_723,B_722)) != A_723 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7945,c_8843])).

tff(c_8892,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) != '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_7700,c_8879])).

tff(c_8914,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7700,c_8892])).

tff(c_8915,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_7098,c_8914])).

tff(c_8921,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_8915])).

tff(c_8924,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_8921])).

tff(c_8927,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_64,c_58,c_7191,c_8924])).

tff(c_8928,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_8915])).

tff(c_7711,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k2_funct_1('#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7700,c_10])).

tff(c_7730,plain,(
    k2_funct_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_7711])).

tff(c_8981,plain,(
    k2_funct_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8928,c_7730])).

tff(c_8991,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8928,c_8928,c_12])).

tff(c_9076,plain,(
    k2_funct_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8991,c_7700])).

tff(c_9078,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8981,c_9076])).

tff(c_9079,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_7711])).

tff(c_9154,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_9079])).

tff(c_7100,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3426])).

tff(c_9163,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9154,c_7100])).

tff(c_9168,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9154,c_9154,c_14])).

tff(c_9282,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9168,c_3418])).

tff(c_9284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9163,c_9282])).

tff(c_9285,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_9079])).

tff(c_9286,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_9079])).

tff(c_9308,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9285,c_9286])).

tff(c_9295,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9285,c_7100])).

tff(c_38,plain,(
    ! [C_23,A_21] :
      ( k1_xboole_0 = C_23
      | ~ v1_funct_2(C_23,A_21,k1_xboole_0)
      | k1_xboole_0 = A_21
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_68,plain,(
    ! [C_23,A_21] :
      ( k1_xboole_0 = C_23
      | ~ v1_funct_2(C_23,A_21,k1_xboole_0)
      | k1_xboole_0 = A_21
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_38])).

tff(c_9362,plain,(
    ! [C_738,A_739] :
      ( C_738 = '#skF_2'
      | ~ v1_funct_2(C_738,A_739,'#skF_2')
      | A_739 = '#skF_2'
      | ~ m1_subset_1(C_738,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9285,c_9285,c_9285,c_9285,c_68])).

tff(c_9366,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_2' = '#skF_1'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_62,c_9362])).

tff(c_9372,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_9308,c_9295,c_9366])).

tff(c_9402,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_9372])).

tff(c_9302,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9285,c_9285,c_12])).

tff(c_7229,plain,(
    ! [A_592] :
      ( m1_subset_1(A_592,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_592),k2_relat_1(A_592))))
      | ~ v1_funct_1(A_592)
      | ~ v1_relat_1(A_592) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_7241,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7191,c_7229])).

tff(c_7254,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_64,c_7241])).

tff(c_7269,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_7254,c_16])).

tff(c_9420,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9302,c_7269])).

tff(c_9423,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9402,c_9420])).

tff(c_9425,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3426])).

tff(c_9433,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9425,c_8])).

tff(c_9430,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9425,c_9425,c_14])).

tff(c_9424,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3426])).

tff(c_9478,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9425,c_9425,c_9424])).

tff(c_9479,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_9478])).

tff(c_9449,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_7099,c_16])).

tff(c_9480,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9479,c_9449])).

tff(c_9486,plain,(
    r1_tarski(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9430,c_9480])).

tff(c_9511,plain,
    ( k2_funct_1('#skF_3') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_9486,c_2])).

tff(c_9517,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9433,c_9511])).

tff(c_9541,plain,(
    ! [A_744] :
      ( k1_relat_1(k2_funct_1(A_744)) = k2_relat_1(A_744)
      | ~ v2_funct_1(A_744)
      | ~ v1_funct_1(A_744)
      | ~ v1_relat_1(A_744) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_9553,plain,
    ( k2_relat_1('#skF_3') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_9517,c_9541])).

tff(c_9557,plain,(
    k2_relat_1('#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_64,c_58,c_9553])).

tff(c_9432,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9425,c_9425,c_12])).

tff(c_9672,plain,(
    ! [A_752,B_753,C_754] :
      ( k2_relset_1(A_752,B_753,C_754) = k2_relat_1(C_754)
      | ~ m1_subset_1(C_754,k1_zfmisc_1(k2_zfmisc_1(A_752,B_753))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_9697,plain,(
    ! [A_755,C_756] :
      ( k2_relset_1(A_755,'#skF_3',C_756) = k2_relat_1(C_756)
      | ~ m1_subset_1(C_756,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9432,c_9672])).

tff(c_9699,plain,(
    ! [A_755] : k2_relset_1(A_755,'#skF_3','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3421,c_9697])).

tff(c_9726,plain,(
    ! [A_760] : k2_relset_1(A_760,'#skF_3','#skF_3') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9557,c_9699])).

tff(c_9484,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9479,c_9479,c_56])).

tff(c_9730,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_9726,c_9484])).

tff(c_9706,plain,(
    ! [A_757,B_758,C_759] :
      ( k1_relset_1(A_757,B_758,C_759) = k1_relat_1(C_759)
      | ~ m1_subset_1(C_759,k1_zfmisc_1(k2_zfmisc_1(A_757,B_758))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_9892,plain,(
    ! [B_776,C_777] :
      ( k1_relset_1('#skF_3',B_776,C_777) = k1_relat_1(C_777)
      | ~ m1_subset_1(C_777,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9430,c_9706])).

tff(c_9894,plain,(
    ! [B_776] : k1_relset_1('#skF_3',B_776,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3421,c_9892])).

tff(c_9899,plain,(
    ! [B_776] : k1_relset_1('#skF_3',B_776,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9730,c_9894])).

tff(c_40,plain,(
    ! [C_23,B_22] :
      ( v1_funct_2(C_23,k1_xboole_0,B_22)
      | k1_relset_1(k1_xboole_0,B_22,C_23) != k1_xboole_0
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_66,plain,(
    ! [C_23,B_22] :
      ( v1_funct_2(C_23,k1_xboole_0,B_22)
      | k1_relset_1(k1_xboole_0,B_22,C_23) != k1_xboole_0
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_40])).

tff(c_9902,plain,(
    ! [C_778,B_779] :
      ( v1_funct_2(C_778,'#skF_3',B_779)
      | k1_relset_1('#skF_3',B_779,C_778) != '#skF_3'
      | ~ m1_subset_1(C_778,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9425,c_9425,c_9425,c_9425,c_66])).

tff(c_9908,plain,(
    ! [B_779] :
      ( v1_funct_2('#skF_3','#skF_3',B_779)
      | k1_relset_1('#skF_3',B_779,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_3421,c_9902])).

tff(c_9926,plain,(
    ! [B_779] : v1_funct_2('#skF_3','#skF_3',B_779) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9899,c_9908])).

tff(c_9482,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9479,c_7098])).

tff(c_9585,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9517,c_9482])).

tff(c_9930,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9926,c_9585])).

tff(c_9931,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_9478])).

tff(c_9932,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_9478])).

tff(c_9956,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9931,c_9932])).

tff(c_36,plain,(
    ! [A_21] :
      ( v1_funct_2(k1_xboole_0,A_21,k1_xboole_0)
      | k1_xboole_0 = A_21
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_21,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_67,plain,(
    ! [A_21] :
      ( v1_funct_2(k1_xboole_0,A_21,k1_xboole_0)
      | k1_xboole_0 = A_21
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_36])).

tff(c_3445,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_3448,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_3445])).

tff(c_3452,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3448])).

tff(c_3453,plain,(
    ! [A_21] :
      ( v1_funct_2(k1_xboole_0,A_21,k1_xboole_0)
      | k1_xboole_0 = A_21 ) ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_9426,plain,(
    ! [A_21] :
      ( v1_funct_2('#skF_3',A_21,'#skF_3')
      | A_21 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9425,c_9425,c_9425,c_3453])).

tff(c_10124,plain,(
    ! [A_789] :
      ( v1_funct_2('#skF_1',A_789,'#skF_1')
      | A_789 = '#skF_1' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9931,c_9931,c_9931,c_9426])).

tff(c_10000,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9931,c_9931,c_9432])).

tff(c_9937,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9931,c_7099])).

tff(c_10050,plain,(
    m1_subset_1(k2_funct_1('#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10000,c_9937])).

tff(c_10060,plain,(
    r1_tarski(k2_funct_1('#skF_1'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_10050,c_16])).

tff(c_176,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_164])).

tff(c_9428,plain,(
    ! [A_3] :
      ( A_3 = '#skF_3'
      | ~ r1_tarski(A_3,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9425,c_9425,c_176])).

tff(c_10019,plain,(
    ! [A_3] :
      ( A_3 = '#skF_1'
      | ~ r1_tarski(A_3,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9931,c_9931,c_9428])).

tff(c_10069,plain,(
    k2_funct_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_10060,c_10019])).

tff(c_9939,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_1'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9931,c_7098])).

tff(c_10078,plain,(
    ~ v1_funct_2('#skF_1','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10069,c_9939])).

tff(c_10129,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_10124,c_10078])).

tff(c_10137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9956,c_10129])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:08:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.32/2.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.49/2.57  
% 7.49/2.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.49/2.58  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 7.49/2.58  
% 7.49/2.58  %Foreground sorts:
% 7.49/2.58  
% 7.49/2.58  
% 7.49/2.58  %Background operators:
% 7.49/2.58  
% 7.49/2.58  
% 7.49/2.58  %Foreground operators:
% 7.49/2.58  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.49/2.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.49/2.58  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.49/2.58  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.49/2.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.49/2.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.49/2.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.49/2.58  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.49/2.58  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.49/2.58  tff('#skF_2', type, '#skF_2': $i).
% 7.49/2.58  tff('#skF_3', type, '#skF_3': $i).
% 7.49/2.58  tff('#skF_1', type, '#skF_1': $i).
% 7.49/2.58  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.49/2.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.49/2.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.49/2.58  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.49/2.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.49/2.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.49/2.58  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.49/2.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.49/2.58  
% 7.87/2.62  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.87/2.62  tff(f_123, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 7.87/2.62  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.87/2.62  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.87/2.62  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.87/2.62  tff(f_70, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 7.87/2.62  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.87/2.62  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 7.87/2.62  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.87/2.62  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.87/2.62  tff(f_106, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 7.87/2.62  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.87/2.62  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.87/2.62  tff(c_22, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.87/2.62  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.87/2.62  tff(c_116, plain, (![B_37, A_38]: (v1_relat_1(B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.87/2.62  tff(c_122, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_116])).
% 7.87/2.62  tff(c_126, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_122])).
% 7.87/2.62  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.87/2.62  tff(c_58, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.87/2.62  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.87/2.62  tff(c_56, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.87/2.62  tff(c_239, plain, (![A_50, B_51, C_52]: (k2_relset_1(A_50, B_51, C_52)=k2_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.87/2.62  tff(c_246, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_239])).
% 7.87/2.62  tff(c_255, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_246])).
% 7.87/2.62  tff(c_30, plain, (![A_14]: (k1_relat_1(k2_funct_1(A_14))=k2_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.87/2.62  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.87/2.62  tff(c_24, plain, (![A_13]: (v1_funct_1(k2_funct_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.87/2.62  tff(c_54, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.87/2.62  tff(c_143, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_54])).
% 7.87/2.62  tff(c_146, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_24, c_143])).
% 7.87/2.62  tff(c_150, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_64, c_146])).
% 7.87/2.62  tff(c_151, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_54])).
% 7.87/2.62  tff(c_273, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_151])).
% 7.87/2.62  tff(c_284, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_18, c_273])).
% 7.87/2.62  tff(c_62, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.87/2.62  tff(c_359, plain, (![A_68, B_69, C_70]: (k1_relset_1(A_68, B_69, C_70)=k1_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.87/2.62  tff(c_374, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_359])).
% 7.87/2.62  tff(c_713, plain, (![B_102, A_103, C_104]: (k1_xboole_0=B_102 | k1_relset_1(A_103, B_102, C_104)=A_103 | ~v1_funct_2(C_104, A_103, B_102) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_103, B_102))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.87/2.62  tff(c_726, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_713])).
% 7.87/2.62  tff(c_740, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_374, c_726])).
% 7.87/2.62  tff(c_742, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_740])).
% 7.87/2.62  tff(c_28, plain, (![A_14]: (k2_relat_1(k2_funct_1(A_14))=k1_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.87/2.62  tff(c_26, plain, (![A_13]: (v1_relat_1(k2_funct_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.87/2.62  tff(c_152, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_54])).
% 7.87/2.62  tff(c_215, plain, (![A_48]: (k1_relat_1(k2_funct_1(A_48))=k2_relat_1(A_48) | ~v2_funct_1(A_48) | ~v1_funct_1(A_48) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.87/2.62  tff(c_50, plain, (![A_24]: (v1_funct_2(A_24, k1_relat_1(A_24), k2_relat_1(A_24)) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.87/2.62  tff(c_1025, plain, (![A_126]: (v1_funct_2(k2_funct_1(A_126), k2_relat_1(A_126), k2_relat_1(k2_funct_1(A_126))) | ~v1_funct_1(k2_funct_1(A_126)) | ~v1_relat_1(k2_funct_1(A_126)) | ~v2_funct_1(A_126) | ~v1_funct_1(A_126) | ~v1_relat_1(A_126))), inference(superposition, [status(thm), theory('equality')], [c_215, c_50])).
% 7.87/2.62  tff(c_1028, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_255, c_1025])).
% 7.87/2.62  tff(c_1036, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_64, c_58, c_152, c_1028])).
% 7.87/2.62  tff(c_1037, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1036])).
% 7.87/2.62  tff(c_1040, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_1037])).
% 7.87/2.62  tff(c_1044, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_64, c_1040])).
% 7.87/2.62  tff(c_1046, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1036])).
% 7.87/2.62  tff(c_414, plain, (![A_78]: (m1_subset_1(A_78, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_78), k2_relat_1(A_78)))) | ~v1_funct_1(A_78) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.87/2.62  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.87/2.62  tff(c_536, plain, (![A_86]: (r1_tarski(A_86, k2_zfmisc_1(k1_relat_1(A_86), k2_relat_1(A_86))) | ~v1_funct_1(A_86) | ~v1_relat_1(A_86))), inference(resolution, [status(thm)], [c_414, c_16])).
% 7.87/2.62  tff(c_1069, plain, (![A_128]: (r1_tarski(k2_funct_1(A_128), k2_zfmisc_1(k2_relat_1(A_128), k2_relat_1(k2_funct_1(A_128)))) | ~v1_funct_1(k2_funct_1(A_128)) | ~v1_relat_1(k2_funct_1(A_128)) | ~v2_funct_1(A_128) | ~v1_funct_1(A_128) | ~v1_relat_1(A_128))), inference(superposition, [status(thm), theory('equality')], [c_30, c_536])).
% 7.87/2.62  tff(c_1089, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3')))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_255, c_1069])).
% 7.87/2.62  tff(c_1105, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_64, c_58, c_1046, c_152, c_1089])).
% 7.87/2.62  tff(c_1125, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', k1_relat_1('#skF_3'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_1105])).
% 7.87/2.62  tff(c_1138, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_64, c_58, c_742, c_1125])).
% 7.87/2.62  tff(c_1140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_284, c_1138])).
% 7.87/2.62  tff(c_1141, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_740])).
% 7.87/2.62  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.87/2.62  tff(c_1195, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1141, c_8])).
% 7.87/2.62  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.87/2.62  tff(c_1194, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1141, c_1141, c_12])).
% 7.87/2.62  tff(c_429, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_255, c_414])).
% 7.87/2.62  tff(c_443, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_64, c_429])).
% 7.87/2.62  tff(c_462, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_443, c_16])).
% 7.87/2.62  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.87/2.62  tff(c_477, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_462, c_2])).
% 7.87/2.62  tff(c_626, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_477])).
% 7.87/2.62  tff(c_1262, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1194, c_626])).
% 7.87/2.62  tff(c_1270, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1195, c_1262])).
% 7.87/2.62  tff(c_1271, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_477])).
% 7.87/2.62  tff(c_1432, plain, (![B_139, C_140, A_141]: (k1_xboole_0=B_139 | v1_funct_2(C_140, A_141, B_139) | k1_relset_1(A_141, B_139, C_140)!=A_141 | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_141, B_139))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.87/2.62  tff(c_1435, plain, (![C_140]: (k1_xboole_0='#skF_2' | v1_funct_2(C_140, k1_relat_1('#skF_3'), '#skF_2') | k1_relset_1(k1_relat_1('#skF_3'), '#skF_2', C_140)!=k1_relat_1('#skF_3') | ~m1_subset_1(C_140, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1271, c_1432])).
% 7.87/2.62  tff(c_1510, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1435])).
% 7.87/2.62  tff(c_1535, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1510, c_8])).
% 7.87/2.62  tff(c_1534, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1510, c_1510, c_12])).
% 7.87/2.62  tff(c_104, plain, (![A_31, B_32]: (r1_tarski(A_31, B_32) | ~m1_subset_1(A_31, k1_zfmisc_1(B_32)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.87/2.62  tff(c_108, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_104])).
% 7.87/2.62  tff(c_164, plain, (![B_43, A_44]: (B_43=A_44 | ~r1_tarski(B_43, A_44) | ~r1_tarski(A_44, B_43))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.87/2.62  tff(c_171, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_108, c_164])).
% 7.87/2.62  tff(c_191, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_171])).
% 7.87/2.62  tff(c_1581, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1534, c_191])).
% 7.87/2.62  tff(c_1586, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1535, c_1581])).
% 7.87/2.62  tff(c_1588, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_1435])).
% 7.87/2.62  tff(c_1703, plain, (![B_159, A_160, C_161]: (k1_xboole_0=B_159 | k1_relset_1(A_160, B_159, C_161)=A_160 | ~v1_funct_2(C_161, A_160, B_159) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_160, B_159))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.87/2.62  tff(c_1716, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_1703])).
% 7.87/2.62  tff(c_1728, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_374, c_1716])).
% 7.87/2.62  tff(c_1729, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_1588, c_1728])).
% 7.87/2.62  tff(c_1736, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1729, c_1271])).
% 7.87/2.62  tff(c_1772, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1736, c_191])).
% 7.87/2.62  tff(c_1777, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1772])).
% 7.87/2.62  tff(c_1778, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_151])).
% 7.87/2.62  tff(c_1779, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_151])).
% 7.87/2.62  tff(c_1825, plain, (![A_165, B_166, C_167]: (k1_relset_1(A_165, B_166, C_167)=k1_relat_1(C_167) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.87/2.62  tff(c_1842, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1779, c_1825])).
% 7.87/2.62  tff(c_2302, plain, (![B_211, C_212, A_213]: (k1_xboole_0=B_211 | v1_funct_2(C_212, A_213, B_211) | k1_relset_1(A_213, B_211, C_212)!=A_213 | ~m1_subset_1(C_212, k1_zfmisc_1(k2_zfmisc_1(A_213, B_211))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.87/2.62  tff(c_2308, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_1779, c_2302])).
% 7.87/2.62  tff(c_2324, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1842, c_2308])).
% 7.87/2.62  tff(c_2325, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_1778, c_2324])).
% 7.87/2.62  tff(c_2331, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_2325])).
% 7.87/2.62  tff(c_2334, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_2331])).
% 7.87/2.62  tff(c_2337, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_64, c_58, c_255, c_2334])).
% 7.87/2.62  tff(c_2338, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_2325])).
% 7.87/2.62  tff(c_2364, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2338, c_8])).
% 7.87/2.62  tff(c_2363, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2338, c_2338, c_12])).
% 7.87/2.62  tff(c_1793, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_1779, c_16])).
% 7.87/2.62  tff(c_1799, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3') | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1793, c_2])).
% 7.87/2.62  tff(c_1861, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1799])).
% 7.87/2.62  tff(c_2423, plain, (~r1_tarski('#skF_1', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2363, c_1861])).
% 7.87/2.62  tff(c_2428, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2364, c_2423])).
% 7.87/2.62  tff(c_2429, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_1799])).
% 7.87/2.62  tff(c_2432, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2429, c_1779])).
% 7.87/2.62  tff(c_2918, plain, (![B_258, C_259, A_260]: (k1_xboole_0=B_258 | v1_funct_2(C_259, A_260, B_258) | k1_relset_1(A_260, B_258, C_259)!=A_260 | ~m1_subset_1(C_259, k1_zfmisc_1(k2_zfmisc_1(A_260, B_258))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.87/2.62  tff(c_2949, plain, (![B_261, A_262, A_263]: (k1_xboole_0=B_261 | v1_funct_2(A_262, A_263, B_261) | k1_relset_1(A_263, B_261, A_262)!=A_263 | ~r1_tarski(A_262, k2_zfmisc_1(A_263, B_261)))), inference(resolution, [status(thm)], [c_18, c_2918])).
% 7.87/2.62  tff(c_2958, plain, (![A_262]: (k1_xboole_0='#skF_1' | v1_funct_2(A_262, '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', A_262)!='#skF_2' | ~r1_tarski(A_262, k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2429, c_2949])).
% 7.87/2.62  tff(c_3003, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_2958])).
% 7.87/2.62  tff(c_10, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.87/2.62  tff(c_2443, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2' | k2_funct_1('#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2429, c_10])).
% 7.87/2.62  tff(c_2476, plain, (k2_funct_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2443])).
% 7.87/2.62  tff(c_3018, plain, (k2_funct_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3003, c_2476])).
% 7.87/2.62  tff(c_3029, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3003, c_3003, c_12])).
% 7.87/2.62  tff(c_3102, plain, (k2_funct_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3029, c_2429])).
% 7.87/2.62  tff(c_3104, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3018, c_3102])).
% 7.87/2.62  tff(c_3106, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_2958])).
% 7.87/2.62  tff(c_2927, plain, (![C_259]: (k1_xboole_0='#skF_1' | v1_funct_2(C_259, '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', C_259)!='#skF_2' | ~m1_subset_1(C_259, k1_zfmisc_1(k2_funct_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_2429, c_2918])).
% 7.87/2.62  tff(c_3108, plain, (![C_270]: (v1_funct_2(C_270, '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', C_270)!='#skF_2' | ~m1_subset_1(C_270, k1_zfmisc_1(k2_funct_1('#skF_3'))))), inference(negUnitSimplification, [status(thm)], [c_3106, c_2927])).
% 7.87/2.62  tff(c_3111, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_2432, c_3108])).
% 7.87/2.62  tff(c_3117, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1842, c_3111])).
% 7.87/2.62  tff(c_3118, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_1778, c_3117])).
% 7.87/2.62  tff(c_3122, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_3118])).
% 7.87/2.62  tff(c_3125, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_64, c_58, c_255, c_3122])).
% 7.87/2.62  tff(c_3126, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_2443])).
% 7.87/2.62  tff(c_3207, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_3126])).
% 7.87/2.62  tff(c_3224, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_3207, c_8])).
% 7.87/2.62  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.87/2.62  tff(c_3221, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3207, c_3207, c_14])).
% 7.87/2.62  tff(c_3308, plain, (~r1_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3221, c_191])).
% 7.87/2.62  tff(c_3313, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3224, c_3308])).
% 7.87/2.62  tff(c_3314, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_3126])).
% 7.87/2.62  tff(c_3338, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_3314, c_8])).
% 7.87/2.62  tff(c_3337, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3314, c_3314, c_12])).
% 7.87/2.62  tff(c_3412, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3337, c_191])).
% 7.87/2.62  tff(c_3417, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3338, c_3412])).
% 7.87/2.62  tff(c_3418, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_171])).
% 7.87/2.62  tff(c_3421, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3418, c_60])).
% 7.87/2.62  tff(c_7144, plain, (![A_582, B_583, C_584]: (k2_relset_1(A_582, B_583, C_584)=k2_relat_1(C_584) | ~m1_subset_1(C_584, k1_zfmisc_1(k2_zfmisc_1(A_582, B_583))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.87/2.62  tff(c_7182, plain, (![C_588]: (k2_relset_1('#skF_1', '#skF_2', C_588)=k2_relat_1(C_588) | ~m1_subset_1(C_588, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3418, c_7144])).
% 7.87/2.62  tff(c_7185, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3421, c_7182])).
% 7.87/2.62  tff(c_7191, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_7185])).
% 7.87/2.62  tff(c_3467, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_151])).
% 7.87/2.62  tff(c_3472, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_18, c_3467])).
% 7.87/2.62  tff(c_3643, plain, (![A_300, B_301, C_302]: (k2_relset_1(A_300, B_301, C_302)=k2_relat_1(C_302) | ~m1_subset_1(C_302, k1_zfmisc_1(k2_zfmisc_1(A_300, B_301))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.87/2.62  tff(c_3760, plain, (![C_319]: (k2_relset_1('#skF_1', '#skF_2', C_319)=k2_relat_1(C_319) | ~m1_subset_1(C_319, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3418, c_3643])).
% 7.87/2.62  tff(c_3763, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3421, c_3760])).
% 7.87/2.62  tff(c_3769, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_3763])).
% 7.87/2.62  tff(c_3473, plain, (![A_279]: (k1_relat_1(k2_funct_1(A_279))=k2_relat_1(A_279) | ~v2_funct_1(A_279) | ~v1_funct_1(A_279) | ~v1_relat_1(A_279))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.87/2.62  tff(c_5012, plain, (![A_394]: (v1_funct_2(k2_funct_1(A_394), k2_relat_1(A_394), k2_relat_1(k2_funct_1(A_394))) | ~v1_funct_1(k2_funct_1(A_394)) | ~v1_relat_1(k2_funct_1(A_394)) | ~v2_funct_1(A_394) | ~v1_funct_1(A_394) | ~v1_relat_1(A_394))), inference(superposition, [status(thm), theory('equality')], [c_3473, c_50])).
% 7.87/2.62  tff(c_5015, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3769, c_5012])).
% 7.87/2.62  tff(c_5023, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_64, c_58, c_152, c_5015])).
% 7.87/2.62  tff(c_5024, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_5023])).
% 7.87/2.62  tff(c_5027, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_5024])).
% 7.87/2.62  tff(c_5031, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_64, c_5027])).
% 7.87/2.62  tff(c_5033, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_5023])).
% 7.87/2.62  tff(c_3497, plain, (![A_281, B_282, C_283]: (k1_relset_1(A_281, B_282, C_283)=k1_relat_1(C_283) | ~m1_subset_1(C_283, k1_zfmisc_1(k2_zfmisc_1(A_281, B_282))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.87/2.62  tff(c_3527, plain, (![C_287]: (k1_relset_1('#skF_1', '#skF_2', C_287)=k1_relat_1(C_287) | ~m1_subset_1(C_287, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3418, c_3497])).
% 7.87/2.62  tff(c_3535, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3421, c_3527])).
% 7.87/2.62  tff(c_4492, plain, (![B_363, C_364, A_365]: (k1_xboole_0=B_363 | v1_funct_2(C_364, A_365, B_363) | k1_relset_1(A_365, B_363, C_364)!=A_365 | ~m1_subset_1(C_364, k1_zfmisc_1(k2_zfmisc_1(A_365, B_363))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.87/2.62  tff(c_4501, plain, (![C_364]: (k1_xboole_0='#skF_2' | v1_funct_2(C_364, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', C_364)!='#skF_1' | ~m1_subset_1(C_364, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3418, c_4492])).
% 7.87/2.62  tff(c_4515, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_4501])).
% 7.87/2.62  tff(c_3426, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_3418, c_10])).
% 7.87/2.62  tff(c_3468, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_3426])).
% 7.87/2.62  tff(c_4532, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4515, c_3468])).
% 7.87/2.62  tff(c_4606, plain, (![A_368]: (k2_zfmisc_1(A_368, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4515, c_4515, c_12])).
% 7.87/2.62  tff(c_3946, plain, (![B_333, A_334, C_335]: (k1_xboole_0=B_333 | k1_relset_1(A_334, B_333, C_335)=A_334 | ~v1_funct_2(C_335, A_334, B_333) | ~m1_subset_1(C_335, k1_zfmisc_1(k2_zfmisc_1(A_334, B_333))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.87/2.62  tff(c_3955, plain, (![C_335]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_335)='#skF_1' | ~v1_funct_2(C_335, '#skF_1', '#skF_2') | ~m1_subset_1(C_335, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3418, c_3946])).
% 7.87/2.62  tff(c_4074, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_3955])).
% 7.87/2.62  tff(c_4100, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_4074, c_8])).
% 7.87/2.62  tff(c_4099, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4074, c_4074, c_12])).
% 7.87/2.62  tff(c_48, plain, (![A_24]: (m1_subset_1(A_24, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_24), k2_relat_1(A_24)))) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.87/2.62  tff(c_3774, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3769, c_48])).
% 7.87/2.62  tff(c_3781, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_64, c_3774])).
% 7.87/2.62  tff(c_3803, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_3781, c_16])).
% 7.87/2.62  tff(c_3817, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_3803, c_2])).
% 7.87/2.62  tff(c_3935, plain, (~r1_tarski(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_3817])).
% 7.87/2.62  tff(c_4146, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4099, c_3935])).
% 7.87/2.62  tff(c_4151, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4100, c_4146])).
% 7.87/2.62  tff(c_4233, plain, (![C_352]: (k1_relset_1('#skF_1', '#skF_2', C_352)='#skF_1' | ~v1_funct_2(C_352, '#skF_1', '#skF_2') | ~m1_subset_1(C_352, k1_zfmisc_1('#skF_3')))), inference(splitRight, [status(thm)], [c_3955])).
% 7.87/2.62  tff(c_4236, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_3421, c_4233])).
% 7.87/2.62  tff(c_4243, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_3535, c_4236])).
% 7.87/2.62  tff(c_4245, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4243, c_3935])).
% 7.87/2.62  tff(c_4254, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_3418, c_4245])).
% 7.87/2.62  tff(c_4255, plain, (k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_3817])).
% 7.87/2.62  tff(c_4613, plain, ('#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_4606, c_4255])).
% 7.87/2.62  tff(c_4648, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4532, c_4613])).
% 7.87/2.62  tff(c_4650, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_4501])).
% 7.87/2.62  tff(c_4651, plain, (![B_369, A_370, C_371]: (k1_xboole_0=B_369 | k1_relset_1(A_370, B_369, C_371)=A_370 | ~v1_funct_2(C_371, A_370, B_369) | ~m1_subset_1(C_371, k1_zfmisc_1(k2_zfmisc_1(A_370, B_369))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.87/2.62  tff(c_4660, plain, (![C_371]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_371)='#skF_1' | ~v1_funct_2(C_371, '#skF_1', '#skF_2') | ~m1_subset_1(C_371, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_3418, c_4651])).
% 7.87/2.62  tff(c_4687, plain, (![C_374]: (k1_relset_1('#skF_1', '#skF_2', C_374)='#skF_1' | ~v1_funct_2(C_374, '#skF_1', '#skF_2') | ~m1_subset_1(C_374, k1_zfmisc_1('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_4650, c_4660])).
% 7.87/2.62  tff(c_4690, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_3421, c_4687])).
% 7.87/2.62  tff(c_4697, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_3535, c_4690])).
% 7.87/2.62  tff(c_3576, plain, (![A_293]: (m1_subset_1(A_293, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_293), k2_relat_1(A_293)))) | ~v1_funct_1(A_293) | ~v1_relat_1(A_293))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.87/2.62  tff(c_3906, plain, (![A_330]: (r1_tarski(A_330, k2_zfmisc_1(k1_relat_1(A_330), k2_relat_1(A_330))) | ~v1_funct_1(A_330) | ~v1_relat_1(A_330))), inference(resolution, [status(thm)], [c_3576, c_16])).
% 7.87/2.62  tff(c_5058, plain, (![A_396]: (r1_tarski(k2_funct_1(A_396), k2_zfmisc_1(k1_relat_1(k2_funct_1(A_396)), k1_relat_1(A_396))) | ~v1_funct_1(k2_funct_1(A_396)) | ~v1_relat_1(k2_funct_1(A_396)) | ~v2_funct_1(A_396) | ~v1_funct_1(A_396) | ~v1_relat_1(A_396))), inference(superposition, [status(thm), theory('equality')], [c_28, c_3906])).
% 7.87/2.62  tff(c_5078, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4697, c_5058])).
% 7.87/2.62  tff(c_5094, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k1_relat_1(k2_funct_1('#skF_3')), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_64, c_58, c_5033, c_152, c_5078])).
% 7.87/2.62  tff(c_5152, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_5094])).
% 7.87/2.62  tff(c_5165, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_64, c_58, c_3769, c_5152])).
% 7.87/2.62  tff(c_5167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3472, c_5165])).
% 7.87/2.62  tff(c_5169, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_3426])).
% 7.87/2.62  tff(c_5174, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5169, c_5169, c_14])).
% 7.87/2.62  tff(c_5168, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_3426])).
% 7.87/2.62  tff(c_5197, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5169, c_5169, c_5168])).
% 7.87/2.62  tff(c_5198, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_5197])).
% 7.87/2.62  tff(c_5196, plain, (~r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_18, c_3467])).
% 7.87/2.62  tff(c_5265, plain, (~r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5174, c_5198, c_5196])).
% 7.87/2.62  tff(c_5176, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5169, c_5169, c_12])).
% 7.87/2.62  tff(c_5342, plain, (![A_411, B_412, C_413]: (k2_relset_1(A_411, B_412, C_413)=k2_relat_1(C_413) | ~m1_subset_1(C_413, k1_zfmisc_1(k2_zfmisc_1(A_411, B_412))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.87/2.62  tff(c_5487, plain, (![A_437, C_438]: (k2_relset_1(A_437, '#skF_3', C_438)=k2_relat_1(C_438) | ~m1_subset_1(C_438, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_5176, c_5342])).
% 7.87/2.62  tff(c_5495, plain, (![A_439]: (k2_relset_1(A_439, '#skF_3', '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_3421, c_5487])).
% 7.87/2.62  tff(c_5201, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5198, c_5198, c_56])).
% 7.87/2.62  tff(c_5502, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_5495, c_5201])).
% 7.87/2.62  tff(c_5283, plain, (![A_406]: (k1_relat_1(k2_funct_1(A_406))=k2_relat_1(A_406) | ~v2_funct_1(A_406) | ~v1_funct_1(A_406) | ~v1_relat_1(A_406))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.87/2.62  tff(c_5774, plain, (![A_467]: (v1_funct_2(k2_funct_1(A_467), k2_relat_1(A_467), k2_relat_1(k2_funct_1(A_467))) | ~v1_funct_1(k2_funct_1(A_467)) | ~v1_relat_1(k2_funct_1(A_467)) | ~v2_funct_1(A_467) | ~v1_funct_1(A_467) | ~v1_relat_1(A_467))), inference(superposition, [status(thm), theory('equality')], [c_5283, c_50])).
% 7.87/2.62  tff(c_5777, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5502, c_5774])).
% 7.87/2.62  tff(c_5785, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_64, c_58, c_152, c_5777])).
% 7.87/2.62  tff(c_5786, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_5785])).
% 7.87/2.62  tff(c_5789, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_5786])).
% 7.87/2.62  tff(c_5793, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_64, c_5789])).
% 7.87/2.62  tff(c_5795, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_5785])).
% 7.87/2.62  tff(c_5295, plain, (![A_407]: (m1_subset_1(A_407, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_407), k2_relat_1(A_407)))) | ~v1_funct_1(A_407) | ~v1_relat_1(A_407))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.87/2.62  tff(c_5312, plain, (![A_408]: (r1_tarski(A_408, k2_zfmisc_1(k1_relat_1(A_408), k2_relat_1(A_408))) | ~v1_funct_1(A_408) | ~v1_relat_1(A_408))), inference(resolution, [status(thm)], [c_5295, c_16])).
% 7.87/2.62  tff(c_6061, plain, (![A_488]: (r1_tarski(k2_funct_1(A_488), k2_zfmisc_1(k2_relat_1(A_488), k2_relat_1(k2_funct_1(A_488)))) | ~v1_funct_1(k2_funct_1(A_488)) | ~v1_relat_1(k2_funct_1(A_488)) | ~v2_funct_1(A_488) | ~v1_funct_1(A_488) | ~v1_relat_1(A_488))), inference(superposition, [status(thm), theory('equality')], [c_30, c_5312])).
% 7.87/2.62  tff(c_6081, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', k2_relat_1(k2_funct_1('#skF_3')))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5502, c_6061])).
% 7.87/2.62  tff(c_6097, plain, (r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_64, c_58, c_5795, c_152, c_5174, c_6081])).
% 7.87/2.62  tff(c_6099, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5265, c_6097])).
% 7.87/2.62  tff(c_6100, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_5197])).
% 7.87/2.62  tff(c_6143, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6100, c_6100, c_5176])).
% 7.87/2.62  tff(c_6102, plain, (~m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_6100, c_3467])).
% 7.87/2.62  tff(c_6219, plain, (~m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6143, c_6102])).
% 7.87/2.62  tff(c_6108, plain, (v1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6100, c_126])).
% 7.87/2.62  tff(c_6112, plain, (v1_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6100, c_64])).
% 7.87/2.62  tff(c_6111, plain, (v2_funct_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6100, c_58])).
% 7.87/2.62  tff(c_6105, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6100, c_6100, c_3421])).
% 7.87/2.62  tff(c_6177, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6100, c_6100, c_5174])).
% 7.87/2.62  tff(c_6269, plain, (![A_500, B_501, C_502]: (k1_relset_1(A_500, B_501, C_502)=k1_relat_1(C_502) | ~m1_subset_1(C_502, k1_zfmisc_1(k2_zfmisc_1(A_500, B_501))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.87/2.62  tff(c_6301, plain, (![B_506, C_507]: (k1_relset_1('#skF_1', B_506, C_507)=k1_relat_1(C_507) | ~m1_subset_1(C_507, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_6177, c_6269])).
% 7.87/2.62  tff(c_6307, plain, (![B_506]: (k1_relset_1('#skF_1', B_506, '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_6105, c_6301])).
% 7.87/2.62  tff(c_6110, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6100, c_62])).
% 7.87/2.62  tff(c_6104, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6100, c_5169])).
% 7.87/2.62  tff(c_44, plain, (![B_22, C_23]: (k1_relset_1(k1_xboole_0, B_22, C_23)=k1_xboole_0 | ~v1_funct_2(C_23, k1_xboole_0, B_22) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_22))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.87/2.62  tff(c_65, plain, (![B_22, C_23]: (k1_relset_1(k1_xboole_0, B_22, C_23)=k1_xboole_0 | ~v1_funct_2(C_23, k1_xboole_0, B_22) | ~m1_subset_1(C_23, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_44])).
% 7.87/2.62  tff(c_6454, plain, (![B_523, C_524]: (k1_relset_1('#skF_1', B_523, C_524)='#skF_1' | ~v1_funct_2(C_524, '#skF_1', B_523) | ~m1_subset_1(C_524, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_6104, c_6104, c_6104, c_6104, c_65])).
% 7.87/2.62  tff(c_6459, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_1' | ~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_6110, c_6454])).
% 7.87/2.62  tff(c_6466, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6105, c_6307, c_6459])).
% 7.87/2.62  tff(c_6107, plain, (v1_funct_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6100, c_152])).
% 7.87/2.62  tff(c_6118, plain, (![A_489]: (k2_relat_1(k2_funct_1(A_489))=k1_relat_1(A_489) | ~v2_funct_1(A_489) | ~v1_funct_1(A_489) | ~v1_relat_1(A_489))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.87/2.62  tff(c_6922, plain, (![A_574]: (v1_funct_2(k2_funct_1(A_574), k1_relat_1(k2_funct_1(A_574)), k1_relat_1(A_574)) | ~v1_funct_1(k2_funct_1(A_574)) | ~v1_relat_1(k2_funct_1(A_574)) | ~v2_funct_1(A_574) | ~v1_funct_1(A_574) | ~v1_relat_1(A_574))), inference(superposition, [status(thm), theory('equality')], [c_6118, c_50])).
% 7.87/2.62  tff(c_6925, plain, (v1_funct_2(k2_funct_1('#skF_1'), k1_relat_1(k2_funct_1('#skF_1')), '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6466, c_6922])).
% 7.87/2.62  tff(c_6933, plain, (v1_funct_2(k2_funct_1('#skF_1'), k1_relat_1(k2_funct_1('#skF_1')), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6108, c_6112, c_6111, c_6107, c_6925])).
% 7.87/2.62  tff(c_6934, plain, (~v1_relat_1(k2_funct_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_6933])).
% 7.87/2.62  tff(c_6937, plain, (~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_26, c_6934])).
% 7.87/2.62  tff(c_6941, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6108, c_6112, c_6937])).
% 7.87/2.62  tff(c_6943, plain, (v1_relat_1(k2_funct_1('#skF_1'))), inference(splitRight, [status(thm)], [c_6933])).
% 7.87/2.62  tff(c_6285, plain, (![A_503, B_504, C_505]: (k2_relset_1(A_503, B_504, C_505)=k2_relat_1(C_505) | ~m1_subset_1(C_505, k1_zfmisc_1(k2_zfmisc_1(A_503, B_504))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.87/2.62  tff(c_6361, plain, (![B_518, C_519]: (k2_relset_1('#skF_1', B_518, C_519)=k2_relat_1(C_519) | ~m1_subset_1(C_519, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_6177, c_6285])).
% 7.87/2.62  tff(c_6369, plain, (![B_520]: (k2_relset_1('#skF_1', B_520, '#skF_1')=k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_6105, c_6361])).
% 7.87/2.62  tff(c_6109, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6100, c_56])).
% 7.87/2.62  tff(c_6376, plain, (k2_relat_1('#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_6369, c_6109])).
% 7.87/2.62  tff(c_6224, plain, (![A_496]: (m1_subset_1(A_496, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_496), k2_relat_1(A_496)))) | ~v1_funct_1(A_496) | ~v1_relat_1(A_496))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.87/2.62  tff(c_7024, plain, (![A_579]: (m1_subset_1(k2_funct_1(A_579), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_579), k2_relat_1(k2_funct_1(A_579))))) | ~v1_funct_1(k2_funct_1(A_579)) | ~v1_relat_1(k2_funct_1(A_579)) | ~v2_funct_1(A_579) | ~v1_funct_1(A_579) | ~v1_relat_1(A_579))), inference(superposition, [status(thm), theory('equality')], [c_30, c_6224])).
% 7.87/2.62  tff(c_7045, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_1'))))) | ~v1_funct_1(k2_funct_1('#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_1')) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6376, c_7024])).
% 7.87/2.62  tff(c_7061, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1(k2_funct_1('#skF_1')))))), inference(demodulation, [status(thm), theory('equality')], [c_6108, c_6112, c_6111, c_6943, c_6107, c_7045])).
% 7.87/2.62  tff(c_7082, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', k1_relat_1('#skF_1')))) | ~v2_funct_1('#skF_1') | ~v1_funct_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_28, c_7061])).
% 7.87/2.62  tff(c_7095, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6108, c_6112, c_6111, c_6143, c_6466, c_7082])).
% 7.87/2.62  tff(c_7097, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6219, c_7095])).
% 7.87/2.62  tff(c_7098, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_151])).
% 7.87/2.62  tff(c_7099, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_151])).
% 7.87/2.62  tff(c_7339, plain, (![A_599, B_600, C_601]: (k1_relset_1(A_599, B_600, C_601)=k1_relat_1(C_601) | ~m1_subset_1(C_601, k1_zfmisc_1(k2_zfmisc_1(A_599, B_600))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.87/2.62  tff(c_7364, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_7099, c_7339])).
% 7.87/2.62  tff(c_7591, plain, (![B_630, C_631, A_632]: (k1_xboole_0=B_630 | v1_funct_2(C_631, A_632, B_630) | k1_relset_1(A_632, B_630, C_631)!=A_632 | ~m1_subset_1(C_631, k1_zfmisc_1(k2_zfmisc_1(A_632, B_630))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.87/2.62  tff(c_7600, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_7099, c_7591])).
% 7.87/2.62  tff(c_7619, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_7364, c_7600])).
% 7.87/2.62  tff(c_7620, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_7098, c_7619])).
% 7.87/2.62  tff(c_7623, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_7620])).
% 7.87/2.62  tff(c_7626, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_7623])).
% 7.87/2.62  tff(c_7629, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_64, c_58, c_7191, c_7626])).
% 7.87/2.62  tff(c_7630, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_7620])).
% 7.87/2.62  tff(c_7654, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_7630, c_8])).
% 7.87/2.62  tff(c_7653, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7630, c_7630, c_12])).
% 7.87/2.62  tff(c_7110, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_7099, c_16])).
% 7.87/2.62  tff(c_7116, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3') | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_7110, c_2])).
% 7.87/2.62  tff(c_7283, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_7116])).
% 7.87/2.62  tff(c_7694, plain, (~r1_tarski('#skF_1', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7653, c_7283])).
% 7.87/2.62  tff(c_7699, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7654, c_7694])).
% 7.87/2.62  tff(c_7700, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_7116])).
% 7.87/2.62  tff(c_7739, plain, (![A_638, B_639, C_640]: (k1_relset_1(A_638, B_639, C_640)=k1_relat_1(C_640) | ~m1_subset_1(C_640, k1_zfmisc_1(k2_zfmisc_1(A_638, B_639))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.87/2.62  tff(c_7919, plain, (![A_660, B_661, A_662]: (k1_relset_1(A_660, B_661, A_662)=k1_relat_1(A_662) | ~r1_tarski(A_662, k2_zfmisc_1(A_660, B_661)))), inference(resolution, [status(thm)], [c_18, c_7739])).
% 7.87/2.62  tff(c_7945, plain, (![A_660, B_661]: (k1_relset_1(A_660, B_661, k2_zfmisc_1(A_660, B_661))=k1_relat_1(k2_zfmisc_1(A_660, B_661)))), inference(resolution, [status(thm)], [c_6, c_7919])).
% 7.87/2.62  tff(c_8776, plain, (![B_711, C_712, A_713]: (k1_xboole_0=B_711 | v1_funct_2(C_712, A_713, B_711) | k1_relset_1(A_713, B_711, C_712)!=A_713 | ~m1_subset_1(C_712, k1_zfmisc_1(k2_zfmisc_1(A_713, B_711))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.87/2.62  tff(c_8824, plain, (![B_717, A_718, A_719]: (k1_xboole_0=B_717 | v1_funct_2(A_718, A_719, B_717) | k1_relset_1(A_719, B_717, A_718)!=A_719 | ~r1_tarski(A_718, k2_zfmisc_1(A_719, B_717)))), inference(resolution, [status(thm)], [c_18, c_8776])).
% 7.87/2.62  tff(c_8843, plain, (![B_717, A_719]: (k1_xboole_0=B_717 | v1_funct_2(k2_zfmisc_1(A_719, B_717), A_719, B_717) | k1_relset_1(A_719, B_717, k2_zfmisc_1(A_719, B_717))!=A_719)), inference(resolution, [status(thm)], [c_6, c_8824])).
% 7.87/2.62  tff(c_8879, plain, (![B_722, A_723]: (k1_xboole_0=B_722 | v1_funct_2(k2_zfmisc_1(A_723, B_722), A_723, B_722) | k1_relat_1(k2_zfmisc_1(A_723, B_722))!=A_723)), inference(demodulation, [status(thm), theory('equality')], [c_7945, c_8843])).
% 7.87/2.62  tff(c_8892, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))!='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_7700, c_8879])).
% 7.87/2.62  tff(c_8914, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_7700, c_8892])).
% 7.87/2.62  tff(c_8915, plain, (k1_xboole_0='#skF_1' | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_7098, c_8914])).
% 7.87/2.62  tff(c_8921, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_8915])).
% 7.87/2.62  tff(c_8924, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_30, c_8921])).
% 7.87/2.62  tff(c_8927, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_126, c_64, c_58, c_7191, c_8924])).
% 7.87/2.62  tff(c_8928, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_8915])).
% 7.87/2.62  tff(c_7711, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2' | k2_funct_1('#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7700, c_10])).
% 7.87/2.62  tff(c_7730, plain, (k2_funct_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_7711])).
% 7.87/2.62  tff(c_8981, plain, (k2_funct_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8928, c_7730])).
% 7.87/2.62  tff(c_8991, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_8928, c_8928, c_12])).
% 7.87/2.62  tff(c_9076, plain, (k2_funct_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8991, c_7700])).
% 7.87/2.62  tff(c_9078, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8981, c_9076])).
% 7.87/2.62  tff(c_9079, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_7711])).
% 7.87/2.62  tff(c_9154, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_9079])).
% 7.87/2.62  tff(c_7100, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_3426])).
% 7.87/2.62  tff(c_9163, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9154, c_7100])).
% 7.87/2.62  tff(c_9168, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9154, c_9154, c_14])).
% 7.87/2.62  tff(c_9282, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9168, c_3418])).
% 7.87/2.62  tff(c_9284, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9163, c_9282])).
% 7.87/2.62  tff(c_9285, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_9079])).
% 7.87/2.62  tff(c_9286, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_9079])).
% 7.87/2.62  tff(c_9308, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9285, c_9286])).
% 7.87/2.62  tff(c_9295, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9285, c_7100])).
% 7.87/2.62  tff(c_38, plain, (![C_23, A_21]: (k1_xboole_0=C_23 | ~v1_funct_2(C_23, A_21, k1_xboole_0) | k1_xboole_0=A_21 | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.87/2.62  tff(c_68, plain, (![C_23, A_21]: (k1_xboole_0=C_23 | ~v1_funct_2(C_23, A_21, k1_xboole_0) | k1_xboole_0=A_21 | ~m1_subset_1(C_23, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_38])).
% 7.87/2.62  tff(c_9362, plain, (![C_738, A_739]: (C_738='#skF_2' | ~v1_funct_2(C_738, A_739, '#skF_2') | A_739='#skF_2' | ~m1_subset_1(C_738, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_9285, c_9285, c_9285, c_9285, c_68])).
% 7.87/2.62  tff(c_9366, plain, ('#skF_2'='#skF_3' | '#skF_2'='#skF_1' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_62, c_9362])).
% 7.87/2.62  tff(c_9372, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_9308, c_9295, c_9366])).
% 7.87/2.62  tff(c_9402, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_18, c_9372])).
% 7.87/2.62  tff(c_9302, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9285, c_9285, c_12])).
% 7.87/2.62  tff(c_7229, plain, (![A_592]: (m1_subset_1(A_592, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_592), k2_relat_1(A_592)))) | ~v1_funct_1(A_592) | ~v1_relat_1(A_592))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.87/2.62  tff(c_7241, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7191, c_7229])).
% 7.87/2.62  tff(c_7254, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_64, c_7241])).
% 7.87/2.62  tff(c_7269, plain, (r1_tarski('#skF_3', k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))), inference(resolution, [status(thm)], [c_7254, c_16])).
% 7.87/2.62  tff(c_9420, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9302, c_7269])).
% 7.87/2.62  tff(c_9423, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9402, c_9420])).
% 7.87/2.62  tff(c_9425, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_3426])).
% 7.87/2.62  tff(c_9433, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_9425, c_8])).
% 7.87/2.62  tff(c_9430, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9425, c_9425, c_14])).
% 7.87/2.62  tff(c_9424, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_3426])).
% 7.87/2.62  tff(c_9478, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9425, c_9425, c_9424])).
% 7.87/2.62  tff(c_9479, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_9478])).
% 7.87/2.62  tff(c_9449, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_7099, c_16])).
% 7.87/2.62  tff(c_9480, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9479, c_9449])).
% 7.87/2.62  tff(c_9486, plain, (r1_tarski(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9430, c_9480])).
% 7.87/2.62  tff(c_9511, plain, (k2_funct_1('#skF_3')='#skF_3' | ~r1_tarski('#skF_3', k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_9486, c_2])).
% 7.87/2.62  tff(c_9517, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9433, c_9511])).
% 7.87/2.62  tff(c_9541, plain, (![A_744]: (k1_relat_1(k2_funct_1(A_744))=k2_relat_1(A_744) | ~v2_funct_1(A_744) | ~v1_funct_1(A_744) | ~v1_relat_1(A_744))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.87/2.62  tff(c_9553, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_9517, c_9541])).
% 7.87/2.62  tff(c_9557, plain, (k2_relat_1('#skF_3')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_126, c_64, c_58, c_9553])).
% 7.87/2.62  tff(c_9432, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9425, c_9425, c_12])).
% 7.87/2.62  tff(c_9672, plain, (![A_752, B_753, C_754]: (k2_relset_1(A_752, B_753, C_754)=k2_relat_1(C_754) | ~m1_subset_1(C_754, k1_zfmisc_1(k2_zfmisc_1(A_752, B_753))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.87/2.62  tff(c_9697, plain, (![A_755, C_756]: (k2_relset_1(A_755, '#skF_3', C_756)=k2_relat_1(C_756) | ~m1_subset_1(C_756, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_9432, c_9672])).
% 7.87/2.62  tff(c_9699, plain, (![A_755]: (k2_relset_1(A_755, '#skF_3', '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_3421, c_9697])).
% 7.87/2.62  tff(c_9726, plain, (![A_760]: (k2_relset_1(A_760, '#skF_3', '#skF_3')=k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_9557, c_9699])).
% 7.87/2.62  tff(c_9484, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_9479, c_9479, c_56])).
% 7.87/2.62  tff(c_9730, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_9726, c_9484])).
% 7.87/2.62  tff(c_9706, plain, (![A_757, B_758, C_759]: (k1_relset_1(A_757, B_758, C_759)=k1_relat_1(C_759) | ~m1_subset_1(C_759, k1_zfmisc_1(k2_zfmisc_1(A_757, B_758))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.87/2.62  tff(c_9892, plain, (![B_776, C_777]: (k1_relset_1('#skF_3', B_776, C_777)=k1_relat_1(C_777) | ~m1_subset_1(C_777, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_9430, c_9706])).
% 7.87/2.62  tff(c_9894, plain, (![B_776]: (k1_relset_1('#skF_3', B_776, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_3421, c_9892])).
% 7.87/2.62  tff(c_9899, plain, (![B_776]: (k1_relset_1('#skF_3', B_776, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9730, c_9894])).
% 7.87/2.62  tff(c_40, plain, (![C_23, B_22]: (v1_funct_2(C_23, k1_xboole_0, B_22) | k1_relset_1(k1_xboole_0, B_22, C_23)!=k1_xboole_0 | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_22))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.87/2.62  tff(c_66, plain, (![C_23, B_22]: (v1_funct_2(C_23, k1_xboole_0, B_22) | k1_relset_1(k1_xboole_0, B_22, C_23)!=k1_xboole_0 | ~m1_subset_1(C_23, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_40])).
% 7.87/2.62  tff(c_9902, plain, (![C_778, B_779]: (v1_funct_2(C_778, '#skF_3', B_779) | k1_relset_1('#skF_3', B_779, C_778)!='#skF_3' | ~m1_subset_1(C_778, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_9425, c_9425, c_9425, c_9425, c_66])).
% 7.87/2.62  tff(c_9908, plain, (![B_779]: (v1_funct_2('#skF_3', '#skF_3', B_779) | k1_relset_1('#skF_3', B_779, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_3421, c_9902])).
% 7.87/2.62  tff(c_9926, plain, (![B_779]: (v1_funct_2('#skF_3', '#skF_3', B_779))), inference(demodulation, [status(thm), theory('equality')], [c_9899, c_9908])).
% 7.87/2.62  tff(c_9482, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9479, c_7098])).
% 7.87/2.62  tff(c_9585, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9517, c_9482])).
% 7.87/2.62  tff(c_9930, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9926, c_9585])).
% 7.87/2.62  tff(c_9931, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_9478])).
% 7.87/2.62  tff(c_9932, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_9478])).
% 7.87/2.62  tff(c_9956, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9931, c_9932])).
% 7.87/2.62  tff(c_36, plain, (![A_21]: (v1_funct_2(k1_xboole_0, A_21, k1_xboole_0) | k1_xboole_0=A_21 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_21, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.87/2.62  tff(c_67, plain, (![A_21]: (v1_funct_2(k1_xboole_0, A_21, k1_xboole_0) | k1_xboole_0=A_21 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_36])).
% 7.87/2.62  tff(c_3445, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_67])).
% 7.87/2.62  tff(c_3448, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_3445])).
% 7.87/2.62  tff(c_3452, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_3448])).
% 7.87/2.62  tff(c_3453, plain, (![A_21]: (v1_funct_2(k1_xboole_0, A_21, k1_xboole_0) | k1_xboole_0=A_21)), inference(splitRight, [status(thm)], [c_67])).
% 7.87/2.62  tff(c_9426, plain, (![A_21]: (v1_funct_2('#skF_3', A_21, '#skF_3') | A_21='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9425, c_9425, c_9425, c_3453])).
% 7.87/2.62  tff(c_10124, plain, (![A_789]: (v1_funct_2('#skF_1', A_789, '#skF_1') | A_789='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9931, c_9931, c_9931, c_9426])).
% 7.87/2.62  tff(c_10000, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9931, c_9931, c_9432])).
% 7.87/2.62  tff(c_9937, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_9931, c_7099])).
% 7.87/2.62  tff(c_10050, plain, (m1_subset_1(k2_funct_1('#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_10000, c_9937])).
% 7.87/2.62  tff(c_10060, plain, (r1_tarski(k2_funct_1('#skF_1'), '#skF_1')), inference(resolution, [status(thm)], [c_10050, c_16])).
% 7.87/2.62  tff(c_176, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_164])).
% 7.87/2.62  tff(c_9428, plain, (![A_3]: (A_3='#skF_3' | ~r1_tarski(A_3, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_9425, c_9425, c_176])).
% 7.87/2.62  tff(c_10019, plain, (![A_3]: (A_3='#skF_1' | ~r1_tarski(A_3, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_9931, c_9931, c_9428])).
% 7.87/2.62  tff(c_10069, plain, (k2_funct_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_10060, c_10019])).
% 7.87/2.62  tff(c_9939, plain, (~v1_funct_2(k2_funct_1('#skF_1'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_9931, c_7098])).
% 7.87/2.62  tff(c_10078, plain, (~v1_funct_2('#skF_1', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_10069, c_9939])).
% 7.87/2.62  tff(c_10129, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_10124, c_10078])).
% 7.87/2.62  tff(c_10137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9956, c_10129])).
% 7.87/2.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.87/2.62  
% 7.87/2.62  Inference rules
% 7.87/2.62  ----------------------
% 7.87/2.62  #Ref     : 0
% 7.87/2.62  #Sup     : 2106
% 7.87/2.62  #Fact    : 0
% 7.87/2.62  #Define  : 0
% 7.87/2.62  #Split   : 48
% 7.87/2.62  #Chain   : 0
% 7.87/2.62  #Close   : 0
% 7.87/2.62  
% 7.87/2.62  Ordering : KBO
% 7.87/2.62  
% 7.87/2.62  Simplification rules
% 7.87/2.62  ----------------------
% 7.87/2.62  #Subsume      : 233
% 7.87/2.62  #Demod        : 2785
% 7.87/2.62  #Tautology    : 1248
% 7.87/2.62  #SimpNegUnit  : 80
% 7.87/2.62  #BackRed      : 524
% 7.87/2.62  
% 7.87/2.62  #Partial instantiations: 0
% 7.87/2.62  #Strategies tried      : 1
% 7.87/2.62  
% 7.87/2.62  Timing (in seconds)
% 7.87/2.62  ----------------------
% 7.87/2.62  Preprocessing        : 0.32
% 7.87/2.62  Parsing              : 0.16
% 7.87/2.62  CNF conversion       : 0.02
% 7.87/2.62  Main loop            : 1.43
% 7.87/2.62  Inferencing          : 0.49
% 7.87/2.62  Reduction            : 0.52
% 7.87/2.62  Demodulation         : 0.37
% 7.87/2.62  BG Simplification    : 0.06
% 7.87/2.62  Subsumption          : 0.25
% 7.87/2.62  Abstraction          : 0.07
% 7.87/2.62  MUC search           : 0.00
% 7.87/2.62  Cooper               : 0.00
% 7.87/2.62  Total                : 1.89
% 7.87/2.62  Index Insertion      : 0.00
% 7.87/2.63  Index Deletion       : 0.00
% 7.87/2.63  Index Matching       : 0.00
% 7.87/2.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
