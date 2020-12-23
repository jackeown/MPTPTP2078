%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:41 EST 2020

% Result     : Theorem 4.21s
% Output     : CNFRefutation 4.51s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 724 expanded)
%              Number of leaves         :   35 ( 249 expanded)
%              Depth                    :   12
%              Number of atoms          :  302 (2026 expanded)
%              Number of equality atoms :  112 ( 589 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_144,negated_conjecture,(
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

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_85,axiom,(
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

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_115,axiom,(
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

tff(f_75,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_127,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_50,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_140,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_152,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_140])).

tff(c_72,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_66,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_64,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_1175,plain,(
    ! [A_158,B_159,C_160] :
      ( k2_relset_1(A_158,B_159,C_160) = k2_relat_1(C_160)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1181,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1175])).

tff(c_1194,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1181])).

tff(c_36,plain,(
    ! [A_15] :
      ( k1_relat_1(k2_funct_1(A_15)) = k2_relat_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_307,plain,(
    ! [A_64,B_65,C_66] :
      ( k2_relset_1(A_64,B_65,C_66) = k2_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_310,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_307])).

tff(c_322,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_310])).

tff(c_24,plain,(
    ! [A_10] :
      ( k2_relat_1(A_10) != k1_xboole_0
      | k1_xboole_0 = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_193,plain,
    ( k2_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_152,c_24])).

tff(c_208,plain,(
    k2_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_193])).

tff(c_325,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_208])).

tff(c_70,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_349,plain,(
    ! [A_73,B_74,C_75] :
      ( k1_relset_1(A_73,B_74,C_75) = k1_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_363,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_349])).

tff(c_501,plain,(
    ! [B_95,A_96,C_97] :
      ( k1_xboole_0 = B_95
      | k1_relset_1(A_96,B_95,C_97) = A_96
      | ~ v1_funct_2(C_97,A_96,B_95)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_96,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_507,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_501])).

tff(c_521,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_363,c_507])).

tff(c_522,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_325,c_521])).

tff(c_34,plain,(
    ! [A_15] :
      ( k2_relat_1(k2_funct_1(A_15)) = k1_relat_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_32,plain,(
    ! [A_14] :
      ( v1_relat_1(k2_funct_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_30,plain,(
    ! [A_14] :
      ( v1_funct_1(k2_funct_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_62,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_154,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_179,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_154])).

tff(c_183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_72,c_179])).

tff(c_185,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_366,plain,(
    ! [B_76,A_77] :
      ( v1_funct_2(B_76,k1_relat_1(B_76),A_77)
      | ~ r1_tarski(k2_relat_1(B_76),A_77)
      | ~ v1_funct_1(B_76)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_857,plain,(
    ! [A_124,A_125] :
      ( v1_funct_2(k2_funct_1(A_124),k2_relat_1(A_124),A_125)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_124)),A_125)
      | ~ v1_funct_1(k2_funct_1(A_124))
      | ~ v1_relat_1(k2_funct_1(A_124))
      | ~ v2_funct_1(A_124)
      | ~ v1_funct_1(A_124)
      | ~ v1_relat_1(A_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_366])).

tff(c_863,plain,(
    ! [A_125] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_125)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_125)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_857])).

tff(c_872,plain,(
    ! [A_125] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_125)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_125)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_72,c_66,c_185,c_863])).

tff(c_875,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_872])).

tff(c_878,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_875])).

tff(c_882,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_72,c_878])).

tff(c_884,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_872])).

tff(c_398,plain,(
    ! [B_81,A_82] :
      ( m1_subset_1(B_81,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_81),A_82)))
      | ~ r1_tarski(k2_relat_1(B_81),A_82)
      | ~ v1_funct_1(B_81)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_894,plain,(
    ! [A_126,A_127] :
      ( m1_subset_1(k2_funct_1(A_126),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_126),A_127)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_126)),A_127)
      | ~ v1_funct_1(k2_funct_1(A_126))
      | ~ v1_relat_1(k2_funct_1(A_126))
      | ~ v2_funct_1(A_126)
      | ~ v1_funct_1(A_126)
      | ~ v1_relat_1(A_126) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_398])).

tff(c_917,plain,(
    ! [A_127] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_127)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_127)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_322,c_894])).

tff(c_950,plain,(
    ! [A_128] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_128)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_128) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_72,c_66,c_884,c_185,c_917])).

tff(c_184,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_210,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_985,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_950,c_210])).

tff(c_990,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_985])).

tff(c_993,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_72,c_66,c_6,c_522,c_990])).

tff(c_994,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_1197,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1194,c_208])).

tff(c_1127,plain,(
    ! [A_149,B_150,C_151] :
      ( k1_relset_1(A_149,B_150,C_151) = k1_relat_1(C_151)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1145,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_1127])).

tff(c_1312,plain,(
    ! [B_177,A_178,C_179] :
      ( k1_xboole_0 = B_177
      | k1_relset_1(A_178,B_177,C_179) = A_178
      | ~ v1_funct_2(C_179,A_178,B_177)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_178,B_177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1321,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_1312])).

tff(c_1337,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1145,c_1321])).

tff(c_1338,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_1197,c_1337])).

tff(c_26,plain,(
    ! [A_10] :
      ( k1_relat_1(A_10) != k1_xboole_0
      | k1_xboole_0 = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_192,plain,
    ( k1_relat_1('#skF_3') != k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_152,c_26])).

tff(c_209,plain,(
    k1_relat_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_192])).

tff(c_1343,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1338,c_209])).

tff(c_995,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_1144,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_995,c_1127])).

tff(c_1426,plain,(
    ! [B_185,C_186,A_187] :
      ( k1_xboole_0 = B_185
      | v1_funct_2(C_186,A_187,B_185)
      | k1_relset_1(A_187,B_185,C_186) != A_187
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_187,B_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1435,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_995,c_1426])).

tff(c_1452,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1144,c_1435])).

tff(c_1453,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_994,c_1343,c_1452])).

tff(c_1463,plain,
    ( k2_relat_1('#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1453])).

tff(c_1466,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_72,c_66,c_1194,c_1463])).

tff(c_1467,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_1469,plain,(
    k2_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1467,c_208])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1478,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1467,c_1467,c_20])).

tff(c_1494,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1469,c_1478])).

tff(c_1495,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_193])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1507,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1495,c_8])).

tff(c_1496,plain,(
    k2_relat_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_193])).

tff(c_1520,plain,(
    k2_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1495,c_1496])).

tff(c_22,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1506,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1495,c_1495,c_22])).

tff(c_2293,plain,(
    ! [B_298,A_299] :
      ( v1_funct_2(B_298,k1_relat_1(B_298),A_299)
      | ~ r1_tarski(k2_relat_1(B_298),A_299)
      | ~ v1_funct_1(B_298)
      | ~ v1_relat_1(B_298) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2299,plain,(
    ! [A_299] :
      ( v1_funct_2('#skF_3','#skF_3',A_299)
      | ~ r1_tarski(k2_relat_1('#skF_3'),A_299)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1506,c_2293])).

tff(c_2301,plain,(
    ! [A_299] : v1_funct_2('#skF_3','#skF_3',A_299) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_72,c_1507,c_1520,c_2299])).

tff(c_16,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1502,plain,(
    ! [A_6] : m1_subset_1('#skF_3',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1495,c_16])).

tff(c_2212,plain,(
    ! [A_279,B_280,C_281] :
      ( k2_relset_1(A_279,B_280,C_281) = k2_relat_1(C_281)
      | ~ m1_subset_1(C_281,k1_zfmisc_1(k2_zfmisc_1(A_279,B_280))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2222,plain,(
    ! [A_279,B_280] : k2_relset_1(A_279,B_280,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1502,c_2212])).

tff(c_2224,plain,(
    ! [A_279,B_280] : k2_relset_1(A_279,B_280,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1520,c_2222])).

tff(c_2225,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2224,c_64])).

tff(c_2111,plain,(
    ! [A_273] :
      ( k1_relat_1(k2_funct_1(A_273)) = k2_relat_1(A_273)
      | ~ v2_funct_1(A_273)
      | ~ v1_funct_1(A_273)
      | ~ v1_relat_1(A_273) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_120,plain,(
    ! [A_39] :
      ( v1_relat_1(k2_funct_1(A_39))
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_128,plain,(
    ! [A_39] :
      ( k2_relat_1(k2_funct_1(A_39)) != k1_xboole_0
      | k2_funct_1(A_39) = k1_xboole_0
      | ~ v1_funct_1(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(resolution,[status(thm)],[c_120,c_24])).

tff(c_1659,plain,(
    ! [A_211] :
      ( k2_relat_1(k2_funct_1(A_211)) != '#skF_3'
      | k2_funct_1(A_211) = '#skF_3'
      | ~ v1_funct_1(A_211)
      | ~ v1_relat_1(A_211) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1495,c_1495,c_128])).

tff(c_1968,plain,(
    ! [A_254] :
      ( k1_relat_1(A_254) != '#skF_3'
      | k2_funct_1(A_254) = '#skF_3'
      | ~ v1_funct_1(A_254)
      | ~ v1_relat_1(A_254)
      | ~ v2_funct_1(A_254)
      | ~ v1_funct_1(A_254)
      | ~ v1_relat_1(A_254) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1659])).

tff(c_1971,plain,
    ( k1_relat_1('#skF_3') != '#skF_3'
    | k2_funct_1('#skF_3') = '#skF_3'
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1968])).

tff(c_1974,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_72,c_1506,c_1971])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1503,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1495,c_1495,c_14])).

tff(c_1708,plain,(
    ! [A_224,B_225,C_226] :
      ( k2_relset_1(A_224,B_225,C_226) = k2_relat_1(C_226)
      | ~ m1_subset_1(C_226,k1_zfmisc_1(k2_zfmisc_1(A_224,B_225))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1718,plain,(
    ! [A_224,B_225] : k2_relset_1(A_224,B_225,'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1502,c_1708])).

tff(c_1720,plain,(
    ! [A_224,B_225] : k2_relset_1(A_224,B_225,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1520,c_1718])).

tff(c_1721,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1720,c_64])).

tff(c_1533,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_1729,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1721,c_1533])).

tff(c_1731,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1503,c_1729])).

tff(c_1975,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1974,c_1731])).

tff(c_1979,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1502,c_1975])).

tff(c_1981,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_38,plain,(
    ! [C_18,A_16,B_17] :
      ( v1_relat_1(C_18)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2020,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1981,c_38])).

tff(c_2081,plain,(
    ! [A_269] :
      ( k1_relat_1(A_269) != '#skF_3'
      | A_269 = '#skF_3'
      | ~ v1_relat_1(A_269) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1495,c_1495,c_26])).

tff(c_2091,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) != '#skF_3'
    | k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2020,c_2081])).

tff(c_2099,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2091])).

tff(c_2117,plain,
    ( k2_relat_1('#skF_3') != '#skF_3'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2111,c_2099])).

tff(c_2124,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_72,c_66,c_1520,c_2117])).

tff(c_2125,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2091])).

tff(c_2065,plain,(
    ! [A_268] :
      ( k2_relat_1(A_268) != '#skF_3'
      | A_268 = '#skF_3'
      | ~ v1_relat_1(A_268) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1495,c_1495,c_24])).

tff(c_2075,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) != '#skF_3'
    | k2_funct_1('#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2020,c_2065])).

tff(c_2098,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2075])).

tff(c_2127,plain,(
    k2_relat_1('#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2125,c_2098])).

tff(c_2135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1520,c_2127])).

tff(c_2136,plain,(
    k2_funct_1('#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2075])).

tff(c_1980,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_2141,plain,(
    ~ v1_funct_2('#skF_3','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2136,c_1980])).

tff(c_2233,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2225,c_2141])).

tff(c_2304,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2301,c_2233])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:43:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.21/1.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.21/1.80  
% 4.21/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.21/1.80  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.21/1.80  
% 4.21/1.80  %Foreground sorts:
% 4.21/1.80  
% 4.21/1.80  
% 4.21/1.80  %Background operators:
% 4.21/1.80  
% 4.21/1.80  
% 4.21/1.80  %Foreground operators:
% 4.21/1.80  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.21/1.80  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.21/1.80  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.21/1.80  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.21/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.21/1.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.21/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.21/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.21/1.80  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.21/1.80  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.21/1.80  tff('#skF_2', type, '#skF_2': $i).
% 4.21/1.80  tff('#skF_3', type, '#skF_3': $i).
% 4.21/1.80  tff('#skF_1', type, '#skF_1': $i).
% 4.21/1.80  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.21/1.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.21/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.21/1.80  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.21/1.80  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.21/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.21/1.80  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.21/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.21/1.80  
% 4.51/1.83  tff(f_144, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 4.51/1.83  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.51/1.83  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.51/1.83  tff(f_85, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 4.51/1.83  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.51/1.83  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 4.51/1.83  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.51/1.83  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.51/1.83  tff(f_75, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 4.51/1.83  tff(f_127, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 4.51/1.83  tff(f_50, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 4.51/1.83  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.51/1.83  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.51/1.83  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.51/1.83  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.51/1.83  tff(c_140, plain, (![C_42, A_43, B_44]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.51/1.83  tff(c_152, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_140])).
% 4.51/1.83  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.51/1.83  tff(c_66, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.51/1.83  tff(c_64, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.51/1.83  tff(c_1175, plain, (![A_158, B_159, C_160]: (k2_relset_1(A_158, B_159, C_160)=k2_relat_1(C_160) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.51/1.83  tff(c_1181, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_1175])).
% 4.51/1.83  tff(c_1194, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1181])).
% 4.51/1.83  tff(c_36, plain, (![A_15]: (k1_relat_1(k2_funct_1(A_15))=k2_relat_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.51/1.83  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.51/1.83  tff(c_307, plain, (![A_64, B_65, C_66]: (k2_relset_1(A_64, B_65, C_66)=k2_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.51/1.83  tff(c_310, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_307])).
% 4.51/1.83  tff(c_322, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_310])).
% 4.51/1.83  tff(c_24, plain, (![A_10]: (k2_relat_1(A_10)!=k1_xboole_0 | k1_xboole_0=A_10 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.51/1.83  tff(c_193, plain, (k2_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_152, c_24])).
% 4.51/1.83  tff(c_208, plain, (k2_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_193])).
% 4.51/1.83  tff(c_325, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_322, c_208])).
% 4.51/1.83  tff(c_70, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.51/1.83  tff(c_349, plain, (![A_73, B_74, C_75]: (k1_relset_1(A_73, B_74, C_75)=k1_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.51/1.83  tff(c_363, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_349])).
% 4.51/1.83  tff(c_501, plain, (![B_95, A_96, C_97]: (k1_xboole_0=B_95 | k1_relset_1(A_96, B_95, C_97)=A_96 | ~v1_funct_2(C_97, A_96, B_95) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_96, B_95))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.51/1.83  tff(c_507, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_501])).
% 4.51/1.83  tff(c_521, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_363, c_507])).
% 4.51/1.83  tff(c_522, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_325, c_521])).
% 4.51/1.83  tff(c_34, plain, (![A_15]: (k2_relat_1(k2_funct_1(A_15))=k1_relat_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.51/1.83  tff(c_32, plain, (![A_14]: (v1_relat_1(k2_funct_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.51/1.83  tff(c_30, plain, (![A_14]: (v1_funct_1(k2_funct_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.51/1.83  tff(c_62, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_144])).
% 4.51/1.83  tff(c_154, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_62])).
% 4.51/1.83  tff(c_179, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_154])).
% 4.51/1.83  tff(c_183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_152, c_72, c_179])).
% 4.51/1.83  tff(c_185, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_62])).
% 4.51/1.83  tff(c_366, plain, (![B_76, A_77]: (v1_funct_2(B_76, k1_relat_1(B_76), A_77) | ~r1_tarski(k2_relat_1(B_76), A_77) | ~v1_funct_1(B_76) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.51/1.83  tff(c_857, plain, (![A_124, A_125]: (v1_funct_2(k2_funct_1(A_124), k2_relat_1(A_124), A_125) | ~r1_tarski(k2_relat_1(k2_funct_1(A_124)), A_125) | ~v1_funct_1(k2_funct_1(A_124)) | ~v1_relat_1(k2_funct_1(A_124)) | ~v2_funct_1(A_124) | ~v1_funct_1(A_124) | ~v1_relat_1(A_124))), inference(superposition, [status(thm), theory('equality')], [c_36, c_366])).
% 4.51/1.83  tff(c_863, plain, (![A_125]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_125) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_125) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_322, c_857])).
% 4.51/1.83  tff(c_872, plain, (![A_125]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_125) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_125) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_72, c_66, c_185, c_863])).
% 4.51/1.83  tff(c_875, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_872])).
% 4.51/1.83  tff(c_878, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_875])).
% 4.51/1.83  tff(c_882, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_152, c_72, c_878])).
% 4.51/1.83  tff(c_884, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_872])).
% 4.51/1.83  tff(c_398, plain, (![B_81, A_82]: (m1_subset_1(B_81, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_81), A_82))) | ~r1_tarski(k2_relat_1(B_81), A_82) | ~v1_funct_1(B_81) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.51/1.83  tff(c_894, plain, (![A_126, A_127]: (m1_subset_1(k2_funct_1(A_126), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_126), A_127))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_126)), A_127) | ~v1_funct_1(k2_funct_1(A_126)) | ~v1_relat_1(k2_funct_1(A_126)) | ~v2_funct_1(A_126) | ~v1_funct_1(A_126) | ~v1_relat_1(A_126))), inference(superposition, [status(thm), theory('equality')], [c_36, c_398])).
% 4.51/1.83  tff(c_917, plain, (![A_127]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_127))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_127) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_322, c_894])).
% 4.51/1.83  tff(c_950, plain, (![A_128]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_128))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_128))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_72, c_66, c_884, c_185, c_917])).
% 4.51/1.83  tff(c_184, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_62])).
% 4.51/1.83  tff(c_210, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_184])).
% 4.51/1.83  tff(c_985, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(resolution, [status(thm)], [c_950, c_210])).
% 4.51/1.83  tff(c_990, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_34, c_985])).
% 4.51/1.83  tff(c_993, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_152, c_72, c_66, c_6, c_522, c_990])).
% 4.51/1.83  tff(c_994, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_184])).
% 4.51/1.83  tff(c_1197, plain, (k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1194, c_208])).
% 4.51/1.83  tff(c_1127, plain, (![A_149, B_150, C_151]: (k1_relset_1(A_149, B_150, C_151)=k1_relat_1(C_151) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.51/1.83  tff(c_1145, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_1127])).
% 4.51/1.83  tff(c_1312, plain, (![B_177, A_178, C_179]: (k1_xboole_0=B_177 | k1_relset_1(A_178, B_177, C_179)=A_178 | ~v1_funct_2(C_179, A_178, B_177) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_178, B_177))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.51/1.83  tff(c_1321, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_1312])).
% 4.51/1.83  tff(c_1337, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1145, c_1321])).
% 4.51/1.83  tff(c_1338, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_1197, c_1337])).
% 4.51/1.83  tff(c_26, plain, (![A_10]: (k1_relat_1(A_10)!=k1_xboole_0 | k1_xboole_0=A_10 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.51/1.83  tff(c_192, plain, (k1_relat_1('#skF_3')!=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_152, c_26])).
% 4.51/1.83  tff(c_209, plain, (k1_relat_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_192])).
% 4.51/1.83  tff(c_1343, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1338, c_209])).
% 4.51/1.83  tff(c_995, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_184])).
% 4.51/1.83  tff(c_1144, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_995, c_1127])).
% 4.51/1.83  tff(c_1426, plain, (![B_185, C_186, A_187]: (k1_xboole_0=B_185 | v1_funct_2(C_186, A_187, B_185) | k1_relset_1(A_187, B_185, C_186)!=A_187 | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_187, B_185))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.51/1.83  tff(c_1435, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_995, c_1426])).
% 4.51/1.83  tff(c_1452, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1144, c_1435])).
% 4.51/1.83  tff(c_1453, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_994, c_1343, c_1452])).
% 4.51/1.83  tff(c_1463, plain, (k2_relat_1('#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_36, c_1453])).
% 4.51/1.83  tff(c_1466, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_152, c_72, c_66, c_1194, c_1463])).
% 4.51/1.83  tff(c_1467, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_192])).
% 4.51/1.83  tff(c_1469, plain, (k2_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1467, c_208])).
% 4.51/1.83  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.51/1.83  tff(c_1478, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1467, c_1467, c_20])).
% 4.51/1.83  tff(c_1494, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1469, c_1478])).
% 4.51/1.83  tff(c_1495, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_193])).
% 4.51/1.83  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.51/1.83  tff(c_1507, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1495, c_8])).
% 4.51/1.83  tff(c_1496, plain, (k2_relat_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_193])).
% 4.51/1.83  tff(c_1520, plain, (k2_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1495, c_1496])).
% 4.51/1.83  tff(c_22, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.51/1.83  tff(c_1506, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1495, c_1495, c_22])).
% 4.51/1.83  tff(c_2293, plain, (![B_298, A_299]: (v1_funct_2(B_298, k1_relat_1(B_298), A_299) | ~r1_tarski(k2_relat_1(B_298), A_299) | ~v1_funct_1(B_298) | ~v1_relat_1(B_298))), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.51/1.83  tff(c_2299, plain, (![A_299]: (v1_funct_2('#skF_3', '#skF_3', A_299) | ~r1_tarski(k2_relat_1('#skF_3'), A_299) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1506, c_2293])).
% 4.51/1.83  tff(c_2301, plain, (![A_299]: (v1_funct_2('#skF_3', '#skF_3', A_299))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_72, c_1507, c_1520, c_2299])).
% 4.51/1.83  tff(c_16, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.51/1.83  tff(c_1502, plain, (![A_6]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_1495, c_16])).
% 4.51/1.83  tff(c_2212, plain, (![A_279, B_280, C_281]: (k2_relset_1(A_279, B_280, C_281)=k2_relat_1(C_281) | ~m1_subset_1(C_281, k1_zfmisc_1(k2_zfmisc_1(A_279, B_280))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.51/1.83  tff(c_2222, plain, (![A_279, B_280]: (k2_relset_1(A_279, B_280, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1502, c_2212])).
% 4.51/1.83  tff(c_2224, plain, (![A_279, B_280]: (k2_relset_1(A_279, B_280, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1520, c_2222])).
% 4.51/1.83  tff(c_2225, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2224, c_64])).
% 4.51/1.83  tff(c_2111, plain, (![A_273]: (k1_relat_1(k2_funct_1(A_273))=k2_relat_1(A_273) | ~v2_funct_1(A_273) | ~v1_funct_1(A_273) | ~v1_relat_1(A_273))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.51/1.83  tff(c_120, plain, (![A_39]: (v1_relat_1(k2_funct_1(A_39)) | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.51/1.83  tff(c_128, plain, (![A_39]: (k2_relat_1(k2_funct_1(A_39))!=k1_xboole_0 | k2_funct_1(A_39)=k1_xboole_0 | ~v1_funct_1(A_39) | ~v1_relat_1(A_39))), inference(resolution, [status(thm)], [c_120, c_24])).
% 4.51/1.83  tff(c_1659, plain, (![A_211]: (k2_relat_1(k2_funct_1(A_211))!='#skF_3' | k2_funct_1(A_211)='#skF_3' | ~v1_funct_1(A_211) | ~v1_relat_1(A_211))), inference(demodulation, [status(thm), theory('equality')], [c_1495, c_1495, c_128])).
% 4.51/1.83  tff(c_1968, plain, (![A_254]: (k1_relat_1(A_254)!='#skF_3' | k2_funct_1(A_254)='#skF_3' | ~v1_funct_1(A_254) | ~v1_relat_1(A_254) | ~v2_funct_1(A_254) | ~v1_funct_1(A_254) | ~v1_relat_1(A_254))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1659])).
% 4.51/1.83  tff(c_1971, plain, (k1_relat_1('#skF_3')!='#skF_3' | k2_funct_1('#skF_3')='#skF_3' | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_1968])).
% 4.51/1.83  tff(c_1974, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_152, c_72, c_1506, c_1971])).
% 4.51/1.83  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.51/1.83  tff(c_1503, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1495, c_1495, c_14])).
% 4.51/1.83  tff(c_1708, plain, (![A_224, B_225, C_226]: (k2_relset_1(A_224, B_225, C_226)=k2_relat_1(C_226) | ~m1_subset_1(C_226, k1_zfmisc_1(k2_zfmisc_1(A_224, B_225))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.51/1.83  tff(c_1718, plain, (![A_224, B_225]: (k2_relset_1(A_224, B_225, '#skF_3')=k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1502, c_1708])).
% 4.51/1.83  tff(c_1720, plain, (![A_224, B_225]: (k2_relset_1(A_224, B_225, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1520, c_1718])).
% 4.51/1.83  tff(c_1721, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1720, c_64])).
% 4.51/1.83  tff(c_1533, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_184])).
% 4.51/1.83  tff(c_1729, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1721, c_1533])).
% 4.51/1.83  tff(c_1731, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1503, c_1729])).
% 4.51/1.83  tff(c_1975, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1974, c_1731])).
% 4.51/1.83  tff(c_1979, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1502, c_1975])).
% 4.51/1.83  tff(c_1981, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_184])).
% 4.51/1.83  tff(c_38, plain, (![C_18, A_16, B_17]: (v1_relat_1(C_18) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.51/1.83  tff(c_2020, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_1981, c_38])).
% 4.51/1.83  tff(c_2081, plain, (![A_269]: (k1_relat_1(A_269)!='#skF_3' | A_269='#skF_3' | ~v1_relat_1(A_269))), inference(demodulation, [status(thm), theory('equality')], [c_1495, c_1495, c_26])).
% 4.51/1.83  tff(c_2091, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_3' | k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_2020, c_2081])).
% 4.51/1.83  tff(c_2099, plain, (k1_relat_1(k2_funct_1('#skF_3'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_2091])).
% 4.51/1.83  tff(c_2117, plain, (k2_relat_1('#skF_3')!='#skF_3' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2111, c_2099])).
% 4.51/1.83  tff(c_2124, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_152, c_72, c_66, c_1520, c_2117])).
% 4.51/1.83  tff(c_2125, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_2091])).
% 4.51/1.83  tff(c_2065, plain, (![A_268]: (k2_relat_1(A_268)!='#skF_3' | A_268='#skF_3' | ~v1_relat_1(A_268))), inference(demodulation, [status(thm), theory('equality')], [c_1495, c_1495, c_24])).
% 4.51/1.83  tff(c_2075, plain, (k2_relat_1(k2_funct_1('#skF_3'))!='#skF_3' | k2_funct_1('#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_2020, c_2065])).
% 4.51/1.83  tff(c_2098, plain, (k2_relat_1(k2_funct_1('#skF_3'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_2075])).
% 4.51/1.83  tff(c_2127, plain, (k2_relat_1('#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2125, c_2098])).
% 4.51/1.83  tff(c_2135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1520, c_2127])).
% 4.51/1.83  tff(c_2136, plain, (k2_funct_1('#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_2075])).
% 4.51/1.83  tff(c_1980, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_184])).
% 4.51/1.83  tff(c_2141, plain, (~v1_funct_2('#skF_3', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2136, c_1980])).
% 4.51/1.83  tff(c_2233, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2225, c_2141])).
% 4.51/1.83  tff(c_2304, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2301, c_2233])).
% 4.51/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.51/1.83  
% 4.51/1.83  Inference rules
% 4.51/1.83  ----------------------
% 4.51/1.83  #Ref     : 0
% 4.51/1.83  #Sup     : 462
% 4.51/1.83  #Fact    : 0
% 4.51/1.83  #Define  : 0
% 4.51/1.83  #Split   : 17
% 4.51/1.83  #Chain   : 0
% 4.51/1.83  #Close   : 0
% 4.51/1.83  
% 4.51/1.83  Ordering : KBO
% 4.51/1.83  
% 4.51/1.83  Simplification rules
% 4.51/1.83  ----------------------
% 4.51/1.83  #Subsume      : 54
% 4.51/1.83  #Demod        : 532
% 4.51/1.83  #Tautology    : 260
% 4.51/1.83  #SimpNegUnit  : 9
% 4.51/1.83  #BackRed      : 50
% 4.51/1.83  
% 4.51/1.83  #Partial instantiations: 0
% 4.51/1.83  #Strategies tried      : 1
% 4.51/1.83  
% 4.51/1.83  Timing (in seconds)
% 4.51/1.83  ----------------------
% 4.51/1.83  Preprocessing        : 0.37
% 4.51/1.83  Parsing              : 0.21
% 4.51/1.83  CNF conversion       : 0.02
% 4.51/1.83  Main loop            : 0.62
% 4.51/1.83  Inferencing          : 0.23
% 4.51/1.83  Reduction            : 0.20
% 4.51/1.83  Demodulation         : 0.14
% 4.51/1.83  BG Simplification    : 0.03
% 4.51/1.83  Subsumption          : 0.11
% 4.51/1.83  Abstraction          : 0.03
% 4.51/1.83  MUC search           : 0.00
% 4.51/1.83  Cooper               : 0.00
% 4.51/1.83  Total                : 1.06
% 4.51/1.83  Index Insertion      : 0.00
% 4.51/1.83  Index Deletion       : 0.00
% 4.51/1.83  Index Matching       : 0.00
% 4.51/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
