%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:39 EST 2020

% Result     : Theorem 7.56s
% Output     : CNFRefutation 7.56s
% Verified   : 
% Statistics : Number of formulae       :  171 (2201 expanded)
%              Number of leaves         :   41 ( 688 expanded)
%              Depth                    :   13
%              Number of atoms          :  273 (6918 expanded)
%              Number of equality atoms :   72 (2621 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_150,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(A,B,D,C))
              & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
              & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_66,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_116,axiom,(
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

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_130,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_124,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_70,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_68,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_30,plain,(
    ! [A_16,B_17] : v1_relat_1(k2_zfmisc_1(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_828,plain,(
    ! [B_125,A_126] :
      ( v1_relat_1(B_125)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(A_126))
      | ~ v1_relat_1(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_834,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_70,c_828])).

tff(c_838,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_834])).

tff(c_66,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_82,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_72,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_3241,plain,(
    ! [A_322,B_323,C_324] :
      ( k1_relset_1(A_322,B_323,C_324) = k1_relat_1(C_324)
      | ~ m1_subset_1(C_324,k1_zfmisc_1(k2_zfmisc_1(A_322,B_323))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_3260,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_3241])).

tff(c_4059,plain,(
    ! [B_393,A_394,C_395] :
      ( k1_xboole_0 = B_393
      | k1_relset_1(A_394,B_393,C_395) = A_394
      | ~ v1_funct_2(C_395,A_394,B_393)
      | ~ m1_subset_1(C_395,k1_zfmisc_1(k2_zfmisc_1(A_394,B_393))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_4072,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_4059])).

tff(c_4085,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_3260,c_4072])).

tff(c_4086,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_4085])).

tff(c_36,plain,(
    ! [B_22,A_21] :
      ( k1_relat_1(k7_relat_1(B_22,A_21)) = A_21
      | ~ r1_tarski(A_21,k1_relat_1(B_22))
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4095,plain,(
    ! [A_21] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_21)) = A_21
      | ~ r1_tarski(A_21,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4086,c_36])).

tff(c_4101,plain,(
    ! [A_21] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_21)) = A_21
      | ~ r1_tarski(A_21,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_838,c_4095])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_3866,plain,(
    ! [A_384,B_385,C_386,D_387] :
      ( k2_partfun1(A_384,B_385,C_386,D_387) = k7_relat_1(C_386,D_387)
      | ~ m1_subset_1(C_386,k1_zfmisc_1(k2_zfmisc_1(A_384,B_385)))
      | ~ v1_funct_1(C_386) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_3875,plain,(
    ! [D_387] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_387) = k7_relat_1('#skF_4',D_387)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_70,c_3866])).

tff(c_3887,plain,(
    ! [D_387] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_387) = k7_relat_1('#skF_4',D_387) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3875])).

tff(c_1800,plain,(
    ! [A_221,B_222,C_223,D_224] :
      ( k2_partfun1(A_221,B_222,C_223,D_224) = k7_relat_1(C_223,D_224)
      | ~ m1_subset_1(C_223,k1_zfmisc_1(k2_zfmisc_1(A_221,B_222)))
      | ~ v1_funct_1(C_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1807,plain,(
    ! [D_224] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_224) = k7_relat_1('#skF_4',D_224)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_70,c_1800])).

tff(c_1816,plain,(
    ! [D_224] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_224) = k7_relat_1('#skF_4',D_224) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1807])).

tff(c_2472,plain,(
    ! [A_260,B_261,C_262,D_263] :
      ( m1_subset_1(k2_partfun1(A_260,B_261,C_262,D_263),k1_zfmisc_1(k2_zfmisc_1(A_260,B_261)))
      | ~ m1_subset_1(C_262,k1_zfmisc_1(k2_zfmisc_1(A_260,B_261)))
      | ~ v1_funct_1(C_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2500,plain,(
    ! [D_224] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_224),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1816,c_2472])).

tff(c_2522,plain,(
    ! [D_264] : m1_subset_1(k7_relat_1('#skF_4',D_264),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_2500])).

tff(c_38,plain,(
    ! [C_25,B_24,A_23] :
      ( v5_relat_1(C_25,B_24)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2564,plain,(
    ! [D_264] : v5_relat_1(k7_relat_1('#skF_4',D_264),'#skF_2') ),
    inference(resolution,[status(thm)],[c_2522,c_38])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(k7_relat_1(A_14,B_15))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1622,plain,(
    ! [C_207,A_208,B_209] :
      ( m1_subset_1(C_207,k1_zfmisc_1(k2_zfmisc_1(A_208,B_209)))
      | ~ r1_tarski(k2_relat_1(C_207),B_209)
      | ~ r1_tarski(k1_relat_1(C_207),A_208)
      | ~ v1_relat_1(C_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_804,plain,(
    ! [A_119,B_120,C_121,D_122] :
      ( v1_funct_1(k2_partfun1(A_119,B_120,C_121,D_122))
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120)))
      | ~ v1_funct_1(C_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_809,plain,(
    ! [D_122] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_122))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_70,c_804])).

tff(c_817,plain,(
    ! [D_122] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_122)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_809])).

tff(c_64,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_170,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_820,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_817,c_170])).

tff(c_821,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_869,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_821])).

tff(c_1652,plain,
    ( ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')),'#skF_3')
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1622,c_869])).

tff(c_2025,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1816,c_1816,c_1816,c_1652])).

tff(c_2026,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2025])).

tff(c_2029,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_2026])).

tff(c_2033,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_838,c_2029])).

tff(c_2035,plain,(
    v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2025])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v5_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_34,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_20,A_19)),A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_44,plain,(
    ! [C_31,A_29,B_30] :
      ( m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30)))
      | ~ r1_tarski(k2_relat_1(C_31),B_30)
      | ~ r1_tarski(k1_relat_1(C_31),A_29)
      | ~ v1_relat_1(C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1819,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1816,c_869])).

tff(c_1838,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_1819])).

tff(c_2230,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2035,c_1838])).

tff(c_2231,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2230])).

tff(c_2234,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_2231])).

tff(c_2238,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_838,c_2234])).

tff(c_2239,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_2230])).

tff(c_2250,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_26,c_2239])).

tff(c_2253,plain,(
    ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2035,c_2250])).

tff(c_2589,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2564,c_2253])).

tff(c_2591,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_821])).

tff(c_3258,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2591,c_3241])).

tff(c_3890,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3887,c_3887,c_3258])).

tff(c_2590,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_821])).

tff(c_3898,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3887,c_2590])).

tff(c_3897,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3887,c_2591])).

tff(c_52,plain,(
    ! [B_33,C_34,A_32] :
      ( k1_xboole_0 = B_33
      | v1_funct_2(C_34,A_32,B_33)
      | k1_relset_1(A_32,B_33,C_34) != A_32
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_3996,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_3897,c_52])).

tff(c_4018,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_3898,c_82,c_3996])).

tff(c_4223,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3890,c_4018])).

tff(c_4230,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4101,c_4223])).

tff(c_4234,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_4230])).

tff(c_4235,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_16,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4251,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_1',B_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4235,c_4235,c_16])).

tff(c_4236,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_4242,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4235,c_4236])).

tff(c_4250,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4242,c_70])).

tff(c_4252,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4251,c_4250])).

tff(c_5924,plain,(
    ! [A_569,B_570] :
      ( r1_tarski(A_569,B_570)
      | ~ m1_subset_1(A_569,k1_zfmisc_1(B_570)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_5928,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_4252,c_5924])).

tff(c_10,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4281,plain,(
    ! [A_4] :
      ( A_4 = '#skF_1'
      | ~ r1_tarski(A_4,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4235,c_4235,c_10])).

tff(c_5932,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5928,c_4281])).

tff(c_4243,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4242,c_72])).

tff(c_5944,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5932,c_5932,c_4243])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4237,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4235,c_8])).

tff(c_5945,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5932,c_4237])).

tff(c_4253,plain,(
    ! [B_401] : k2_zfmisc_1('#skF_1',B_401) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4235,c_4235,c_16])).

tff(c_4257,plain,(
    v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4253,c_30])).

tff(c_32,plain,(
    ! [A_18] :
      ( k7_relat_1(A_18,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4307,plain,(
    ! [A_406] :
      ( k7_relat_1(A_406,'#skF_1') = '#skF_1'
      | ~ v1_relat_1(A_406) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4235,c_4235,c_32])).

tff(c_4318,plain,(
    k7_relat_1('#skF_1','#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4257,c_4307])).

tff(c_5936,plain,(
    k7_relat_1('#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5932,c_5932,c_5932,c_4318])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_7159,plain,(
    ! [A_696,B_697,C_698,D_699] :
      ( k2_partfun1(A_696,B_697,C_698,D_699) = k7_relat_1(C_698,D_699)
      | ~ m1_subset_1(C_698,k1_zfmisc_1(k2_zfmisc_1(A_696,B_697)))
      | ~ v1_funct_1(C_698) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_9003,plain,(
    ! [A_847,B_848,A_849,D_850] :
      ( k2_partfun1(A_847,B_848,A_849,D_850) = k7_relat_1(A_849,D_850)
      | ~ v1_funct_1(A_849)
      | ~ r1_tarski(A_849,k2_zfmisc_1(A_847,B_848)) ) ),
    inference(resolution,[status(thm)],[c_20,c_7159])).

tff(c_9016,plain,(
    ! [A_847,B_848,D_850] :
      ( k2_partfun1(A_847,B_848,'#skF_4',D_850) = k7_relat_1('#skF_4',D_850)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5945,c_9003])).

tff(c_9024,plain,(
    ! [A_847,B_848,D_850] : k2_partfun1(A_847,B_848,'#skF_4',D_850) = k7_relat_1('#skF_4',D_850) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_9016])).

tff(c_4350,plain,(
    ! [A_411,B_412] :
      ( r1_tarski(A_411,B_412)
      | ~ m1_subset_1(A_411,k1_zfmisc_1(B_412)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4358,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_4252,c_4350])).

tff(c_4362,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4358,c_4281])).

tff(c_4386,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4362,c_4252])).

tff(c_14,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4262,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4235,c_4235,c_14])).

tff(c_4387,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4362,c_4362,c_4262])).

tff(c_5326,plain,(
    ! [A_507,B_508,C_509,D_510] :
      ( v1_funct_1(k2_partfun1(A_507,B_508,C_509,D_510))
      | ~ m1_subset_1(C_509,k1_zfmisc_1(k2_zfmisc_1(A_507,B_508)))
      | ~ v1_funct_1(C_509) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_5891,plain,(
    ! [A_564,C_565,D_566] :
      ( v1_funct_1(k2_partfun1(A_564,'#skF_4',C_565,D_566))
      | ~ m1_subset_1(C_565,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_565) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4387,c_5326])).

tff(c_5893,plain,(
    ! [A_564,D_566] :
      ( v1_funct_1(k2_partfun1(A_564,'#skF_4','#skF_4',D_566))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4386,c_5891])).

tff(c_5899,plain,(
    ! [A_564,D_566] : v1_funct_1(k2_partfun1(A_564,'#skF_4','#skF_4',D_566)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_5893])).

tff(c_4282,plain,(
    ! [A_403] :
      ( A_403 = '#skF_1'
      | ~ r1_tarski(A_403,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4235,c_4235,c_10])).

tff(c_4298,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_68,c_4282])).

tff(c_4329,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4298,c_4242,c_4298,c_4298,c_4242,c_4242,c_4298,c_4262,c_4242,c_4242,c_64])).

tff(c_4330,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_4329])).

tff(c_4380,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4362,c_4362,c_4362,c_4330])).

tff(c_5903,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5899,c_4380])).

tff(c_5904,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_4329])).

tff(c_6069,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5932,c_5932,c_5932,c_5932,c_5932,c_5932,c_5932,c_5932,c_5932,c_5904])).

tff(c_6070,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_6069])).

tff(c_6170,plain,(
    ~ r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_6070])).

tff(c_9029,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9024,c_6170])).

tff(c_9033,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5945,c_5936,c_9029])).

tff(c_9035,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_6069])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_9067,plain,(
    r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_9035,c_18])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_9077,plain,
    ( k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_9067,c_2])).

tff(c_9083,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5945,c_9077])).

tff(c_9034,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_6069])).

tff(c_9145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5944,c_9083,c_9034])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:56:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.56/2.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.56/2.63  
% 7.56/2.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.56/2.64  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.56/2.64  
% 7.56/2.64  %Foreground sorts:
% 7.56/2.64  
% 7.56/2.64  
% 7.56/2.64  %Background operators:
% 7.56/2.64  
% 7.56/2.64  
% 7.56/2.64  %Foreground operators:
% 7.56/2.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.56/2.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.56/2.64  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.56/2.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.56/2.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.56/2.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.56/2.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.56/2.64  tff('#skF_2', type, '#skF_2': $i).
% 7.56/2.64  tff('#skF_3', type, '#skF_3': $i).
% 7.56/2.64  tff('#skF_1', type, '#skF_1': $i).
% 7.56/2.64  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.56/2.64  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.56/2.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.56/2.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.56/2.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.56/2.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.56/2.64  tff('#skF_4', type, '#skF_4': $i).
% 7.56/2.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.56/2.64  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 7.56/2.64  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.56/2.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.56/2.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.56/2.64  
% 7.56/2.66  tff(f_150, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 7.56/2.66  tff(f_66, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.56/2.66  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.56/2.66  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.56/2.66  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.56/2.66  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 7.56/2.66  tff(f_130, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 7.56/2.66  tff(f_124, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 7.56/2.66  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.56/2.66  tff(f_64, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 7.56/2.66  tff(f_98, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 7.56/2.66  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 7.56/2.66  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 7.56/2.66  tff(f_43, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.56/2.66  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.56/2.66  tff(f_37, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 7.56/2.66  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.56/2.66  tff(f_70, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_relat_1)).
% 7.56/2.66  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.56/2.66  tff(c_68, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.56/2.66  tff(c_30, plain, (![A_16, B_17]: (v1_relat_1(k2_zfmisc_1(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.56/2.66  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.56/2.66  tff(c_828, plain, (![B_125, A_126]: (v1_relat_1(B_125) | ~m1_subset_1(B_125, k1_zfmisc_1(A_126)) | ~v1_relat_1(A_126))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.56/2.66  tff(c_834, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_70, c_828])).
% 7.56/2.66  tff(c_838, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_834])).
% 7.56/2.66  tff(c_66, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.56/2.66  tff(c_82, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_66])).
% 7.56/2.66  tff(c_72, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.56/2.66  tff(c_3241, plain, (![A_322, B_323, C_324]: (k1_relset_1(A_322, B_323, C_324)=k1_relat_1(C_324) | ~m1_subset_1(C_324, k1_zfmisc_1(k2_zfmisc_1(A_322, B_323))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.56/2.66  tff(c_3260, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_3241])).
% 7.56/2.66  tff(c_4059, plain, (![B_393, A_394, C_395]: (k1_xboole_0=B_393 | k1_relset_1(A_394, B_393, C_395)=A_394 | ~v1_funct_2(C_395, A_394, B_393) | ~m1_subset_1(C_395, k1_zfmisc_1(k2_zfmisc_1(A_394, B_393))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.56/2.66  tff(c_4072, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_70, c_4059])).
% 7.56/2.66  tff(c_4085, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_3260, c_4072])).
% 7.56/2.66  tff(c_4086, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_82, c_4085])).
% 7.56/2.66  tff(c_36, plain, (![B_22, A_21]: (k1_relat_1(k7_relat_1(B_22, A_21))=A_21 | ~r1_tarski(A_21, k1_relat_1(B_22)) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.56/2.66  tff(c_4095, plain, (![A_21]: (k1_relat_1(k7_relat_1('#skF_4', A_21))=A_21 | ~r1_tarski(A_21, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4086, c_36])).
% 7.56/2.66  tff(c_4101, plain, (![A_21]: (k1_relat_1(k7_relat_1('#skF_4', A_21))=A_21 | ~r1_tarski(A_21, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_838, c_4095])).
% 7.56/2.66  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.56/2.66  tff(c_3866, plain, (![A_384, B_385, C_386, D_387]: (k2_partfun1(A_384, B_385, C_386, D_387)=k7_relat_1(C_386, D_387) | ~m1_subset_1(C_386, k1_zfmisc_1(k2_zfmisc_1(A_384, B_385))) | ~v1_funct_1(C_386))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.56/2.66  tff(c_3875, plain, (![D_387]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_387)=k7_relat_1('#skF_4', D_387) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_70, c_3866])).
% 7.56/2.66  tff(c_3887, plain, (![D_387]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_387)=k7_relat_1('#skF_4', D_387))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_3875])).
% 7.56/2.66  tff(c_1800, plain, (![A_221, B_222, C_223, D_224]: (k2_partfun1(A_221, B_222, C_223, D_224)=k7_relat_1(C_223, D_224) | ~m1_subset_1(C_223, k1_zfmisc_1(k2_zfmisc_1(A_221, B_222))) | ~v1_funct_1(C_223))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.56/2.66  tff(c_1807, plain, (![D_224]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_224)=k7_relat_1('#skF_4', D_224) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_70, c_1800])).
% 7.56/2.66  tff(c_1816, plain, (![D_224]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_224)=k7_relat_1('#skF_4', D_224))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1807])).
% 7.56/2.66  tff(c_2472, plain, (![A_260, B_261, C_262, D_263]: (m1_subset_1(k2_partfun1(A_260, B_261, C_262, D_263), k1_zfmisc_1(k2_zfmisc_1(A_260, B_261))) | ~m1_subset_1(C_262, k1_zfmisc_1(k2_zfmisc_1(A_260, B_261))) | ~v1_funct_1(C_262))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.56/2.66  tff(c_2500, plain, (![D_224]: (m1_subset_1(k7_relat_1('#skF_4', D_224), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1816, c_2472])).
% 7.56/2.66  tff(c_2522, plain, (![D_264]: (m1_subset_1(k7_relat_1('#skF_4', D_264), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_2500])).
% 7.56/2.66  tff(c_38, plain, (![C_25, B_24, A_23]: (v5_relat_1(C_25, B_24) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.56/2.66  tff(c_2564, plain, (![D_264]: (v5_relat_1(k7_relat_1('#skF_4', D_264), '#skF_2'))), inference(resolution, [status(thm)], [c_2522, c_38])).
% 7.56/2.66  tff(c_28, plain, (![A_14, B_15]: (v1_relat_1(k7_relat_1(A_14, B_15)) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.56/2.66  tff(c_1622, plain, (![C_207, A_208, B_209]: (m1_subset_1(C_207, k1_zfmisc_1(k2_zfmisc_1(A_208, B_209))) | ~r1_tarski(k2_relat_1(C_207), B_209) | ~r1_tarski(k1_relat_1(C_207), A_208) | ~v1_relat_1(C_207))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.56/2.66  tff(c_804, plain, (![A_119, B_120, C_121, D_122]: (v1_funct_1(k2_partfun1(A_119, B_120, C_121, D_122)) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))) | ~v1_funct_1(C_121))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.56/2.66  tff(c_809, plain, (![D_122]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_122)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_70, c_804])).
% 7.56/2.66  tff(c_817, plain, (![D_122]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_122)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_809])).
% 7.56/2.66  tff(c_64, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.56/2.66  tff(c_170, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_64])).
% 7.56/2.66  tff(c_820, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_817, c_170])).
% 7.56/2.66  tff(c_821, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_64])).
% 7.56/2.66  tff(c_869, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_821])).
% 7.56/2.66  tff(c_1652, plain, (~r1_tarski(k2_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski(k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3')), '#skF_3') | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_1622, c_869])).
% 7.56/2.66  tff(c_2025, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1816, c_1816, c_1816, c_1652])).
% 7.56/2.66  tff(c_2026, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_2025])).
% 7.56/2.66  tff(c_2029, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_2026])).
% 7.56/2.66  tff(c_2033, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_838, c_2029])).
% 7.56/2.66  tff(c_2035, plain, (v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_2025])).
% 7.56/2.66  tff(c_26, plain, (![B_13, A_12]: (r1_tarski(k2_relat_1(B_13), A_12) | ~v5_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.56/2.66  tff(c_34, plain, (![B_20, A_19]: (r1_tarski(k1_relat_1(k7_relat_1(B_20, A_19)), A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.56/2.66  tff(c_44, plain, (![C_31, A_29, B_30]: (m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))) | ~r1_tarski(k2_relat_1(C_31), B_30) | ~r1_tarski(k1_relat_1(C_31), A_29) | ~v1_relat_1(C_31))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.56/2.66  tff(c_1819, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1816, c_869])).
% 7.56/2.66  tff(c_1838, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_44, c_1819])).
% 7.56/2.66  tff(c_2230, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2035, c_1838])).
% 7.56/2.66  tff(c_2231, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3')), inference(splitLeft, [status(thm)], [c_2230])).
% 7.56/2.66  tff(c_2234, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_2231])).
% 7.56/2.66  tff(c_2238, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_838, c_2234])).
% 7.56/2.66  tff(c_2239, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(splitRight, [status(thm)], [c_2230])).
% 7.56/2.66  tff(c_2250, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_2239])).
% 7.56/2.66  tff(c_2253, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2035, c_2250])).
% 7.56/2.66  tff(c_2589, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2564, c_2253])).
% 7.56/2.66  tff(c_2591, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_821])).
% 7.56/2.66  tff(c_3258, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_2591, c_3241])).
% 7.56/2.66  tff(c_3890, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3887, c_3887, c_3258])).
% 7.56/2.66  tff(c_2590, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_821])).
% 7.56/2.66  tff(c_3898, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3887, c_2590])).
% 7.56/2.66  tff(c_3897, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_3887, c_2591])).
% 7.56/2.66  tff(c_52, plain, (![B_33, C_34, A_32]: (k1_xboole_0=B_33 | v1_funct_2(C_34, A_32, B_33) | k1_relset_1(A_32, B_33, C_34)!=A_32 | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.56/2.66  tff(c_3996, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_3897, c_52])).
% 7.56/2.66  tff(c_4018, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_3898, c_82, c_3996])).
% 7.56/2.66  tff(c_4223, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3890, c_4018])).
% 7.56/2.66  tff(c_4230, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4101, c_4223])).
% 7.56/2.66  tff(c_4234, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_4230])).
% 7.56/2.66  tff(c_4235, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_66])).
% 7.56/2.66  tff(c_16, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.56/2.66  tff(c_4251, plain, (![B_6]: (k2_zfmisc_1('#skF_1', B_6)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4235, c_4235, c_16])).
% 7.56/2.66  tff(c_4236, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_66])).
% 7.56/2.66  tff(c_4242, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4235, c_4236])).
% 7.56/2.66  tff(c_4250, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4242, c_70])).
% 7.56/2.66  tff(c_4252, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4251, c_4250])).
% 7.56/2.66  tff(c_5924, plain, (![A_569, B_570]: (r1_tarski(A_569, B_570) | ~m1_subset_1(A_569, k1_zfmisc_1(B_570)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.56/2.66  tff(c_5928, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_4252, c_5924])).
% 7.56/2.66  tff(c_10, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.56/2.66  tff(c_4281, plain, (![A_4]: (A_4='#skF_1' | ~r1_tarski(A_4, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4235, c_4235, c_10])).
% 7.56/2.66  tff(c_5932, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_5928, c_4281])).
% 7.56/2.66  tff(c_4243, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4242, c_72])).
% 7.56/2.66  tff(c_5944, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5932, c_5932, c_4243])).
% 7.56/2.66  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.56/2.66  tff(c_4237, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_4235, c_8])).
% 7.56/2.66  tff(c_5945, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_5932, c_4237])).
% 7.56/2.66  tff(c_4253, plain, (![B_401]: (k2_zfmisc_1('#skF_1', B_401)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4235, c_4235, c_16])).
% 7.56/2.66  tff(c_4257, plain, (v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4253, c_30])).
% 7.56/2.66  tff(c_32, plain, (![A_18]: (k7_relat_1(A_18, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.56/2.66  tff(c_4307, plain, (![A_406]: (k7_relat_1(A_406, '#skF_1')='#skF_1' | ~v1_relat_1(A_406))), inference(demodulation, [status(thm), theory('equality')], [c_4235, c_4235, c_32])).
% 7.56/2.66  tff(c_4318, plain, (k7_relat_1('#skF_1', '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_4257, c_4307])).
% 7.56/2.66  tff(c_5936, plain, (k7_relat_1('#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5932, c_5932, c_5932, c_4318])).
% 7.56/2.66  tff(c_20, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.56/2.66  tff(c_7159, plain, (![A_696, B_697, C_698, D_699]: (k2_partfun1(A_696, B_697, C_698, D_699)=k7_relat_1(C_698, D_699) | ~m1_subset_1(C_698, k1_zfmisc_1(k2_zfmisc_1(A_696, B_697))) | ~v1_funct_1(C_698))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.56/2.66  tff(c_9003, plain, (![A_847, B_848, A_849, D_850]: (k2_partfun1(A_847, B_848, A_849, D_850)=k7_relat_1(A_849, D_850) | ~v1_funct_1(A_849) | ~r1_tarski(A_849, k2_zfmisc_1(A_847, B_848)))), inference(resolution, [status(thm)], [c_20, c_7159])).
% 7.56/2.66  tff(c_9016, plain, (![A_847, B_848, D_850]: (k2_partfun1(A_847, B_848, '#skF_4', D_850)=k7_relat_1('#skF_4', D_850) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_5945, c_9003])).
% 7.56/2.66  tff(c_9024, plain, (![A_847, B_848, D_850]: (k2_partfun1(A_847, B_848, '#skF_4', D_850)=k7_relat_1('#skF_4', D_850))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_9016])).
% 7.56/2.66  tff(c_4350, plain, (![A_411, B_412]: (r1_tarski(A_411, B_412) | ~m1_subset_1(A_411, k1_zfmisc_1(B_412)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.56/2.66  tff(c_4358, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_4252, c_4350])).
% 7.56/2.66  tff(c_4362, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_4358, c_4281])).
% 7.56/2.66  tff(c_4386, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4362, c_4252])).
% 7.56/2.66  tff(c_14, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.56/2.66  tff(c_4262, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4235, c_4235, c_14])).
% 7.56/2.66  tff(c_4387, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4362, c_4362, c_4262])).
% 7.56/2.66  tff(c_5326, plain, (![A_507, B_508, C_509, D_510]: (v1_funct_1(k2_partfun1(A_507, B_508, C_509, D_510)) | ~m1_subset_1(C_509, k1_zfmisc_1(k2_zfmisc_1(A_507, B_508))) | ~v1_funct_1(C_509))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.56/2.66  tff(c_5891, plain, (![A_564, C_565, D_566]: (v1_funct_1(k2_partfun1(A_564, '#skF_4', C_565, D_566)) | ~m1_subset_1(C_565, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_565))), inference(superposition, [status(thm), theory('equality')], [c_4387, c_5326])).
% 7.56/2.66  tff(c_5893, plain, (![A_564, D_566]: (v1_funct_1(k2_partfun1(A_564, '#skF_4', '#skF_4', D_566)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_4386, c_5891])).
% 7.56/2.66  tff(c_5899, plain, (![A_564, D_566]: (v1_funct_1(k2_partfun1(A_564, '#skF_4', '#skF_4', D_566)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_5893])).
% 7.56/2.66  tff(c_4282, plain, (![A_403]: (A_403='#skF_1' | ~r1_tarski(A_403, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4235, c_4235, c_10])).
% 7.56/2.66  tff(c_4298, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_68, c_4282])).
% 7.56/2.66  tff(c_4329, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4298, c_4242, c_4298, c_4298, c_4242, c_4242, c_4298, c_4262, c_4242, c_4242, c_64])).
% 7.56/2.66  tff(c_4330, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(splitLeft, [status(thm)], [c_4329])).
% 7.56/2.66  tff(c_4380, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4362, c_4362, c_4362, c_4330])).
% 7.56/2.66  tff(c_5903, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5899, c_4380])).
% 7.56/2.66  tff(c_5904, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_4329])).
% 7.56/2.66  tff(c_6069, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5932, c_5932, c_5932, c_5932, c_5932, c_5932, c_5932, c_5932, c_5932, c_5904])).
% 7.56/2.66  tff(c_6070, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_6069])).
% 7.56/2.66  tff(c_6170, plain, (~r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_20, c_6070])).
% 7.56/2.66  tff(c_9029, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9024, c_6170])).
% 7.56/2.66  tff(c_9033, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5945, c_5936, c_9029])).
% 7.56/2.66  tff(c_9035, plain, (m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_6069])).
% 7.56/2.66  tff(c_18, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.56/2.66  tff(c_9067, plain, (r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_9035, c_18])).
% 7.56/2.66  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.56/2.66  tff(c_9077, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4' | ~r1_tarski('#skF_4', k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_9067, c_2])).
% 7.56/2.66  tff(c_9083, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5945, c_9077])).
% 7.56/2.66  tff(c_9034, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_6069])).
% 7.56/2.66  tff(c_9145, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5944, c_9083, c_9034])).
% 7.56/2.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.56/2.66  
% 7.56/2.66  Inference rules
% 7.56/2.66  ----------------------
% 7.56/2.66  #Ref     : 0
% 7.56/2.66  #Sup     : 1959
% 7.56/2.66  #Fact    : 0
% 7.56/2.66  #Define  : 0
% 7.56/2.66  #Split   : 26
% 7.56/2.66  #Chain   : 0
% 7.56/2.66  #Close   : 0
% 7.56/2.66  
% 7.56/2.66  Ordering : KBO
% 7.56/2.66  
% 7.56/2.66  Simplification rules
% 7.56/2.66  ----------------------
% 7.56/2.66  #Subsume      : 226
% 7.56/2.66  #Demod        : 2194
% 7.56/2.66  #Tautology    : 1186
% 7.56/2.66  #SimpNegUnit  : 46
% 7.56/2.66  #BackRed      : 82
% 7.56/2.66  
% 7.56/2.66  #Partial instantiations: 0
% 7.56/2.66  #Strategies tried      : 1
% 7.56/2.66  
% 7.56/2.66  Timing (in seconds)
% 7.56/2.66  ----------------------
% 7.56/2.66  Preprocessing        : 0.34
% 7.56/2.66  Parsing              : 0.18
% 7.90/2.66  CNF conversion       : 0.02
% 7.90/2.66  Main loop            : 1.44
% 7.90/2.66  Inferencing          : 0.51
% 7.90/2.66  Reduction            : 0.49
% 7.90/2.66  Demodulation         : 0.35
% 7.90/2.66  BG Simplification    : 0.05
% 7.90/2.66  Subsumption          : 0.27
% 7.90/2.66  Abstraction          : 0.06
% 7.90/2.67  MUC search           : 0.00
% 7.90/2.67  Cooper               : 0.00
% 7.90/2.67  Total                : 1.84
% 7.90/2.67  Index Insertion      : 0.00
% 7.90/2.67  Index Deletion       : 0.00
% 7.90/2.67  Index Matching       : 0.00
% 7.90/2.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
