%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:44 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :  101 (2254 expanded)
%              Number of leaves         :   28 ( 823 expanded)
%              Depth                    :   13
%              Number of atoms          :  140 (7208 expanded)
%              Number of equality atoms :   66 (2443 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_67,axiom,(
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

tff(f_37,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_33,axiom,(
    ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_36,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(c_42,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_428,plain,(
    ! [A_53,B_54,C_55] :
      ( k1_relset_1(A_53,B_54,C_55) = k1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_431,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_428])).

tff(c_439,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_431])).

tff(c_46,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_40,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_48,plain,(
    ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_40])).

tff(c_785,plain,(
    ! [B_79,C_80,A_81] :
      ( k1_xboole_0 = B_79
      | v1_funct_2(C_80,A_81,B_79)
      | k1_relset_1(A_81,B_79,C_80) != A_81
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_794,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2')
    | k1_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_44,c_785])).

tff(c_807,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_794])).

tff(c_808,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_807])).

tff(c_14,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_823,plain,(
    k6_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_808,c_14])).

tff(c_4,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_819,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_808,c_4])).

tff(c_119,plain,(
    ! [A_25,B_26] :
      ( k9_relat_1(k6_relat_1(A_25),B_26) = B_26
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_123,plain,(
    k9_relat_1(k6_relat_1(k2_zfmisc_1('#skF_1','#skF_2')),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_44,c_119])).

tff(c_903,plain,(
    k9_relat_1(k6_relat_1('#skF_2'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_819,c_123])).

tff(c_905,plain,(
    k9_relat_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_823,c_903])).

tff(c_8,plain,(
    ! [A_3] : k9_relat_1(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_820,plain,(
    ! [A_3] : k9_relat_1('#skF_2',A_3) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_808,c_8])).

tff(c_939,plain,(
    '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_905,c_820])).

tff(c_12,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_822,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_808,c_12])).

tff(c_954,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_939,c_939,c_822])).

tff(c_961,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_439,c_954])).

tff(c_960,plain,(
    ~ v1_funct_2('#skF_3','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_939,c_48])).

tff(c_1056,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_961,c_961,c_960])).

tff(c_976,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_961,c_939])).

tff(c_98,plain,(
    ! [C_19,A_20,B_21] :
      ( v1_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_106,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_98])).

tff(c_259,plain,(
    ! [B_44,C_45,A_46] :
      ( k1_xboole_0 = B_44
      | v1_funct_2(C_45,A_46,B_44)
      | k1_relset_1(A_46,B_44,C_45) != A_46
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_46,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_268,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2')
    | k1_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_44,c_259])).

tff(c_281,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_268])).

tff(c_282,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_281])).

tff(c_296,plain,(
    ! [A_3] : k9_relat_1('#skF_2',A_3) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_282,c_8])).

tff(c_299,plain,(
    k6_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_282,c_14])).

tff(c_295,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_282,c_4])).

tff(c_384,plain,(
    k9_relat_1(k6_relat_1('#skF_2'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_123])).

tff(c_386,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_296,c_299,c_384])).

tff(c_10,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_128,plain,(
    ! [A_27] :
      ( v1_funct_2(A_27,k1_relat_1(A_27),k2_relat_1(A_27))
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_131,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_128])).

tff(c_135,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_131])).

tff(c_137,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_291,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_137])).

tff(c_417,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_291])).

tff(c_425,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_417])).

tff(c_427,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_815,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_427])).

tff(c_558,plain,(
    ! [B_69,C_70,A_71] :
      ( k1_xboole_0 = B_69
      | v1_funct_2(C_70,A_71,B_69)
      | k1_relset_1(A_71,B_69,C_70) != A_71
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_567,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2')
    | k1_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_44,c_558])).

tff(c_580,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_567])).

tff(c_581,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_580])).

tff(c_596,plain,(
    ! [A_3] : k9_relat_1('#skF_2',A_3) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_581,c_8])).

tff(c_599,plain,(
    k6_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_581,c_14])).

tff(c_595,plain,(
    ! [A_1] : k2_zfmisc_1(A_1,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_581,c_4])).

tff(c_680,plain,(
    k9_relat_1(k6_relat_1('#skF_2'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_595,c_123])).

tff(c_682,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_596,c_599,c_680])).

tff(c_426,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_449,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_426])).

tff(c_590,plain,(
    ~ v1_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_581,c_449])).

tff(c_705,plain,(
    ~ v1_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_682,c_590])).

tff(c_713,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_705])).

tff(c_715,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_426])).

tff(c_814,plain,(
    v1_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_715])).

tff(c_821,plain,(
    k2_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_808,c_10])).

tff(c_36,plain,(
    ! [A_15] :
      ( v1_funct_2(A_15,k1_relat_1(A_15),k2_relat_1(A_15))
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_848,plain,
    ( v1_funct_2('#skF_2','#skF_2',k2_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_822,c_36])).

tff(c_854,plain,(
    v1_funct_2('#skF_2','#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_815,c_814,c_821,c_848])).

tff(c_1062,plain,(
    v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_976,c_976,c_976,c_854])).

tff(c_1063,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1056,c_1062])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:20:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/1.46  
% 3.01/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/1.46  %$ v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.01/1.46  
% 3.01/1.46  %Foreground sorts:
% 3.01/1.46  
% 3.01/1.46  
% 3.01/1.46  %Background operators:
% 3.01/1.46  
% 3.01/1.46  
% 3.01/1.46  %Foreground operators:
% 3.01/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.01/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.01/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.01/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.01/1.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.01/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.01/1.46  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.01/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.01/1.46  tff('#skF_1', type, '#skF_1': $i).
% 3.01/1.46  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.01/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.01/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.01/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.01/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.01/1.46  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.01/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.01/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.01/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.01/1.46  
% 3.01/1.48  tff(f_90, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_funct_2)).
% 3.01/1.48  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.01/1.48  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.01/1.48  tff(f_37, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 3.01/1.48  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.01/1.48  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_funct_1)).
% 3.01/1.48  tff(f_33, axiom, (![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 3.01/1.48  tff(f_36, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.01/1.48  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.01/1.48  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 3.01/1.48  tff(c_42, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.01/1.48  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.01/1.48  tff(c_428, plain, (![A_53, B_54, C_55]: (k1_relset_1(A_53, B_54, C_55)=k1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.01/1.48  tff(c_431, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_428])).
% 3.01/1.48  tff(c_439, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_431])).
% 3.01/1.48  tff(c_46, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.01/1.48  tff(c_40, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.01/1.48  tff(c_48, plain, (~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_40])).
% 3.01/1.48  tff(c_785, plain, (![B_79, C_80, A_81]: (k1_xboole_0=B_79 | v1_funct_2(C_80, A_81, B_79) | k1_relset_1(A_81, B_79, C_80)!=A_81 | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_79))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.01/1.48  tff(c_794, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_44, c_785])).
% 3.01/1.48  tff(c_807, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_794])).
% 3.01/1.48  tff(c_808, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_48, c_807])).
% 3.01/1.48  tff(c_14, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.01/1.48  tff(c_823, plain, (k6_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_808, c_808, c_14])).
% 3.01/1.48  tff(c_4, plain, (![A_1]: (k2_zfmisc_1(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.01/1.48  tff(c_819, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_808, c_808, c_4])).
% 3.01/1.48  tff(c_119, plain, (![A_25, B_26]: (k9_relat_1(k6_relat_1(A_25), B_26)=B_26 | ~m1_subset_1(B_26, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.01/1.48  tff(c_123, plain, (k9_relat_1(k6_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_44, c_119])).
% 3.01/1.48  tff(c_903, plain, (k9_relat_1(k6_relat_1('#skF_2'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_819, c_123])).
% 3.01/1.48  tff(c_905, plain, (k9_relat_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_823, c_903])).
% 3.01/1.48  tff(c_8, plain, (![A_3]: (k9_relat_1(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.01/1.48  tff(c_820, plain, (![A_3]: (k9_relat_1('#skF_2', A_3)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_808, c_808, c_8])).
% 3.01/1.48  tff(c_939, plain, ('#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_905, c_820])).
% 3.01/1.48  tff(c_12, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.01/1.48  tff(c_822, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_808, c_808, c_12])).
% 3.01/1.48  tff(c_954, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_939, c_939, c_822])).
% 3.01/1.48  tff(c_961, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_439, c_954])).
% 3.01/1.48  tff(c_960, plain, (~v1_funct_2('#skF_3', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_939, c_48])).
% 3.01/1.48  tff(c_1056, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_961, c_961, c_960])).
% 3.01/1.48  tff(c_976, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_961, c_939])).
% 3.01/1.48  tff(c_98, plain, (![C_19, A_20, B_21]: (v1_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.01/1.48  tff(c_106, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_98])).
% 3.01/1.48  tff(c_259, plain, (![B_44, C_45, A_46]: (k1_xboole_0=B_44 | v1_funct_2(C_45, A_46, B_44) | k1_relset_1(A_46, B_44, C_45)!=A_46 | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_46, B_44))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.01/1.48  tff(c_268, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_44, c_259])).
% 3.01/1.48  tff(c_281, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_268])).
% 3.01/1.48  tff(c_282, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_48, c_281])).
% 3.01/1.48  tff(c_296, plain, (![A_3]: (k9_relat_1('#skF_2', A_3)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_282, c_282, c_8])).
% 3.01/1.48  tff(c_299, plain, (k6_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_282, c_282, c_14])).
% 3.01/1.48  tff(c_295, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_282, c_282, c_4])).
% 3.01/1.48  tff(c_384, plain, (k9_relat_1(k6_relat_1('#skF_2'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_295, c_123])).
% 3.01/1.48  tff(c_386, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_296, c_299, c_384])).
% 3.01/1.48  tff(c_10, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.01/1.48  tff(c_128, plain, (![A_27]: (v1_funct_2(A_27, k1_relat_1(A_27), k2_relat_1(A_27)) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.01/1.48  tff(c_131, plain, (v1_funct_2(k1_xboole_0, k1_relat_1(k1_xboole_0), k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_128])).
% 3.01/1.48  tff(c_135, plain, (v1_funct_2(k1_xboole_0, k1_xboole_0, k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_131])).
% 3.01/1.48  tff(c_137, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_135])).
% 3.01/1.48  tff(c_291, plain, (~v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_282, c_137])).
% 3.01/1.48  tff(c_417, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_386, c_291])).
% 3.01/1.48  tff(c_425, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_417])).
% 3.01/1.48  tff(c_427, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_135])).
% 3.01/1.48  tff(c_815, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_808, c_427])).
% 3.01/1.48  tff(c_558, plain, (![B_69, C_70, A_71]: (k1_xboole_0=B_69 | v1_funct_2(C_70, A_71, B_69) | k1_relset_1(A_71, B_69, C_70)!=A_71 | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_69))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.01/1.48  tff(c_567, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_44, c_558])).
% 3.01/1.48  tff(c_580, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_567])).
% 3.01/1.48  tff(c_581, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_48, c_580])).
% 3.01/1.48  tff(c_596, plain, (![A_3]: (k9_relat_1('#skF_2', A_3)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_581, c_581, c_8])).
% 3.01/1.48  tff(c_599, plain, (k6_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_581, c_581, c_14])).
% 3.01/1.48  tff(c_595, plain, (![A_1]: (k2_zfmisc_1(A_1, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_581, c_581, c_4])).
% 3.01/1.48  tff(c_680, plain, (k9_relat_1(k6_relat_1('#skF_2'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_595, c_123])).
% 3.01/1.48  tff(c_682, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_596, c_599, c_680])).
% 3.01/1.48  tff(c_426, plain, (~v1_funct_1(k1_xboole_0) | v1_funct_2(k1_xboole_0, k1_xboole_0, k1_xboole_0)), inference(splitRight, [status(thm)], [c_135])).
% 3.01/1.48  tff(c_449, plain, (~v1_funct_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_426])).
% 3.01/1.48  tff(c_590, plain, (~v1_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_581, c_449])).
% 3.01/1.48  tff(c_705, plain, (~v1_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_682, c_590])).
% 3.01/1.48  tff(c_713, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_705])).
% 3.01/1.48  tff(c_715, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_426])).
% 3.01/1.48  tff(c_814, plain, (v1_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_808, c_715])).
% 3.01/1.48  tff(c_821, plain, (k2_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_808, c_808, c_10])).
% 3.01/1.48  tff(c_36, plain, (![A_15]: (v1_funct_2(A_15, k1_relat_1(A_15), k2_relat_1(A_15)) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.01/1.48  tff(c_848, plain, (v1_funct_2('#skF_2', '#skF_2', k2_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_822, c_36])).
% 3.01/1.48  tff(c_854, plain, (v1_funct_2('#skF_2', '#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_815, c_814, c_821, c_848])).
% 3.01/1.48  tff(c_1062, plain, (v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_976, c_976, c_976, c_854])).
% 3.01/1.48  tff(c_1063, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1056, c_1062])).
% 3.01/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/1.48  
% 3.01/1.48  Inference rules
% 3.01/1.48  ----------------------
% 3.01/1.48  #Ref     : 0
% 3.01/1.48  #Sup     : 237
% 3.01/1.48  #Fact    : 0
% 3.01/1.48  #Define  : 0
% 3.01/1.48  #Split   : 4
% 3.01/1.48  #Chain   : 0
% 3.01/1.48  #Close   : 0
% 3.01/1.48  
% 3.01/1.48  Ordering : KBO
% 3.01/1.48  
% 3.01/1.48  Simplification rules
% 3.01/1.48  ----------------------
% 3.01/1.48  #Subsume      : 41
% 3.01/1.48  #Demod        : 375
% 3.01/1.48  #Tautology    : 143
% 3.01/1.48  #SimpNegUnit  : 8
% 3.01/1.48  #BackRed      : 101
% 3.01/1.48  
% 3.01/1.48  #Partial instantiations: 0
% 3.01/1.48  #Strategies tried      : 1
% 3.01/1.48  
% 3.01/1.48  Timing (in seconds)
% 3.01/1.48  ----------------------
% 3.01/1.48  Preprocessing        : 0.31
% 3.01/1.48  Parsing              : 0.16
% 3.01/1.48  CNF conversion       : 0.02
% 3.01/1.48  Main loop            : 0.40
% 3.01/1.48  Inferencing          : 0.13
% 3.01/1.48  Reduction            : 0.14
% 3.01/1.48  Demodulation         : 0.10
% 3.01/1.48  BG Simplification    : 0.02
% 3.16/1.48  Subsumption          : 0.06
% 3.16/1.48  Abstraction          : 0.02
% 3.16/1.48  MUC search           : 0.00
% 3.16/1.48  Cooper               : 0.00
% 3.16/1.48  Total                : 0.75
% 3.16/1.48  Index Insertion      : 0.00
% 3.16/1.48  Index Deletion       : 0.00
% 3.16/1.48  Index Matching       : 0.00
% 3.16/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
