%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:54 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 380 expanded)
%              Number of leaves         :   44 ( 151 expanded)
%              Depth                    :   17
%              Number of atoms          :  131 ( 877 expanded)
%              Number of equality atoms :   52 ( 326 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_137,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_125,axiom,(
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

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(D,k1_enumset1(A,B,C))
    <=> ~ ( D != k1_xboole_0
          & D != k1_tarski(A)
          & D != k1_tarski(B)
          & D != k1_tarski(C)
          & D != k2_tarski(A,B)
          & D != k2_tarski(B,C)
          & D != k2_tarski(A,C)
          & D != k1_enumset1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => k11_relat_1(B,A) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

tff(f_107,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_211,plain,(
    ! [C_93,A_94,B_95] :
      ( v1_relat_1(C_93)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_215,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_211])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_68,plain,(
    v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_269,plain,(
    ! [A_114,B_115,C_116] :
      ( k1_relset_1(A_114,B_115,C_116) = k1_relat_1(C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_273,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_269])).

tff(c_312,plain,(
    ! [B_137,A_138,C_139] :
      ( k1_xboole_0 = B_137
      | k1_relset_1(A_138,B_137,C_139) = A_138
      | ~ v1_funct_2(C_139,A_138,B_137)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_138,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_315,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_4',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_312])).

tff(c_318,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_273,c_315])).

tff(c_319,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_318])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_96,plain,(
    ! [A_48,B_49,C_50] : r1_tarski(k1_tarski(A_48),k1_enumset1(A_48,B_49,C_50)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_100,plain,(
    ! [A_51,B_52] : r1_tarski(k1_tarski(A_51),k2_tarski(A_51,B_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_96])).

tff(c_103,plain,(
    ! [A_1] : r1_tarski(k1_tarski(A_1),k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_100])).

tff(c_351,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_relat_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_103])).

tff(c_363,plain,(
    r1_tarski(k1_relat_1('#skF_4'),k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_351])).

tff(c_32,plain,(
    ! [B_17,A_16] :
      ( v4_relat_1(B_17,A_16)
      | ~ r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_428,plain,
    ( v4_relat_1('#skF_4',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_363,c_32])).

tff(c_431,plain,(
    v4_relat_1('#skF_4',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_428])).

tff(c_40,plain,(
    ! [B_23,A_22] :
      ( k7_relat_1(B_23,A_22) = B_23
      | ~ v4_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_434,plain,
    ( k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_431,c_40])).

tff(c_437,plain,(
    k7_relat_1('#skF_4',k1_relat_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_434])).

tff(c_38,plain,(
    ! [B_21,A_20] :
      ( k2_relat_1(k7_relat_1(B_21,A_20)) = k9_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_470,plain,
    ( k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_38])).

tff(c_476,plain,(
    k9_relat_1('#skF_4',k1_relat_1('#skF_4')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_470])).

tff(c_222,plain,(
    ! [B_100,A_101] :
      ( k2_relat_1(k7_relat_1(B_100,A_101)) = k9_relat_1(B_100,A_101)
      | ~ v1_relat_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_36,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k9_relat_1(B_19,A_18),k2_relat_1(B_19))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_228,plain,(
    ! [B_100,A_101,A_18] :
      ( r1_tarski(k9_relat_1(k7_relat_1(B_100,A_101),A_18),k9_relat_1(B_100,A_101))
      | ~ v1_relat_1(k7_relat_1(B_100,A_101))
      | ~ v1_relat_1(B_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_36])).

tff(c_586,plain,(
    ! [A_18] :
      ( r1_tarski(k9_relat_1(k7_relat_1('#skF_4',k1_relat_1('#skF_4')),A_18),k2_relat_1('#skF_4'))
      | ~ v1_relat_1(k7_relat_1('#skF_4',k1_relat_1('#skF_4')))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_476,c_228])).

tff(c_593,plain,(
    ! [A_18] : r1_tarski(k9_relat_1('#skF_4',A_18),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_215,c_437,c_437,c_586])).

tff(c_30,plain,(
    ! [A_13,B_15] :
      ( k9_relat_1(A_13,k1_tarski(B_15)) = k11_relat_1(A_13,B_15)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_903,plain,(
    ! [A_176] :
      ( k9_relat_1(A_176,k1_relat_1('#skF_4')) = k11_relat_1(A_176,'#skF_1')
      | ~ v1_relat_1(A_176) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_30])).

tff(c_913,plain,
    ( k11_relat_1('#skF_4','#skF_1') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_903,c_476])).

tff(c_934,plain,(
    k11_relat_1('#skF_4','#skF_1') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_913])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_115,plain,(
    ! [A_61,B_62] :
      ( r2_hidden(A_61,B_62)
      | ~ r1_tarski(k1_tarski(A_61),B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_137,plain,(
    ! [A_1] : r2_hidden(A_1,k1_tarski(A_1)) ),
    inference(resolution,[status(thm)],[c_103,c_115])).

tff(c_333,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_137])).

tff(c_42,plain,(
    ! [B_25,A_24] :
      ( k1_tarski(k1_funct_1(B_25,A_24)) = k11_relat_1(B_25,A_24)
      | ~ r2_hidden(A_24,k1_relat_1(B_25))
      | ~ v1_funct_1(B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_367,plain,
    ( k1_tarski(k1_funct_1('#skF_4','#skF_1')) = k11_relat_1('#skF_4','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_333,c_42])).

tff(c_370,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_1')) = k11_relat_1('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_70,c_367])).

tff(c_1031,plain,(
    k1_tarski(k1_funct_1('#skF_4','#skF_1')) = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_934,c_370])).

tff(c_279,plain,(
    ! [A_118,B_119,C_120,D_121] :
      ( k7_relset_1(A_118,B_119,C_120,D_121) = k9_relat_1(C_120,D_121)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_282,plain,(
    ! [D_121] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_121) = k9_relat_1('#skF_4',D_121) ),
    inference(resolution,[status(thm)],[c_66,c_279])).

tff(c_62,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_283,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_62])).

tff(c_1032,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1031,c_283])).

tff(c_1035,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_1032])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:12:05 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.14/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.51  
% 3.14/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.51  %$ v1_funct_2 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > k11_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.14/1.51  
% 3.14/1.51  %Foreground sorts:
% 3.14/1.51  
% 3.14/1.51  
% 3.14/1.51  %Background operators:
% 3.14/1.51  
% 3.14/1.51  
% 3.14/1.51  %Foreground operators:
% 3.14/1.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.14/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.14/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.14/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.14/1.51  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.14/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.14/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.14/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.14/1.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.14/1.51  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.14/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.14/1.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.14/1.51  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 3.14/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.14/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.14/1.51  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.14/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.14/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.14/1.51  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.14/1.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.14/1.51  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.14/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.14/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.14/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.14/1.51  tff('#skF_4', type, '#skF_4': $i).
% 3.14/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.14/1.51  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.14/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.14/1.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.14/1.51  
% 3.39/1.53  tff(f_137, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 3.39/1.53  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.39/1.53  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.39/1.53  tff(f_125, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.39/1.53  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.39/1.53  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.39/1.53  tff(f_62, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 3.39/1.53  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.39/1.53  tff(f_87, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.39/1.53  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 3.39/1.53  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 3.39/1.53  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 3.39/1.53  tff(f_35, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.39/1.53  tff(f_95, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => (k11_relat_1(B, A) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_funct_1)).
% 3.39/1.53  tff(f_107, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.39/1.53  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.39/1.53  tff(c_211, plain, (![C_93, A_94, B_95]: (v1_relat_1(C_93) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.39/1.53  tff(c_215, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_211])).
% 3.39/1.53  tff(c_64, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.39/1.53  tff(c_68, plain, (v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.39/1.53  tff(c_269, plain, (![A_114, B_115, C_116]: (k1_relset_1(A_114, B_115, C_116)=k1_relat_1(C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.39/1.53  tff(c_273, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_269])).
% 3.39/1.53  tff(c_312, plain, (![B_137, A_138, C_139]: (k1_xboole_0=B_137 | k1_relset_1(A_138, B_137, C_139)=A_138 | ~v1_funct_2(C_139, A_138, B_137) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_138, B_137))))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.39/1.53  tff(c_315, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_4', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_66, c_312])).
% 3.39/1.53  tff(c_318, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_273, c_315])).
% 3.39/1.53  tff(c_319, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_64, c_318])).
% 3.39/1.53  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.39/1.53  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.39/1.53  tff(c_96, plain, (![A_48, B_49, C_50]: (r1_tarski(k1_tarski(A_48), k1_enumset1(A_48, B_49, C_50)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.39/1.53  tff(c_100, plain, (![A_51, B_52]: (r1_tarski(k1_tarski(A_51), k2_tarski(A_51, B_52)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_96])).
% 3.39/1.53  tff(c_103, plain, (![A_1]: (r1_tarski(k1_tarski(A_1), k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_100])).
% 3.39/1.53  tff(c_351, plain, (r1_tarski(k1_tarski('#skF_1'), k1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_319, c_103])).
% 3.39/1.53  tff(c_363, plain, (r1_tarski(k1_relat_1('#skF_4'), k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_319, c_351])).
% 3.39/1.53  tff(c_32, plain, (![B_17, A_16]: (v4_relat_1(B_17, A_16) | ~r1_tarski(k1_relat_1(B_17), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.39/1.53  tff(c_428, plain, (v4_relat_1('#skF_4', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_363, c_32])).
% 3.39/1.53  tff(c_431, plain, (v4_relat_1('#skF_4', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_428])).
% 3.39/1.53  tff(c_40, plain, (![B_23, A_22]: (k7_relat_1(B_23, A_22)=B_23 | ~v4_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.39/1.53  tff(c_434, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_431, c_40])).
% 3.39/1.53  tff(c_437, plain, (k7_relat_1('#skF_4', k1_relat_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_215, c_434])).
% 3.39/1.53  tff(c_38, plain, (![B_21, A_20]: (k2_relat_1(k7_relat_1(B_21, A_20))=k9_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.39/1.53  tff(c_470, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_437, c_38])).
% 3.39/1.53  tff(c_476, plain, (k9_relat_1('#skF_4', k1_relat_1('#skF_4'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_215, c_470])).
% 3.39/1.53  tff(c_222, plain, (![B_100, A_101]: (k2_relat_1(k7_relat_1(B_100, A_101))=k9_relat_1(B_100, A_101) | ~v1_relat_1(B_100))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.39/1.53  tff(c_36, plain, (![B_19, A_18]: (r1_tarski(k9_relat_1(B_19, A_18), k2_relat_1(B_19)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.39/1.53  tff(c_228, plain, (![B_100, A_101, A_18]: (r1_tarski(k9_relat_1(k7_relat_1(B_100, A_101), A_18), k9_relat_1(B_100, A_101)) | ~v1_relat_1(k7_relat_1(B_100, A_101)) | ~v1_relat_1(B_100))), inference(superposition, [status(thm), theory('equality')], [c_222, c_36])).
% 3.39/1.53  tff(c_586, plain, (![A_18]: (r1_tarski(k9_relat_1(k7_relat_1('#skF_4', k1_relat_1('#skF_4')), A_18), k2_relat_1('#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_4', k1_relat_1('#skF_4'))) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_476, c_228])).
% 3.39/1.53  tff(c_593, plain, (![A_18]: (r1_tarski(k9_relat_1('#skF_4', A_18), k2_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_215, c_437, c_437, c_586])).
% 3.39/1.53  tff(c_30, plain, (![A_13, B_15]: (k9_relat_1(A_13, k1_tarski(B_15))=k11_relat_1(A_13, B_15) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.39/1.53  tff(c_903, plain, (![A_176]: (k9_relat_1(A_176, k1_relat_1('#skF_4'))=k11_relat_1(A_176, '#skF_1') | ~v1_relat_1(A_176))), inference(superposition, [status(thm), theory('equality')], [c_319, c_30])).
% 3.39/1.53  tff(c_913, plain, (k11_relat_1('#skF_4', '#skF_1')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_903, c_476])).
% 3.39/1.53  tff(c_934, plain, (k11_relat_1('#skF_4', '#skF_1')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_215, c_913])).
% 3.39/1.53  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.39/1.53  tff(c_115, plain, (![A_61, B_62]: (r2_hidden(A_61, B_62) | ~r1_tarski(k1_tarski(A_61), B_62))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.39/1.53  tff(c_137, plain, (![A_1]: (r2_hidden(A_1, k1_tarski(A_1)))), inference(resolution, [status(thm)], [c_103, c_115])).
% 3.39/1.53  tff(c_333, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_319, c_137])).
% 3.39/1.53  tff(c_42, plain, (![B_25, A_24]: (k1_tarski(k1_funct_1(B_25, A_24))=k11_relat_1(B_25, A_24) | ~r2_hidden(A_24, k1_relat_1(B_25)) | ~v1_funct_1(B_25) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.39/1.53  tff(c_367, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_1'))=k11_relat_1('#skF_4', '#skF_1') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_333, c_42])).
% 3.39/1.53  tff(c_370, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_1'))=k11_relat_1('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_215, c_70, c_367])).
% 3.39/1.53  tff(c_1031, plain, (k1_tarski(k1_funct_1('#skF_4', '#skF_1'))=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_934, c_370])).
% 3.39/1.53  tff(c_279, plain, (![A_118, B_119, C_120, D_121]: (k7_relset_1(A_118, B_119, C_120, D_121)=k9_relat_1(C_120, D_121) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.39/1.53  tff(c_282, plain, (![D_121]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_121)=k9_relat_1('#skF_4', D_121))), inference(resolution, [status(thm)], [c_66, c_279])).
% 3.39/1.53  tff(c_62, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.39/1.53  tff(c_283, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_282, c_62])).
% 3.39/1.53  tff(c_1032, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1031, c_283])).
% 3.39/1.53  tff(c_1035, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_593, c_1032])).
% 3.39/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.53  
% 3.39/1.53  Inference rules
% 3.39/1.53  ----------------------
% 3.39/1.53  #Ref     : 0
% 3.39/1.53  #Sup     : 204
% 3.39/1.53  #Fact    : 0
% 3.39/1.53  #Define  : 0
% 3.39/1.53  #Split   : 0
% 3.39/1.53  #Chain   : 0
% 3.39/1.53  #Close   : 0
% 3.39/1.53  
% 3.39/1.53  Ordering : KBO
% 3.39/1.53  
% 3.39/1.53  Simplification rules
% 3.39/1.53  ----------------------
% 3.39/1.53  #Subsume      : 1
% 3.39/1.53  #Demod        : 150
% 3.39/1.53  #Tautology    : 128
% 3.39/1.53  #SimpNegUnit  : 4
% 3.39/1.53  #BackRed      : 6
% 3.39/1.53  
% 3.39/1.53  #Partial instantiations: 0
% 3.39/1.53  #Strategies tried      : 1
% 3.39/1.53  
% 3.39/1.53  Timing (in seconds)
% 3.39/1.53  ----------------------
% 3.39/1.53  Preprocessing        : 0.34
% 3.39/1.53  Parsing              : 0.18
% 3.39/1.53  CNF conversion       : 0.02
% 3.39/1.53  Main loop            : 0.41
% 3.39/1.53  Inferencing          : 0.15
% 3.39/1.53  Reduction            : 0.14
% 3.39/1.53  Demodulation         : 0.11
% 3.39/1.54  BG Simplification    : 0.03
% 3.39/1.54  Subsumption          : 0.07
% 3.39/1.54  Abstraction          : 0.02
% 3.39/1.54  MUC search           : 0.00
% 3.39/1.54  Cooper               : 0.00
% 3.39/1.54  Total                : 0.79
% 3.39/1.54  Index Insertion      : 0.00
% 3.39/1.54  Index Deletion       : 0.00
% 3.39/1.54  Index Matching       : 0.00
% 3.39/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
