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
% DateTime   : Thu Dec  3 10:15:00 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 4.11s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 298 expanded)
%              Number of leaves         :   42 ( 117 expanded)
%              Depth                    :    9
%              Number of atoms          :  192 ( 629 expanded)
%              Number of equality atoms :  102 ( 213 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_132,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_102,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_120,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_72,axiom,(
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

tff(f_94,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_46,plain,(
    ! [A_21,B_22] : v1_relat_1(k2_zfmisc_1(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_268,plain,(
    ! [B_75,A_76] :
      ( v1_relat_1(B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_76))
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_271,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_70,c_268])).

tff(c_274,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_271])).

tff(c_48,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k9_relat_1(B_24,A_23),k2_relat_1(B_24))
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_56,plain,(
    ! [A_25] :
      ( k1_relat_1(A_25) != k1_xboole_0
      | k1_xboole_0 = A_25
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_282,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_274,c_56])).

tff(c_320,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_282])).

tff(c_450,plain,(
    ! [A_108,B_109,C_110,D_111] :
      ( k7_relset_1(A_108,B_109,C_110,D_111) = k9_relat_1(C_110,D_111)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_457,plain,(
    ! [D_111] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_111) = k9_relat_1('#skF_4',D_111) ),
    inference(resolution,[status(thm)],[c_70,c_450])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_389,plain,(
    ! [B_98,A_99] :
      ( k1_tarski(k1_funct_1(B_98,A_99)) = k2_relat_1(B_98)
      | k1_tarski(A_99) != k1_relat_1(B_98)
      | ~ v1_funct_1(B_98)
      | ~ v1_relat_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_66,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_401,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_66])).

tff(c_416,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_74,c_401])).

tff(c_474,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_416])).

tff(c_475,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_474])).

tff(c_332,plain,(
    ! [C_84,A_85,B_86] :
      ( v4_relat_1(C_84,A_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_342,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_70,c_332])).

tff(c_10,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_44,plain,(
    ! [B_20,A_19] :
      ( r1_tarski(k1_relat_1(B_20),A_19)
      | ~ v4_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_12,plain,(
    ! [A_5,B_6] : k1_enumset1(A_5,A_5,B_6) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_508,plain,(
    ! [A_120,B_121,C_122,D_123] :
      ( k1_enumset1(A_120,B_121,C_122) = D_123
      | k2_tarski(A_120,C_122) = D_123
      | k2_tarski(B_121,C_122) = D_123
      | k2_tarski(A_120,B_121) = D_123
      | k1_tarski(C_122) = D_123
      | k1_tarski(B_121) = D_123
      | k1_tarski(A_120) = D_123
      | k1_xboole_0 = D_123
      | ~ r1_tarski(D_123,k1_enumset1(A_120,B_121,C_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_530,plain,(
    ! [A_5,B_6,D_123] :
      ( k1_enumset1(A_5,A_5,B_6) = D_123
      | k2_tarski(A_5,B_6) = D_123
      | k2_tarski(A_5,B_6) = D_123
      | k2_tarski(A_5,A_5) = D_123
      | k1_tarski(B_6) = D_123
      | k1_tarski(A_5) = D_123
      | k1_tarski(A_5) = D_123
      | k1_xboole_0 = D_123
      | ~ r1_tarski(D_123,k2_tarski(A_5,B_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_508])).

tff(c_763,plain,(
    ! [A_179,B_180,D_181] :
      ( k2_tarski(A_179,B_180) = D_181
      | k2_tarski(A_179,B_180) = D_181
      | k2_tarski(A_179,B_180) = D_181
      | k1_tarski(A_179) = D_181
      | k1_tarski(B_180) = D_181
      | k1_tarski(A_179) = D_181
      | k1_tarski(A_179) = D_181
      | k1_xboole_0 = D_181
      | ~ r1_tarski(D_181,k2_tarski(A_179,B_180)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12,c_530])).

tff(c_803,plain,(
    ! [A_182,B_183,B_184] :
      ( k2_tarski(A_182,B_183) = k1_relat_1(B_184)
      | k1_tarski(B_183) = k1_relat_1(B_184)
      | k1_tarski(A_182) = k1_relat_1(B_184)
      | k1_relat_1(B_184) = k1_xboole_0
      | ~ v4_relat_1(B_184,k2_tarski(A_182,B_183))
      | ~ v1_relat_1(B_184) ) ),
    inference(resolution,[status(thm)],[c_44,c_763])).

tff(c_810,plain,(
    ! [A_4,B_184] :
      ( k2_tarski(A_4,A_4) = k1_relat_1(B_184)
      | k1_tarski(A_4) = k1_relat_1(B_184)
      | k1_tarski(A_4) = k1_relat_1(B_184)
      | k1_relat_1(B_184) = k1_xboole_0
      | ~ v4_relat_1(B_184,k1_tarski(A_4))
      | ~ v1_relat_1(B_184) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_803])).

tff(c_815,plain,(
    ! [A_185,B_186] :
      ( k1_tarski(A_185) = k1_relat_1(B_186)
      | k1_tarski(A_185) = k1_relat_1(B_186)
      | k1_tarski(A_185) = k1_relat_1(B_186)
      | k1_relat_1(B_186) = k1_xboole_0
      | ~ v4_relat_1(B_186,k1_tarski(A_185))
      | ~ v1_relat_1(B_186) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_810])).

tff(c_821,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_342,c_815])).

tff(c_828,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_821])).

tff(c_830,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_320,c_475,c_828])).

tff(c_832,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_474])).

tff(c_58,plain,(
    ! [B_27,A_26] :
      ( k1_tarski(k1_funct_1(B_27,A_26)) = k2_relat_1(B_27)
      | k1_tarski(A_26) != k1_relat_1(B_27)
      | ~ v1_funct_1(B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_458,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_66])).

tff(c_470,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_458])).

tff(c_472,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_74,c_470])).

tff(c_473,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_472])).

tff(c_861,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_832,c_473])).

tff(c_862,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_472])).

tff(c_945,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_862])).

tff(c_949,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_945])).

tff(c_950,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_282])).

tff(c_50,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_961,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_950,c_950,c_50])).

tff(c_54,plain,(
    ! [A_25] :
      ( k2_relat_1(A_25) != k1_xboole_0
      | k1_xboole_0 = A_25
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_281,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_274,c_54])).

tff(c_310,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_281])).

tff(c_952,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_950,c_310])).

tff(c_990,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_961,c_952])).

tff(c_991,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_281])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1003,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_991,c_8])).

tff(c_18,plain,(
    ! [A_10] : k2_zfmisc_1(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_95,plain,(
    ! [A_38,B_39] : v1_relat_1(k2_zfmisc_1(A_38,B_39)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_97,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_95])).

tff(c_181,plain,(
    ! [B_59,A_60] :
      ( r1_tarski(k9_relat_1(B_59,A_60),k2_relat_1(B_59))
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_184,plain,(
    ! [A_60] :
      ( r1_tarski(k9_relat_1(k1_xboole_0,A_60),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_181])).

tff(c_186,plain,(
    ! [A_60] : r1_tarski(k9_relat_1(k1_xboole_0,A_60),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_184])).

tff(c_226,plain,(
    ! [B_73,A_74] :
      ( B_73 = A_74
      | ~ r1_tarski(B_73,A_74)
      | ~ r1_tarski(A_74,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_234,plain,(
    ! [A_60] :
      ( k9_relat_1(k1_xboole_0,A_60) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k9_relat_1(k1_xboole_0,A_60)) ) ),
    inference(resolution,[status(thm)],[c_186,c_226])).

tff(c_256,plain,(
    ! [A_60] : k9_relat_1(k1_xboole_0,A_60) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_234])).

tff(c_994,plain,(
    ! [A_60] : k9_relat_1('#skF_4',A_60) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_991,c_991,c_256])).

tff(c_1302,plain,(
    ! [A_235,B_236,C_237,D_238] :
      ( k7_relset_1(A_235,B_236,C_237,D_238) = k9_relat_1(C_237,D_238)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(A_235,B_236))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1308,plain,(
    ! [D_238] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_238) = k9_relat_1('#skF_4',D_238) ),
    inference(resolution,[status(thm)],[c_70,c_1302])).

tff(c_1310,plain,(
    ! [D_238] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_238) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_994,c_1308])).

tff(c_1311,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1310,c_66])).

tff(c_1314,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1003,c_1311])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:26:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.85/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.72  
% 3.85/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.72  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.85/1.72  
% 3.85/1.72  %Foreground sorts:
% 3.85/1.72  
% 3.85/1.72  
% 3.85/1.72  %Background operators:
% 3.85/1.72  
% 3.85/1.72  
% 3.85/1.72  %Foreground operators:
% 3.85/1.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.85/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.85/1.72  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.85/1.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.85/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.85/1.72  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.85/1.72  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.85/1.72  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.85/1.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.85/1.72  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.85/1.72  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.85/1.72  tff('#skF_2', type, '#skF_2': $i).
% 3.85/1.72  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.85/1.72  tff('#skF_3', type, '#skF_3': $i).
% 3.85/1.72  tff('#skF_1', type, '#skF_1': $i).
% 3.85/1.72  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.85/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.85/1.72  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.85/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.85/1.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.85/1.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.85/1.72  tff('#skF_4', type, '#skF_4': $i).
% 3.85/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.85/1.72  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.85/1.72  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.85/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.85/1.72  
% 4.11/1.75  tff(f_87, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.11/1.75  tff(f_132, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_2)).
% 4.11/1.75  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.11/1.75  tff(f_91, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_relat_1)).
% 4.11/1.75  tff(f_102, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 4.11/1.75  tff(f_120, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.11/1.75  tff(f_110, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 4.11/1.75  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.11/1.75  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.11/1.75  tff(f_85, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 4.11/1.75  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.11/1.75  tff(f_72, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 4.11/1.75  tff(f_94, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 4.11/1.75  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.11/1.75  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.11/1.75  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.11/1.75  tff(c_46, plain, (![A_21, B_22]: (v1_relat_1(k2_zfmisc_1(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.11/1.75  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.11/1.75  tff(c_268, plain, (![B_75, A_76]: (v1_relat_1(B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(A_76)) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.11/1.75  tff(c_271, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_70, c_268])).
% 4.11/1.75  tff(c_274, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_271])).
% 4.11/1.75  tff(c_48, plain, (![B_24, A_23]: (r1_tarski(k9_relat_1(B_24, A_23), k2_relat_1(B_24)) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.11/1.75  tff(c_56, plain, (![A_25]: (k1_relat_1(A_25)!=k1_xboole_0 | k1_xboole_0=A_25 | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.11/1.75  tff(c_282, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_274, c_56])).
% 4.11/1.75  tff(c_320, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_282])).
% 4.11/1.75  tff(c_450, plain, (![A_108, B_109, C_110, D_111]: (k7_relset_1(A_108, B_109, C_110, D_111)=k9_relat_1(C_110, D_111) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.11/1.75  tff(c_457, plain, (![D_111]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_111)=k9_relat_1('#skF_4', D_111))), inference(resolution, [status(thm)], [c_70, c_450])).
% 4.11/1.75  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.11/1.75  tff(c_389, plain, (![B_98, A_99]: (k1_tarski(k1_funct_1(B_98, A_99))=k2_relat_1(B_98) | k1_tarski(A_99)!=k1_relat_1(B_98) | ~v1_funct_1(B_98) | ~v1_relat_1(B_98))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.11/1.75  tff(c_66, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.11/1.75  tff(c_401, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_389, c_66])).
% 4.11/1.75  tff(c_416, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_274, c_74, c_401])).
% 4.11/1.75  tff(c_474, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_457, c_416])).
% 4.11/1.75  tff(c_475, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_474])).
% 4.11/1.75  tff(c_332, plain, (![C_84, A_85, B_86]: (v4_relat_1(C_84, A_85) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.11/1.75  tff(c_342, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_70, c_332])).
% 4.11/1.75  tff(c_10, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.11/1.75  tff(c_44, plain, (![B_20, A_19]: (r1_tarski(k1_relat_1(B_20), A_19) | ~v4_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.11/1.75  tff(c_12, plain, (![A_5, B_6]: (k1_enumset1(A_5, A_5, B_6)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.11/1.75  tff(c_508, plain, (![A_120, B_121, C_122, D_123]: (k1_enumset1(A_120, B_121, C_122)=D_123 | k2_tarski(A_120, C_122)=D_123 | k2_tarski(B_121, C_122)=D_123 | k2_tarski(A_120, B_121)=D_123 | k1_tarski(C_122)=D_123 | k1_tarski(B_121)=D_123 | k1_tarski(A_120)=D_123 | k1_xboole_0=D_123 | ~r1_tarski(D_123, k1_enumset1(A_120, B_121, C_122)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.11/1.75  tff(c_530, plain, (![A_5, B_6, D_123]: (k1_enumset1(A_5, A_5, B_6)=D_123 | k2_tarski(A_5, B_6)=D_123 | k2_tarski(A_5, B_6)=D_123 | k2_tarski(A_5, A_5)=D_123 | k1_tarski(B_6)=D_123 | k1_tarski(A_5)=D_123 | k1_tarski(A_5)=D_123 | k1_xboole_0=D_123 | ~r1_tarski(D_123, k2_tarski(A_5, B_6)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_508])).
% 4.11/1.75  tff(c_763, plain, (![A_179, B_180, D_181]: (k2_tarski(A_179, B_180)=D_181 | k2_tarski(A_179, B_180)=D_181 | k2_tarski(A_179, B_180)=D_181 | k1_tarski(A_179)=D_181 | k1_tarski(B_180)=D_181 | k1_tarski(A_179)=D_181 | k1_tarski(A_179)=D_181 | k1_xboole_0=D_181 | ~r1_tarski(D_181, k2_tarski(A_179, B_180)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12, c_530])).
% 4.11/1.75  tff(c_803, plain, (![A_182, B_183, B_184]: (k2_tarski(A_182, B_183)=k1_relat_1(B_184) | k1_tarski(B_183)=k1_relat_1(B_184) | k1_tarski(A_182)=k1_relat_1(B_184) | k1_relat_1(B_184)=k1_xboole_0 | ~v4_relat_1(B_184, k2_tarski(A_182, B_183)) | ~v1_relat_1(B_184))), inference(resolution, [status(thm)], [c_44, c_763])).
% 4.11/1.75  tff(c_810, plain, (![A_4, B_184]: (k2_tarski(A_4, A_4)=k1_relat_1(B_184) | k1_tarski(A_4)=k1_relat_1(B_184) | k1_tarski(A_4)=k1_relat_1(B_184) | k1_relat_1(B_184)=k1_xboole_0 | ~v4_relat_1(B_184, k1_tarski(A_4)) | ~v1_relat_1(B_184))), inference(superposition, [status(thm), theory('equality')], [c_10, c_803])).
% 4.11/1.75  tff(c_815, plain, (![A_185, B_186]: (k1_tarski(A_185)=k1_relat_1(B_186) | k1_tarski(A_185)=k1_relat_1(B_186) | k1_tarski(A_185)=k1_relat_1(B_186) | k1_relat_1(B_186)=k1_xboole_0 | ~v4_relat_1(B_186, k1_tarski(A_185)) | ~v1_relat_1(B_186))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_810])).
% 4.11/1.75  tff(c_821, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_342, c_815])).
% 4.11/1.75  tff(c_828, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_274, c_821])).
% 4.11/1.75  tff(c_830, plain, $false, inference(negUnitSimplification, [status(thm)], [c_320, c_475, c_828])).
% 4.11/1.75  tff(c_832, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_474])).
% 4.11/1.75  tff(c_58, plain, (![B_27, A_26]: (k1_tarski(k1_funct_1(B_27, A_26))=k2_relat_1(B_27) | k1_tarski(A_26)!=k1_relat_1(B_27) | ~v1_funct_1(B_27) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.11/1.75  tff(c_458, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_457, c_66])).
% 4.11/1.75  tff(c_470, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_58, c_458])).
% 4.11/1.75  tff(c_472, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_274, c_74, c_470])).
% 4.11/1.75  tff(c_473, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_472])).
% 4.11/1.75  tff(c_861, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_832, c_473])).
% 4.11/1.75  tff(c_862, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_472])).
% 4.11/1.75  tff(c_945, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_862])).
% 4.11/1.75  tff(c_949, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_274, c_945])).
% 4.11/1.75  tff(c_950, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_282])).
% 4.11/1.75  tff(c_50, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.11/1.75  tff(c_961, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_950, c_950, c_50])).
% 4.11/1.75  tff(c_54, plain, (![A_25]: (k2_relat_1(A_25)!=k1_xboole_0 | k1_xboole_0=A_25 | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.11/1.75  tff(c_281, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_274, c_54])).
% 4.11/1.75  tff(c_310, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_281])).
% 4.11/1.75  tff(c_952, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_950, c_310])).
% 4.11/1.75  tff(c_990, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_961, c_952])).
% 4.11/1.75  tff(c_991, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_281])).
% 4.11/1.75  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.11/1.75  tff(c_1003, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_991, c_8])).
% 4.11/1.75  tff(c_18, plain, (![A_10]: (k2_zfmisc_1(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.11/1.75  tff(c_95, plain, (![A_38, B_39]: (v1_relat_1(k2_zfmisc_1(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.11/1.75  tff(c_97, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_95])).
% 4.11/1.75  tff(c_181, plain, (![B_59, A_60]: (r1_tarski(k9_relat_1(B_59, A_60), k2_relat_1(B_59)) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.11/1.75  tff(c_184, plain, (![A_60]: (r1_tarski(k9_relat_1(k1_xboole_0, A_60), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_50, c_181])).
% 4.11/1.75  tff(c_186, plain, (![A_60]: (r1_tarski(k9_relat_1(k1_xboole_0, A_60), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_184])).
% 4.11/1.75  tff(c_226, plain, (![B_73, A_74]: (B_73=A_74 | ~r1_tarski(B_73, A_74) | ~r1_tarski(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.11/1.75  tff(c_234, plain, (![A_60]: (k9_relat_1(k1_xboole_0, A_60)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k9_relat_1(k1_xboole_0, A_60)))), inference(resolution, [status(thm)], [c_186, c_226])).
% 4.11/1.75  tff(c_256, plain, (![A_60]: (k9_relat_1(k1_xboole_0, A_60)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_234])).
% 4.11/1.75  tff(c_994, plain, (![A_60]: (k9_relat_1('#skF_4', A_60)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_991, c_991, c_256])).
% 4.11/1.75  tff(c_1302, plain, (![A_235, B_236, C_237, D_238]: (k7_relset_1(A_235, B_236, C_237, D_238)=k9_relat_1(C_237, D_238) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(A_235, B_236))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.11/1.75  tff(c_1308, plain, (![D_238]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_238)=k9_relat_1('#skF_4', D_238))), inference(resolution, [status(thm)], [c_70, c_1302])).
% 4.11/1.75  tff(c_1310, plain, (![D_238]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_238)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_994, c_1308])).
% 4.11/1.75  tff(c_1311, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1310, c_66])).
% 4.11/1.75  tff(c_1314, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1003, c_1311])).
% 4.11/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.11/1.75  
% 4.11/1.75  Inference rules
% 4.11/1.75  ----------------------
% 4.11/1.75  #Ref     : 0
% 4.11/1.75  #Sup     : 266
% 4.11/1.75  #Fact    : 0
% 4.11/1.75  #Define  : 0
% 4.11/1.75  #Split   : 5
% 4.11/1.75  #Chain   : 0
% 4.11/1.75  #Close   : 0
% 4.11/1.75  
% 4.11/1.75  Ordering : KBO
% 4.11/1.75  
% 4.11/1.75  Simplification rules
% 4.11/1.75  ----------------------
% 4.11/1.75  #Subsume      : 37
% 4.11/1.75  #Demod        : 251
% 4.11/1.75  #Tautology    : 145
% 4.11/1.75  #SimpNegUnit  : 1
% 4.11/1.75  #BackRed      : 36
% 4.11/1.75  
% 4.11/1.75  #Partial instantiations: 0
% 4.11/1.75  #Strategies tried      : 1
% 4.11/1.75  
% 4.11/1.75  Timing (in seconds)
% 4.11/1.75  ----------------------
% 4.11/1.75  Preprocessing        : 0.36
% 4.11/1.75  Parsing              : 0.19
% 4.11/1.75  CNF conversion       : 0.02
% 4.11/1.75  Main loop            : 0.56
% 4.11/1.75  Inferencing          : 0.19
% 4.11/1.75  Reduction            : 0.19
% 4.11/1.76  Demodulation         : 0.14
% 4.11/1.76  BG Simplification    : 0.03
% 4.11/1.76  Subsumption          : 0.11
% 4.21/1.76  Abstraction          : 0.03
% 4.21/1.76  MUC search           : 0.00
% 4.21/1.76  Cooper               : 0.00
% 4.21/1.76  Total                : 0.97
% 4.21/1.76  Index Insertion      : 0.00
% 4.21/1.76  Index Deletion       : 0.00
% 4.21/1.76  Index Matching       : 0.00
% 4.21/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
