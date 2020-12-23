%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:47 EST 2020

% Result     : Theorem 13.55s
% Output     : CNFRefutation 13.65s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 492 expanded)
%              Number of leaves         :   44 ( 194 expanded)
%              Depth                    :   14
%              Number of atoms          :  178 (1232 expanded)
%              Number of equality atoms :   86 ( 582 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_141,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_119,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_129,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_74,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_97,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_78,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_193,plain,(
    ! [C_70,A_71,B_72] :
      ( v1_relat_1(C_70)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_210,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_193])).

tff(c_52,plain,(
    ! [B_25,A_24] :
      ( r1_tarski(k9_relat_1(B_25,A_24),k2_relat_1(B_25))
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_82,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [B_11] : k2_zfmisc_1(k1_xboole_0,B_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12157,plain,(
    ! [B_525,A_526] :
      ( k1_tarski(k1_funct_1(B_525,A_526)) = k2_relat_1(B_525)
      | k1_tarski(A_526) != k1_relat_1(B_525)
      | ~ v1_funct_1(B_525)
      | ~ v1_relat_1(B_525) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_12085,plain,(
    ! [A_511,B_512,C_513,D_514] :
      ( k7_relset_1(A_511,B_512,C_513,D_514) = k9_relat_1(C_513,D_514)
      | ~ m1_subset_1(C_513,k1_zfmisc_1(k2_zfmisc_1(A_511,B_512))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_12102,plain,(
    ! [D_514] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_514) = k9_relat_1('#skF_4',D_514) ),
    inference(resolution,[status(thm)],[c_78,c_12085])).

tff(c_74,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_12112,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12102,c_74])).

tff(c_12163,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_12157,c_12112])).

tff(c_12184,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_82,c_12163])).

tff(c_12192,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_12184])).

tff(c_405,plain,(
    ! [C_98,A_99,B_100] :
      ( v4_relat_1(C_98,A_99)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_424,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_78,c_405])).

tff(c_50,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k1_relat_1(B_23),A_22)
      | ~ v4_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_10,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_5,B_6] : k1_enumset1(A_5,A_5,B_6) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12193,plain,(
    ! [A_528,B_529,C_530,D_531] :
      ( k1_enumset1(A_528,B_529,C_530) = D_531
      | k2_tarski(A_528,C_530) = D_531
      | k2_tarski(B_529,C_530) = D_531
      | k2_tarski(A_528,B_529) = D_531
      | k1_tarski(C_530) = D_531
      | k1_tarski(B_529) = D_531
      | k1_tarski(A_528) = D_531
      | k1_xboole_0 = D_531
      | ~ r1_tarski(D_531,k1_enumset1(A_528,B_529,C_530)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12218,plain,(
    ! [A_5,B_6,D_531] :
      ( k1_enumset1(A_5,A_5,B_6) = D_531
      | k2_tarski(A_5,B_6) = D_531
      | k2_tarski(A_5,B_6) = D_531
      | k2_tarski(A_5,A_5) = D_531
      | k1_tarski(B_6) = D_531
      | k1_tarski(A_5) = D_531
      | k1_tarski(A_5) = D_531
      | k1_xboole_0 = D_531
      | ~ r1_tarski(D_531,k2_tarski(A_5,B_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_12193])).

tff(c_15818,plain,(
    ! [A_737,B_738,D_739] :
      ( k2_tarski(A_737,B_738) = D_739
      | k2_tarski(A_737,B_738) = D_739
      | k2_tarski(A_737,B_738) = D_739
      | k1_tarski(A_737) = D_739
      | k1_tarski(B_738) = D_739
      | k1_tarski(A_737) = D_739
      | k1_tarski(A_737) = D_739
      | k1_xboole_0 = D_739
      | ~ r1_tarski(D_739,k2_tarski(A_737,B_738)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12,c_12218])).

tff(c_15841,plain,(
    ! [A_4,D_739] :
      ( k2_tarski(A_4,A_4) = D_739
      | k2_tarski(A_4,A_4) = D_739
      | k2_tarski(A_4,A_4) = D_739
      | k1_tarski(A_4) = D_739
      | k1_tarski(A_4) = D_739
      | k1_tarski(A_4) = D_739
      | k1_tarski(A_4) = D_739
      | k1_xboole_0 = D_739
      | ~ r1_tarski(D_739,k1_tarski(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_15818])).

tff(c_25748,plain,(
    ! [A_894,D_895] :
      ( k1_tarski(A_894) = D_895
      | k1_tarski(A_894) = D_895
      | k1_tarski(A_894) = D_895
      | k1_tarski(A_894) = D_895
      | k1_tarski(A_894) = D_895
      | k1_tarski(A_894) = D_895
      | k1_tarski(A_894) = D_895
      | k1_xboole_0 = D_895
      | ~ r1_tarski(D_895,k1_tarski(A_894)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_10,c_15841])).

tff(c_25974,plain,(
    ! [A_898,B_899] :
      ( k1_tarski(A_898) = k1_relat_1(B_899)
      | k1_relat_1(B_899) = k1_xboole_0
      | ~ v4_relat_1(B_899,k1_tarski(A_898))
      | ~ v1_relat_1(B_899) ) ),
    inference(resolution,[status(thm)],[c_50,c_25748])).

tff(c_26060,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_424,c_25974])).

tff(c_26107,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_26060])).

tff(c_26108,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_12192,c_26107])).

tff(c_12047,plain,(
    ! [A_509] :
      ( m1_subset_1(A_509,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_509),k2_relat_1(A_509))))
      | ~ v1_funct_1(A_509)
      | ~ v1_relat_1(A_509) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_42,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ m1_subset_1(A_17,k1_zfmisc_1(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12245,plain,(
    ! [A_532] :
      ( r1_tarski(A_532,k2_zfmisc_1(k1_relat_1(A_532),k2_relat_1(A_532)))
      | ~ v1_funct_1(A_532)
      | ~ v1_relat_1(A_532) ) ),
    inference(resolution,[status(thm)],[c_12047,c_42])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12271,plain,(
    ! [A_532] :
      ( k2_zfmisc_1(k1_relat_1(A_532),k2_relat_1(A_532)) = A_532
      | ~ r1_tarski(k2_zfmisc_1(k1_relat_1(A_532),k2_relat_1(A_532)),A_532)
      | ~ v1_funct_1(A_532)
      | ~ v1_relat_1(A_532) ) ),
    inference(resolution,[status(thm)],[c_12245,c_2])).

tff(c_26212,plain,
    ( k2_zfmisc_1(k1_relat_1('#skF_4'),k2_relat_1('#skF_4')) = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_4')),'#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_26108,c_12271])).

tff(c_26384,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_82,c_8,c_20,c_20,c_26108,c_26212])).

tff(c_26556,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26384,c_8])).

tff(c_40,plain,(
    ! [A_16] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_211,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_40,c_193])).

tff(c_54,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_336,plain,(
    ! [B_88,A_89] :
      ( r1_tarski(k9_relat_1(B_88,A_89),k2_relat_1(B_88))
      | ~ v1_relat_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_341,plain,(
    ! [A_89] :
      ( r1_tarski(k9_relat_1(k1_xboole_0,A_89),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_336])).

tff(c_354,plain,(
    ! [A_93] : r1_tarski(k9_relat_1(k1_xboole_0,A_93),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_341])).

tff(c_212,plain,(
    ! [B_73,A_74] :
      ( B_73 = A_74
      | ~ r1_tarski(B_73,A_74)
      | ~ r1_tarski(A_74,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_245,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_212])).

tff(c_364,plain,(
    ! [A_93] : k9_relat_1(k1_xboole_0,A_93) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_354,c_245])).

tff(c_26545,plain,(
    ! [A_93] : k9_relat_1('#skF_4',A_93) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26384,c_26384,c_364])).

tff(c_27228,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26545,c_12112])).

tff(c_27232,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26556,c_27228])).

tff(c_27233,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_12184])).

tff(c_27358,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_27233])).

tff(c_27362,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_27358])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:22:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.55/5.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.55/5.41  
% 13.55/5.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.55/5.41  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 13.55/5.41  
% 13.55/5.41  %Foreground sorts:
% 13.55/5.41  
% 13.55/5.41  
% 13.55/5.41  %Background operators:
% 13.55/5.41  
% 13.55/5.41  
% 13.55/5.41  %Foreground operators:
% 13.55/5.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.55/5.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.55/5.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.55/5.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.55/5.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.55/5.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.55/5.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.55/5.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.55/5.41  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 13.55/5.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.55/5.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.55/5.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.55/5.41  tff('#skF_2', type, '#skF_2': $i).
% 13.55/5.41  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 13.55/5.41  tff('#skF_3', type, '#skF_3': $i).
% 13.55/5.41  tff('#skF_1', type, '#skF_1': $i).
% 13.55/5.41  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 13.55/5.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.55/5.41  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 13.55/5.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.55/5.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.55/5.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.55/5.41  tff('#skF_4', type, '#skF_4': $i).
% 13.55/5.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.55/5.41  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 13.55/5.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.55/5.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.55/5.41  
% 13.65/5.42  tff(f_141, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 13.65/5.42  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 13.65/5.42  tff(f_94, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 13.65/5.42  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 13.65/5.42  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 13.65/5.42  tff(f_105, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 13.65/5.42  tff(f_119, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 13.65/5.42  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 13.65/5.42  tff(f_90, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 13.65/5.42  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 13.65/5.42  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 13.65/5.42  tff(f_72, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 13.65/5.42  tff(f_129, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 13.65/5.42  tff(f_78, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 13.65/5.42  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.65/5.42  tff(f_74, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 13.65/5.42  tff(f_97, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 13.65/5.42  tff(c_78, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 13.65/5.42  tff(c_193, plain, (![C_70, A_71, B_72]: (v1_relat_1(C_70) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 13.65/5.42  tff(c_210, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_193])).
% 13.65/5.42  tff(c_52, plain, (![B_25, A_24]: (r1_tarski(k9_relat_1(B_25, A_24), k2_relat_1(B_25)) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.65/5.42  tff(c_82, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_141])).
% 13.65/5.42  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.65/5.42  tff(c_20, plain, (![B_11]: (k2_zfmisc_1(k1_xboole_0, B_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.65/5.42  tff(c_12157, plain, (![B_525, A_526]: (k1_tarski(k1_funct_1(B_525, A_526))=k2_relat_1(B_525) | k1_tarski(A_526)!=k1_relat_1(B_525) | ~v1_funct_1(B_525) | ~v1_relat_1(B_525))), inference(cnfTransformation, [status(thm)], [f_105])).
% 13.65/5.42  tff(c_12085, plain, (![A_511, B_512, C_513, D_514]: (k7_relset_1(A_511, B_512, C_513, D_514)=k9_relat_1(C_513, D_514) | ~m1_subset_1(C_513, k1_zfmisc_1(k2_zfmisc_1(A_511, B_512))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 13.65/5.42  tff(c_12102, plain, (![D_514]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_514)=k9_relat_1('#skF_4', D_514))), inference(resolution, [status(thm)], [c_78, c_12085])).
% 13.65/5.42  tff(c_74, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 13.65/5.42  tff(c_12112, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_12102, c_74])).
% 13.65/5.42  tff(c_12163, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_12157, c_12112])).
% 13.65/5.42  tff(c_12184, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_210, c_82, c_12163])).
% 13.65/5.42  tff(c_12192, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_12184])).
% 13.65/5.42  tff(c_405, plain, (![C_98, A_99, B_100]: (v4_relat_1(C_98, A_99) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 13.65/5.42  tff(c_424, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_78, c_405])).
% 13.65/5.42  tff(c_50, plain, (![B_23, A_22]: (r1_tarski(k1_relat_1(B_23), A_22) | ~v4_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_90])).
% 13.65/5.42  tff(c_10, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.65/5.42  tff(c_12, plain, (![A_5, B_6]: (k1_enumset1(A_5, A_5, B_6)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.65/5.42  tff(c_12193, plain, (![A_528, B_529, C_530, D_531]: (k1_enumset1(A_528, B_529, C_530)=D_531 | k2_tarski(A_528, C_530)=D_531 | k2_tarski(B_529, C_530)=D_531 | k2_tarski(A_528, B_529)=D_531 | k1_tarski(C_530)=D_531 | k1_tarski(B_529)=D_531 | k1_tarski(A_528)=D_531 | k1_xboole_0=D_531 | ~r1_tarski(D_531, k1_enumset1(A_528, B_529, C_530)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 13.65/5.42  tff(c_12218, plain, (![A_5, B_6, D_531]: (k1_enumset1(A_5, A_5, B_6)=D_531 | k2_tarski(A_5, B_6)=D_531 | k2_tarski(A_5, B_6)=D_531 | k2_tarski(A_5, A_5)=D_531 | k1_tarski(B_6)=D_531 | k1_tarski(A_5)=D_531 | k1_tarski(A_5)=D_531 | k1_xboole_0=D_531 | ~r1_tarski(D_531, k2_tarski(A_5, B_6)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_12193])).
% 13.65/5.42  tff(c_15818, plain, (![A_737, B_738, D_739]: (k2_tarski(A_737, B_738)=D_739 | k2_tarski(A_737, B_738)=D_739 | k2_tarski(A_737, B_738)=D_739 | k1_tarski(A_737)=D_739 | k1_tarski(B_738)=D_739 | k1_tarski(A_737)=D_739 | k1_tarski(A_737)=D_739 | k1_xboole_0=D_739 | ~r1_tarski(D_739, k2_tarski(A_737, B_738)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12, c_12218])).
% 13.65/5.42  tff(c_15841, plain, (![A_4, D_739]: (k2_tarski(A_4, A_4)=D_739 | k2_tarski(A_4, A_4)=D_739 | k2_tarski(A_4, A_4)=D_739 | k1_tarski(A_4)=D_739 | k1_tarski(A_4)=D_739 | k1_tarski(A_4)=D_739 | k1_tarski(A_4)=D_739 | k1_xboole_0=D_739 | ~r1_tarski(D_739, k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_15818])).
% 13.65/5.42  tff(c_25748, plain, (![A_894, D_895]: (k1_tarski(A_894)=D_895 | k1_tarski(A_894)=D_895 | k1_tarski(A_894)=D_895 | k1_tarski(A_894)=D_895 | k1_tarski(A_894)=D_895 | k1_tarski(A_894)=D_895 | k1_tarski(A_894)=D_895 | k1_xboole_0=D_895 | ~r1_tarski(D_895, k1_tarski(A_894)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_10, c_15841])).
% 13.65/5.42  tff(c_25974, plain, (![A_898, B_899]: (k1_tarski(A_898)=k1_relat_1(B_899) | k1_relat_1(B_899)=k1_xboole_0 | ~v4_relat_1(B_899, k1_tarski(A_898)) | ~v1_relat_1(B_899))), inference(resolution, [status(thm)], [c_50, c_25748])).
% 13.65/5.42  tff(c_26060, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_424, c_25974])).
% 13.65/5.42  tff(c_26107, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_210, c_26060])).
% 13.65/5.42  tff(c_26108, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_12192, c_26107])).
% 13.65/5.42  tff(c_12047, plain, (![A_509]: (m1_subset_1(A_509, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_509), k2_relat_1(A_509)))) | ~v1_funct_1(A_509) | ~v1_relat_1(A_509))), inference(cnfTransformation, [status(thm)], [f_129])).
% 13.65/5.42  tff(c_42, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~m1_subset_1(A_17, k1_zfmisc_1(B_18)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 13.65/5.42  tff(c_12245, plain, (![A_532]: (r1_tarski(A_532, k2_zfmisc_1(k1_relat_1(A_532), k2_relat_1(A_532))) | ~v1_funct_1(A_532) | ~v1_relat_1(A_532))), inference(resolution, [status(thm)], [c_12047, c_42])).
% 13.65/5.42  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.65/5.42  tff(c_12271, plain, (![A_532]: (k2_zfmisc_1(k1_relat_1(A_532), k2_relat_1(A_532))=A_532 | ~r1_tarski(k2_zfmisc_1(k1_relat_1(A_532), k2_relat_1(A_532)), A_532) | ~v1_funct_1(A_532) | ~v1_relat_1(A_532))), inference(resolution, [status(thm)], [c_12245, c_2])).
% 13.65/5.42  tff(c_26212, plain, (k2_zfmisc_1(k1_relat_1('#skF_4'), k2_relat_1('#skF_4'))='#skF_4' | ~r1_tarski(k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_4')), '#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_26108, c_12271])).
% 13.65/5.42  tff(c_26384, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_210, c_82, c_8, c_20, c_20, c_26108, c_26212])).
% 13.65/5.42  tff(c_26556, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_26384, c_8])).
% 13.65/5.42  tff(c_40, plain, (![A_16]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 13.65/5.42  tff(c_211, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_193])).
% 13.65/5.42  tff(c_54, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_97])).
% 13.65/5.42  tff(c_336, plain, (![B_88, A_89]: (r1_tarski(k9_relat_1(B_88, A_89), k2_relat_1(B_88)) | ~v1_relat_1(B_88))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.65/5.42  tff(c_341, plain, (![A_89]: (r1_tarski(k9_relat_1(k1_xboole_0, A_89), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_54, c_336])).
% 13.65/5.42  tff(c_354, plain, (![A_93]: (r1_tarski(k9_relat_1(k1_xboole_0, A_93), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_211, c_341])).
% 13.65/5.42  tff(c_212, plain, (![B_73, A_74]: (B_73=A_74 | ~r1_tarski(B_73, A_74) | ~r1_tarski(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.65/5.42  tff(c_245, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_212])).
% 13.65/5.42  tff(c_364, plain, (![A_93]: (k9_relat_1(k1_xboole_0, A_93)=k1_xboole_0)), inference(resolution, [status(thm)], [c_354, c_245])).
% 13.65/5.42  tff(c_26545, plain, (![A_93]: (k9_relat_1('#skF_4', A_93)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26384, c_26384, c_364])).
% 13.65/5.42  tff(c_27228, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26545, c_12112])).
% 13.65/5.42  tff(c_27232, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26556, c_27228])).
% 13.65/5.42  tff(c_27233, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_12184])).
% 13.65/5.42  tff(c_27358, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_27233])).
% 13.65/5.42  tff(c_27362, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_210, c_27358])).
% 13.65/5.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.65/5.42  
% 13.65/5.42  Inference rules
% 13.65/5.42  ----------------------
% 13.65/5.42  #Ref     : 0
% 13.65/5.42  #Sup     : 5961
% 13.65/5.42  #Fact    : 0
% 13.65/5.42  #Define  : 0
% 13.65/5.42  #Split   : 6
% 13.65/5.42  #Chain   : 0
% 13.65/5.42  #Close   : 0
% 13.65/5.42  
% 13.65/5.42  Ordering : KBO
% 13.65/5.42  
% 13.65/5.42  Simplification rules
% 13.65/5.42  ----------------------
% 13.65/5.42  #Subsume      : 1150
% 13.65/5.42  #Demod        : 10098
% 13.65/5.42  #Tautology    : 2376
% 13.65/5.42  #SimpNegUnit  : 2
% 13.65/5.42  #BackRed      : 221
% 13.65/5.42  
% 13.65/5.42  #Partial instantiations: 0
% 13.65/5.42  #Strategies tried      : 1
% 13.65/5.42  
% 13.65/5.42  Timing (in seconds)
% 13.65/5.42  ----------------------
% 13.65/5.43  Preprocessing        : 0.37
% 13.65/5.43  Parsing              : 0.20
% 13.65/5.43  CNF conversion       : 0.02
% 13.65/5.43  Main loop            : 4.28
% 13.65/5.43  Inferencing          : 0.92
% 13.65/5.43  Reduction            : 1.83
% 13.65/5.43  Demodulation         : 1.50
% 13.65/5.43  BG Simplification    : 0.12
% 13.65/5.43  Subsumption          : 1.23
% 13.65/5.43  Abstraction          : 0.22
% 13.65/5.43  MUC search           : 0.00
% 13.65/5.43  Cooper               : 0.00
% 13.65/5.43  Total                : 4.69
% 13.65/5.43  Index Insertion      : 0.00
% 13.65/5.43  Index Deletion       : 0.00
% 13.65/5.43  Index Matching       : 0.00
% 13.65/5.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
