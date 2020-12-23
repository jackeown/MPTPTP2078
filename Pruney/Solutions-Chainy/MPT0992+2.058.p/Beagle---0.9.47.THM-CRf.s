%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:39 EST 2020

% Result     : Theorem 7.35s
% Output     : CNFRefutation 7.70s
% Verified   : 
% Statistics : Number of formulae       :  190 (3339 expanded)
%              Number of leaves         :   39 (1054 expanded)
%              Depth                    :   16
%              Number of atoms          :  320 (10366 expanded)
%              Number of equality atoms :   84 (4088 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

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

tff(f_156,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_70,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_122,axiom,(
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

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_136,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_130,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_68,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_30,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_1576,plain,(
    ! [B_194,A_195] :
      ( v1_relat_1(B_194)
      | ~ m1_subset_1(B_194,k1_zfmisc_1(A_195))
      | ~ v1_relat_1(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1582,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_70,c_1576])).

tff(c_1586,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1582])).

tff(c_66,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_81,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_72,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_4358,plain,(
    ! [A_452,B_453,C_454] :
      ( k1_relset_1(A_452,B_453,C_454) = k1_relat_1(C_454)
      | ~ m1_subset_1(C_454,k1_zfmisc_1(k2_zfmisc_1(A_452,B_453))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_4377,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_4358])).

tff(c_5697,plain,(
    ! [B_549,A_550,C_551] :
      ( k1_xboole_0 = B_549
      | k1_relset_1(A_550,B_549,C_551) = A_550
      | ~ v1_funct_2(C_551,A_550,B_549)
      | ~ m1_subset_1(C_551,k1_zfmisc_1(k2_zfmisc_1(A_550,B_549))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_5710,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_5697])).

tff(c_5724,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4377,c_5710])).

tff(c_5725,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_5724])).

tff(c_36,plain,(
    ! [B_25,A_24] :
      ( k1_relat_1(k7_relat_1(B_25,A_24)) = A_24
      | ~ r1_tarski(A_24,k1_relat_1(B_25))
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_5734,plain,(
    ! [A_24] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_24)) = A_24
      | ~ r1_tarski(A_24,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5725,c_36])).

tff(c_5785,plain,(
    ! [A_555] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_555)) = A_555
      | ~ r1_tarski(A_555,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1586,c_5734])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_5381,plain,(
    ! [A_531,B_532,C_533,D_534] :
      ( k2_partfun1(A_531,B_532,C_533,D_534) = k7_relat_1(C_533,D_534)
      | ~ m1_subset_1(C_533,k1_zfmisc_1(k2_zfmisc_1(A_531,B_532)))
      | ~ v1_funct_1(C_533) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_5390,plain,(
    ! [D_534] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_534) = k7_relat_1('#skF_4',D_534)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_70,c_5381])).

tff(c_5402,plain,(
    ! [D_534] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_534) = k7_relat_1('#skF_4',D_534) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_5390])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k7_relat_1(B_23,A_22),B_23)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_126,plain,(
    ! [A_56,B_57] :
      ( r1_tarski(A_56,B_57)
      | ~ m1_subset_1(A_56,k1_zfmisc_1(B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_130,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_70,c_126])).

tff(c_1636,plain,(
    ! [A_202,C_203,B_204] :
      ( r1_tarski(A_202,C_203)
      | ~ r1_tarski(B_204,C_203)
      | ~ r1_tarski(A_202,B_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1662,plain,(
    ! [A_206] :
      ( r1_tarski(A_206,k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_206,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_130,c_1636])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2488,plain,(
    ! [A_278,A_279] :
      ( r1_tarski(A_278,k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_278,A_279)
      | ~ r1_tarski(A_279,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1662,c_8])).

tff(c_3463,plain,(
    ! [B_377,A_378] :
      ( r1_tarski(k7_relat_1(B_377,A_378),k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(B_377,'#skF_4')
      | ~ v1_relat_1(B_377) ) ),
    inference(resolution,[status(thm)],[c_34,c_2488])).

tff(c_20,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1908,plain,(
    ! [C_238,B_239,A_240] :
      ( v5_relat_1(C_238,B_239)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_240,B_239))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1922,plain,(
    ! [A_9,B_239,A_240] :
      ( v5_relat_1(A_9,B_239)
      | ~ r1_tarski(A_9,k2_zfmisc_1(A_240,B_239)) ) ),
    inference(resolution,[status(thm)],[c_20,c_1908])).

tff(c_3496,plain,(
    ! [B_377,A_378] :
      ( v5_relat_1(k7_relat_1(B_377,A_378),'#skF_2')
      | ~ r1_tarski(B_377,'#skF_4')
      | ~ v1_relat_1(B_377) ) ),
    inference(resolution,[status(thm)],[c_3463,c_1922])).

tff(c_1583,plain,(
    ! [A_9,B_10] :
      ( v1_relat_1(A_9)
      | ~ v1_relat_1(B_10)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(resolution,[status(thm)],[c_20,c_1576])).

tff(c_1669,plain,(
    ! [A_206] :
      ( v1_relat_1(A_206)
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_206,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1662,c_1583])).

tff(c_1675,plain,(
    ! [A_207] :
      ( v1_relat_1(A_207)
      | ~ r1_tarski(A_207,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1669])).

tff(c_1679,plain,(
    ! [A_22] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_22))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_34,c_1675])).

tff(c_1686,plain,(
    ! [A_22] : v1_relat_1(k7_relat_1('#skF_4',A_22)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1586,c_1679])).

tff(c_26,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k2_relat_1(B_15),A_14)
      | ~ v5_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2377,plain,(
    ! [A_271,B_272,C_273] :
      ( k1_relset_1(A_271,B_272,C_273) = k1_relat_1(C_273)
      | ~ m1_subset_1(C_273,k1_zfmisc_1(k2_zfmisc_1(A_271,B_272))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_2392,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_2377])).

tff(c_3686,plain,(
    ! [B_385,A_386,C_387] :
      ( k1_xboole_0 = B_385
      | k1_relset_1(A_386,B_385,C_387) = A_386
      | ~ v1_funct_2(C_387,A_386,B_385)
      | ~ m1_subset_1(C_387,k1_zfmisc_1(k2_zfmisc_1(A_386,B_385))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_3696,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_3686])).

tff(c_3707,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_2392,c_3696])).

tff(c_3708,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_3707])).

tff(c_3717,plain,(
    ! [A_24] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_24)) = A_24
      | ~ r1_tarski(A_24,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3708,c_36])).

tff(c_3723,plain,(
    ! [A_24] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_24)) = A_24
      | ~ r1_tarski(A_24,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1586,c_3717])).

tff(c_44,plain,(
    ! [C_34,A_32,B_33] :
      ( m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | ~ r1_tarski(k2_relat_1(C_34),B_33)
      | ~ r1_tarski(k1_relat_1(C_34),A_32)
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3420,plain,(
    ! [A_371,B_372,C_373,D_374] :
      ( k2_partfun1(A_371,B_372,C_373,D_374) = k7_relat_1(C_373,D_374)
      | ~ m1_subset_1(C_373,k1_zfmisc_1(k2_zfmisc_1(A_371,B_372)))
      | ~ v1_funct_1(C_373) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_3427,plain,(
    ! [D_374] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_374) = k7_relat_1('#skF_4',D_374)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_70,c_3420])).

tff(c_3436,plain,(
    ! [D_374] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_374) = k7_relat_1('#skF_4',D_374) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3427])).

tff(c_1557,plain,(
    ! [A_190,B_191,C_192,D_193] :
      ( v1_funct_1(k2_partfun1(A_190,B_191,C_192,D_193))
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(A_190,B_191)))
      | ~ v1_funct_1(C_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_1562,plain,(
    ! [D_193] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_193))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_70,c_1557])).

tff(c_1570,plain,(
    ! [D_193] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_193)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1562])).

tff(c_64,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_153,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_1573,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1570,c_153])).

tff(c_1574,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_1587,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1574])).

tff(c_3439,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3436,c_1587])).

tff(c_3455,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_3439])).

tff(c_3461,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1686,c_3455])).

tff(c_3779,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3461])).

tff(c_3782,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3723,c_3779])).

tff(c_3785,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_6,c_3782])).

tff(c_3786,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_3461])).

tff(c_3815,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_26,c_3786])).

tff(c_3821,plain,(
    ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1686,c_3815])).

tff(c_3824,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3496,c_3821])).

tff(c_3834,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1586,c_6,c_3824])).

tff(c_3836,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1574])).

tff(c_5409,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5402,c_3836])).

tff(c_42,plain,(
    ! [A_29,B_30,C_31] :
      ( k1_relset_1(A_29,B_30,C_31) = k1_relat_1(C_31)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_5491,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_5409,c_42])).

tff(c_3835,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_1574])).

tff(c_5410,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5402,c_3835])).

tff(c_5539,plain,(
    ! [B_541,C_542,A_543] :
      ( k1_xboole_0 = B_541
      | v1_funct_2(C_542,A_543,B_541)
      | k1_relset_1(A_543,B_541,C_542) != A_543
      | ~ m1_subset_1(C_542,k1_zfmisc_1(k2_zfmisc_1(A_543,B_541))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_5542,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_5409,c_5539])).

tff(c_5561,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_5410,c_81,c_5542])).

tff(c_5625,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5491,c_5561])).

tff(c_5791,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5785,c_5625])).

tff(c_5824,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_5791])).

tff(c_5825,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_14,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_5838,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5825,c_5825,c_14])).

tff(c_5826,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_5831,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5825,c_5826])).

tff(c_5867,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5838,c_5831,c_70])).

tff(c_5913,plain,(
    ! [A_568,B_569] :
      ( r1_tarski(A_568,B_569)
      | ~ m1_subset_1(A_568,k1_zfmisc_1(B_569)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_5921,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_5867,c_5913])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5868,plain,(
    ! [A_6] :
      ( A_6 = '#skF_1'
      | ~ r1_tarski(A_6,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5825,c_5825,c_10])).

tff(c_5925,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5921,c_5868])).

tff(c_5832,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5831,c_72])).

tff(c_7772,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5925,c_5925,c_5832])).

tff(c_5839,plain,(
    ! [A_558] : k2_zfmisc_1(A_558,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5825,c_5825,c_14])).

tff(c_5843,plain,(
    v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5839,c_30])).

tff(c_7775,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5925,c_5843])).

tff(c_7773,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5925,c_5867])).

tff(c_16,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_5848,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_1',B_8) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5825,c_5825,c_16])).

tff(c_7774,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_4',B_8) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5925,c_5925,c_5848])).

tff(c_7903,plain,(
    ! [C_750,B_751,A_752] :
      ( v5_relat_1(C_750,B_751)
      | ~ m1_subset_1(C_750,k1_zfmisc_1(k2_zfmisc_1(A_752,B_751))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_7929,plain,(
    ! [C_757,B_758] :
      ( v5_relat_1(C_757,B_758)
      | ~ m1_subset_1(C_757,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7774,c_7903])).

tff(c_7935,plain,(
    ! [B_758] : v5_relat_1('#skF_4',B_758) ),
    inference(resolution,[status(thm)],[c_7773,c_7929])).

tff(c_5888,plain,(
    ! [B_565,A_566] :
      ( r1_tarski(k7_relat_1(B_565,A_566),B_565)
      | ~ v1_relat_1(B_565) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_5892,plain,(
    ! [A_566] :
      ( k7_relat_1('#skF_1',A_566) = '#skF_1'
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_5888,c_5868])).

tff(c_5895,plain,(
    ! [A_566] : k7_relat_1('#skF_1',A_566) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5843,c_5892])).

tff(c_7769,plain,(
    ! [A_566] : k7_relat_1('#skF_4',A_566) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5925,c_5925,c_5895])).

tff(c_7776,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5925,c_5925,c_5838])).

tff(c_7940,plain,(
    ! [A_762,B_763,A_764] :
      ( v5_relat_1(A_762,B_763)
      | ~ r1_tarski(A_762,k2_zfmisc_1(A_764,B_763)) ) ),
    inference(resolution,[status(thm)],[c_20,c_7903])).

tff(c_7950,plain,(
    ! [A_764,B_763,A_22] :
      ( v5_relat_1(k7_relat_1(k2_zfmisc_1(A_764,B_763),A_22),B_763)
      | ~ v1_relat_1(k2_zfmisc_1(A_764,B_763)) ) ),
    inference(resolution,[status(thm)],[c_34,c_7940])).

tff(c_7957,plain,(
    ! [A_764,B_763,A_22] : v5_relat_1(k7_relat_1(k2_zfmisc_1(A_764,B_763),A_22),B_763) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_7950])).

tff(c_8074,plain,(
    ! [B_792,A_793] :
      ( r1_tarski(k2_relat_1(B_792),A_793)
      | ~ v5_relat_1(B_792,A_793)
      | ~ v1_relat_1(B_792) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_7771,plain,(
    ! [A_6] :
      ( A_6 = '#skF_4'
      | ~ r1_tarski(A_6,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5925,c_5925,c_5868])).

tff(c_8139,plain,(
    ! [B_796] :
      ( k2_relat_1(B_796) = '#skF_4'
      | ~ v5_relat_1(B_796,'#skF_4')
      | ~ v1_relat_1(B_796) ) ),
    inference(resolution,[status(thm)],[c_8074,c_7771])).

tff(c_8143,plain,(
    ! [A_764,A_22] :
      ( k2_relat_1(k7_relat_1(k2_zfmisc_1(A_764,'#skF_4'),A_22)) = '#skF_4'
      | ~ v1_relat_1(k7_relat_1(k2_zfmisc_1(A_764,'#skF_4'),A_22)) ) ),
    inference(resolution,[status(thm)],[c_7957,c_8139])).

tff(c_8158,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7775,c_7769,c_7776,c_7769,c_7776,c_8143])).

tff(c_8169,plain,(
    ! [A_14] :
      ( r1_tarski('#skF_4',A_14)
      | ~ v5_relat_1('#skF_4',A_14)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8158,c_26])).

tff(c_8179,plain,(
    ! [A_14] : r1_tarski('#skF_4',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7775,c_7935,c_8169])).

tff(c_9076,plain,(
    ! [A_887,B_888,C_889,D_890] :
      ( k2_partfun1(A_887,B_888,C_889,D_890) = k7_relat_1(C_889,D_890)
      | ~ m1_subset_1(C_889,k1_zfmisc_1(k2_zfmisc_1(A_887,B_888)))
      | ~ v1_funct_1(C_889) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_9747,plain,(
    ! [A_973,B_974,A_975,D_976] :
      ( k2_partfun1(A_973,B_974,A_975,D_976) = k7_relat_1(A_975,D_976)
      | ~ v1_funct_1(A_975)
      | ~ r1_tarski(A_975,k2_zfmisc_1(A_973,B_974)) ) ),
    inference(resolution,[status(thm)],[c_20,c_9076])).

tff(c_9753,plain,(
    ! [A_973,B_974,D_976] :
      ( k2_partfun1(A_973,B_974,'#skF_4',D_976) = k7_relat_1('#skF_4',D_976)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8179,c_9747])).

tff(c_9770,plain,(
    ! [A_973,B_974,D_976] : k2_partfun1(A_973,B_974,'#skF_4',D_976) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_7769,c_9753])).

tff(c_5933,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5925,c_5867])).

tff(c_5936,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5925,c_5925,c_5838])).

tff(c_7744,plain,(
    ! [A_731,B_732,C_733,D_734] :
      ( v1_funct_1(k2_partfun1(A_731,B_732,C_733,D_734))
      | ~ m1_subset_1(C_733,k1_zfmisc_1(k2_zfmisc_1(A_731,B_732)))
      | ~ v1_funct_1(C_733) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_7753,plain,(
    ! [A_735,C_736,D_737] :
      ( v1_funct_1(k2_partfun1(A_735,'#skF_4',C_736,D_737))
      | ~ m1_subset_1(C_736,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_736) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5936,c_7744])).

tff(c_7755,plain,(
    ! [A_735,D_737] :
      ( v1_funct_1(k2_partfun1(A_735,'#skF_4','#skF_4',D_737))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5933,c_7753])).

tff(c_7761,plain,(
    ! [A_735,D_737] : v1_funct_1(k2_partfun1(A_735,'#skF_4','#skF_4',D_737)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_7755])).

tff(c_5869,plain,(
    ! [A_560] :
      ( A_560 = '#skF_1'
      | ~ r1_tarski(A_560,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5825,c_5825,c_10])).

tff(c_5879,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_68,c_5869])).

tff(c_5926,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5879,c_5831,c_5879,c_5879,c_5831,c_5831,c_5879,c_5838,c_5831,c_5831,c_64])).

tff(c_5927,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_5926])).

tff(c_6030,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5925,c_5925,c_5925,c_5927])).

tff(c_7765,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7761,c_6030])).

tff(c_7766,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_5926])).

tff(c_7927,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5925,c_5925,c_5925,c_5925,c_5925,c_5925,c_5925,c_5925,c_5925,c_7766])).

tff(c_7928,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_7927])).

tff(c_7987,plain,(
    ~ r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_7928])).

tff(c_9781,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9770,c_7987])).

tff(c_9787,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8179,c_9781])).

tff(c_9789,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_7927])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,B_10)
      | ~ m1_subset_1(A_9,k1_zfmisc_1(B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_9857,plain,(
    r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_9789,c_18])).

tff(c_9873,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_9857,c_7771])).

tff(c_9788,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_7927])).

tff(c_9879,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9873,c_9788])).

tff(c_9887,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7772,c_9879])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.09  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.08/0.28  % Computer   : n012.cluster.edu
% 0.08/0.28  % Model      : x86_64 x86_64
% 0.08/0.28  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.28  % Memory     : 8042.1875MB
% 0.08/0.28  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.28  % CPULimit   : 60
% 0.08/0.28  % DateTime   : Tue Dec  1 09:16:07 EST 2020
% 0.08/0.28  % CPUTime    : 
% 0.08/0.29  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.35/2.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.70/2.50  
% 7.70/2.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.70/2.50  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.70/2.50  
% 7.70/2.50  %Foreground sorts:
% 7.70/2.50  
% 7.70/2.50  
% 7.70/2.50  %Background operators:
% 7.70/2.50  
% 7.70/2.50  
% 7.70/2.50  %Foreground operators:
% 7.70/2.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.70/2.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.70/2.50  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.70/2.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.70/2.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.70/2.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.70/2.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.70/2.50  tff('#skF_2', type, '#skF_2': $i).
% 7.70/2.50  tff('#skF_3', type, '#skF_3': $i).
% 7.70/2.50  tff('#skF_1', type, '#skF_1': $i).
% 7.70/2.50  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.70/2.50  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.70/2.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.70/2.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.70/2.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.70/2.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.70/2.50  tff('#skF_4', type, '#skF_4': $i).
% 7.70/2.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.70/2.50  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 7.70/2.50  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.70/2.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.70/2.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.70/2.50  
% 7.70/2.53  tff(f_156, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 7.70/2.53  tff(f_70, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.70/2.53  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.70/2.53  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.70/2.53  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 7.70/2.53  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 7.70/2.53  tff(f_136, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 7.70/2.53  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.70/2.53  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 7.70/2.53  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.70/2.53  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 7.70/2.53  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.70/2.53  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 7.70/2.53  tff(f_104, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 7.70/2.53  tff(f_130, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 7.70/2.53  tff(f_47, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.70/2.53  tff(f_41, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 7.70/2.53  tff(c_68, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_156])).
% 7.70/2.53  tff(c_30, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.70/2.53  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_156])).
% 7.70/2.53  tff(c_1576, plain, (![B_194, A_195]: (v1_relat_1(B_194) | ~m1_subset_1(B_194, k1_zfmisc_1(A_195)) | ~v1_relat_1(A_195))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.70/2.53  tff(c_1582, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_70, c_1576])).
% 7.70/2.53  tff(c_1586, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1582])).
% 7.70/2.53  tff(c_66, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_156])).
% 7.70/2.53  tff(c_81, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_66])).
% 7.70/2.53  tff(c_72, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_156])).
% 7.70/2.53  tff(c_4358, plain, (![A_452, B_453, C_454]: (k1_relset_1(A_452, B_453, C_454)=k1_relat_1(C_454) | ~m1_subset_1(C_454, k1_zfmisc_1(k2_zfmisc_1(A_452, B_453))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.70/2.53  tff(c_4377, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_4358])).
% 7.70/2.53  tff(c_5697, plain, (![B_549, A_550, C_551]: (k1_xboole_0=B_549 | k1_relset_1(A_550, B_549, C_551)=A_550 | ~v1_funct_2(C_551, A_550, B_549) | ~m1_subset_1(C_551, k1_zfmisc_1(k2_zfmisc_1(A_550, B_549))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.70/2.53  tff(c_5710, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_70, c_5697])).
% 7.70/2.53  tff(c_5724, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4377, c_5710])).
% 7.70/2.53  tff(c_5725, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_81, c_5724])).
% 7.70/2.53  tff(c_36, plain, (![B_25, A_24]: (k1_relat_1(k7_relat_1(B_25, A_24))=A_24 | ~r1_tarski(A_24, k1_relat_1(B_25)) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.70/2.53  tff(c_5734, plain, (![A_24]: (k1_relat_1(k7_relat_1('#skF_4', A_24))=A_24 | ~r1_tarski(A_24, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5725, c_36])).
% 7.70/2.53  tff(c_5785, plain, (![A_555]: (k1_relat_1(k7_relat_1('#skF_4', A_555))=A_555 | ~r1_tarski(A_555, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1586, c_5734])).
% 7.70/2.53  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_156])).
% 7.70/2.53  tff(c_5381, plain, (![A_531, B_532, C_533, D_534]: (k2_partfun1(A_531, B_532, C_533, D_534)=k7_relat_1(C_533, D_534) | ~m1_subset_1(C_533, k1_zfmisc_1(k2_zfmisc_1(A_531, B_532))) | ~v1_funct_1(C_533))), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.70/2.53  tff(c_5390, plain, (![D_534]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_534)=k7_relat_1('#skF_4', D_534) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_70, c_5381])).
% 7.70/2.53  tff(c_5402, plain, (![D_534]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_534)=k7_relat_1('#skF_4', D_534))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_5390])).
% 7.70/2.53  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.70/2.53  tff(c_34, plain, (![B_23, A_22]: (r1_tarski(k7_relat_1(B_23, A_22), B_23) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.70/2.53  tff(c_126, plain, (![A_56, B_57]: (r1_tarski(A_56, B_57) | ~m1_subset_1(A_56, k1_zfmisc_1(B_57)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.70/2.53  tff(c_130, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_70, c_126])).
% 7.70/2.53  tff(c_1636, plain, (![A_202, C_203, B_204]: (r1_tarski(A_202, C_203) | ~r1_tarski(B_204, C_203) | ~r1_tarski(A_202, B_204))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.70/2.53  tff(c_1662, plain, (![A_206]: (r1_tarski(A_206, k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(A_206, '#skF_4'))), inference(resolution, [status(thm)], [c_130, c_1636])).
% 7.70/2.53  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.70/2.53  tff(c_2488, plain, (![A_278, A_279]: (r1_tarski(A_278, k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(A_278, A_279) | ~r1_tarski(A_279, '#skF_4'))), inference(resolution, [status(thm)], [c_1662, c_8])).
% 7.70/2.53  tff(c_3463, plain, (![B_377, A_378]: (r1_tarski(k7_relat_1(B_377, A_378), k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(B_377, '#skF_4') | ~v1_relat_1(B_377))), inference(resolution, [status(thm)], [c_34, c_2488])).
% 7.70/2.53  tff(c_20, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.70/2.53  tff(c_1908, plain, (![C_238, B_239, A_240]: (v5_relat_1(C_238, B_239) | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_240, B_239))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.70/2.53  tff(c_1922, plain, (![A_9, B_239, A_240]: (v5_relat_1(A_9, B_239) | ~r1_tarski(A_9, k2_zfmisc_1(A_240, B_239)))), inference(resolution, [status(thm)], [c_20, c_1908])).
% 7.70/2.53  tff(c_3496, plain, (![B_377, A_378]: (v5_relat_1(k7_relat_1(B_377, A_378), '#skF_2') | ~r1_tarski(B_377, '#skF_4') | ~v1_relat_1(B_377))), inference(resolution, [status(thm)], [c_3463, c_1922])).
% 7.70/2.53  tff(c_1583, plain, (![A_9, B_10]: (v1_relat_1(A_9) | ~v1_relat_1(B_10) | ~r1_tarski(A_9, B_10))), inference(resolution, [status(thm)], [c_20, c_1576])).
% 7.70/2.53  tff(c_1669, plain, (![A_206]: (v1_relat_1(A_206) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(A_206, '#skF_4'))), inference(resolution, [status(thm)], [c_1662, c_1583])).
% 7.70/2.53  tff(c_1675, plain, (![A_207]: (v1_relat_1(A_207) | ~r1_tarski(A_207, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1669])).
% 7.70/2.53  tff(c_1679, plain, (![A_22]: (v1_relat_1(k7_relat_1('#skF_4', A_22)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_1675])).
% 7.70/2.53  tff(c_1686, plain, (![A_22]: (v1_relat_1(k7_relat_1('#skF_4', A_22)))), inference(demodulation, [status(thm), theory('equality')], [c_1586, c_1679])).
% 7.70/2.53  tff(c_26, plain, (![B_15, A_14]: (r1_tarski(k2_relat_1(B_15), A_14) | ~v5_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.70/2.53  tff(c_2377, plain, (![A_271, B_272, C_273]: (k1_relset_1(A_271, B_272, C_273)=k1_relat_1(C_273) | ~m1_subset_1(C_273, k1_zfmisc_1(k2_zfmisc_1(A_271, B_272))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.70/2.53  tff(c_2392, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_2377])).
% 7.70/2.53  tff(c_3686, plain, (![B_385, A_386, C_387]: (k1_xboole_0=B_385 | k1_relset_1(A_386, B_385, C_387)=A_386 | ~v1_funct_2(C_387, A_386, B_385) | ~m1_subset_1(C_387, k1_zfmisc_1(k2_zfmisc_1(A_386, B_385))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.70/2.53  tff(c_3696, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_70, c_3686])).
% 7.70/2.53  tff(c_3707, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_2392, c_3696])).
% 7.70/2.53  tff(c_3708, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_81, c_3707])).
% 7.70/2.53  tff(c_3717, plain, (![A_24]: (k1_relat_1(k7_relat_1('#skF_4', A_24))=A_24 | ~r1_tarski(A_24, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3708, c_36])).
% 7.70/2.53  tff(c_3723, plain, (![A_24]: (k1_relat_1(k7_relat_1('#skF_4', A_24))=A_24 | ~r1_tarski(A_24, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1586, c_3717])).
% 7.70/2.53  tff(c_44, plain, (![C_34, A_32, B_33]: (m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | ~r1_tarski(k2_relat_1(C_34), B_33) | ~r1_tarski(k1_relat_1(C_34), A_32) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.70/2.53  tff(c_3420, plain, (![A_371, B_372, C_373, D_374]: (k2_partfun1(A_371, B_372, C_373, D_374)=k7_relat_1(C_373, D_374) | ~m1_subset_1(C_373, k1_zfmisc_1(k2_zfmisc_1(A_371, B_372))) | ~v1_funct_1(C_373))), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.70/2.53  tff(c_3427, plain, (![D_374]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_374)=k7_relat_1('#skF_4', D_374) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_70, c_3420])).
% 7.70/2.53  tff(c_3436, plain, (![D_374]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_374)=k7_relat_1('#skF_4', D_374))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_3427])).
% 7.70/2.53  tff(c_1557, plain, (![A_190, B_191, C_192, D_193]: (v1_funct_1(k2_partfun1(A_190, B_191, C_192, D_193)) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(A_190, B_191))) | ~v1_funct_1(C_192))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.70/2.53  tff(c_1562, plain, (![D_193]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_193)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_70, c_1557])).
% 7.70/2.53  tff(c_1570, plain, (![D_193]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_193)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1562])).
% 7.70/2.53  tff(c_64, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_156])).
% 7.70/2.53  tff(c_153, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_64])).
% 7.70/2.53  tff(c_1573, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1570, c_153])).
% 7.70/2.53  tff(c_1574, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_64])).
% 7.70/2.53  tff(c_1587, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1574])).
% 7.70/2.53  tff(c_3439, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_3436, c_1587])).
% 7.70/2.53  tff(c_3455, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_44, c_3439])).
% 7.70/2.53  tff(c_3461, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1686, c_3455])).
% 7.70/2.53  tff(c_3779, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3')), inference(splitLeft, [status(thm)], [c_3461])).
% 7.70/2.53  tff(c_3782, plain, (~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3723, c_3779])).
% 7.70/2.53  tff(c_3785, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_6, c_3782])).
% 7.70/2.53  tff(c_3786, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(splitRight, [status(thm)], [c_3461])).
% 7.70/2.53  tff(c_3815, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_3786])).
% 7.70/2.53  tff(c_3821, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1686, c_3815])).
% 7.70/2.53  tff(c_3824, plain, (~r1_tarski('#skF_4', '#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_3496, c_3821])).
% 7.70/2.53  tff(c_3834, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1586, c_6, c_3824])).
% 7.70/2.53  tff(c_3836, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_1574])).
% 7.70/2.53  tff(c_5409, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_5402, c_3836])).
% 7.70/2.53  tff(c_42, plain, (![A_29, B_30, C_31]: (k1_relset_1(A_29, B_30, C_31)=k1_relat_1(C_31) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.70/2.53  tff(c_5491, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_5409, c_42])).
% 7.70/2.53  tff(c_3835, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_1574])).
% 7.70/2.53  tff(c_5410, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5402, c_3835])).
% 7.70/2.53  tff(c_5539, plain, (![B_541, C_542, A_543]: (k1_xboole_0=B_541 | v1_funct_2(C_542, A_543, B_541) | k1_relset_1(A_543, B_541, C_542)!=A_543 | ~m1_subset_1(C_542, k1_zfmisc_1(k2_zfmisc_1(A_543, B_541))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.70/2.53  tff(c_5542, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_5409, c_5539])).
% 7.70/2.53  tff(c_5561, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_5410, c_81, c_5542])).
% 7.70/2.53  tff(c_5625, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5491, c_5561])).
% 7.70/2.53  tff(c_5791, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5785, c_5625])).
% 7.70/2.53  tff(c_5824, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_5791])).
% 7.70/2.53  tff(c_5825, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_66])).
% 7.70/2.53  tff(c_14, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.70/2.53  tff(c_5838, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5825, c_5825, c_14])).
% 7.70/2.53  tff(c_5826, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_66])).
% 7.70/2.53  tff(c_5831, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5825, c_5826])).
% 7.70/2.53  tff(c_5867, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5838, c_5831, c_70])).
% 7.70/2.53  tff(c_5913, plain, (![A_568, B_569]: (r1_tarski(A_568, B_569) | ~m1_subset_1(A_568, k1_zfmisc_1(B_569)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.70/2.53  tff(c_5921, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_5867, c_5913])).
% 7.70/2.53  tff(c_10, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.70/2.53  tff(c_5868, plain, (![A_6]: (A_6='#skF_1' | ~r1_tarski(A_6, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5825, c_5825, c_10])).
% 7.70/2.53  tff(c_5925, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_5921, c_5868])).
% 7.70/2.53  tff(c_5832, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5831, c_72])).
% 7.70/2.53  tff(c_7772, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5925, c_5925, c_5832])).
% 7.70/2.53  tff(c_5839, plain, (![A_558]: (k2_zfmisc_1(A_558, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5825, c_5825, c_14])).
% 7.70/2.53  tff(c_5843, plain, (v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5839, c_30])).
% 7.70/2.53  tff(c_7775, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5925, c_5843])).
% 7.70/2.53  tff(c_7773, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5925, c_5867])).
% 7.70/2.53  tff(c_16, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.70/2.53  tff(c_5848, plain, (![B_8]: (k2_zfmisc_1('#skF_1', B_8)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5825, c_5825, c_16])).
% 7.70/2.53  tff(c_7774, plain, (![B_8]: (k2_zfmisc_1('#skF_4', B_8)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5925, c_5925, c_5848])).
% 7.70/2.53  tff(c_7903, plain, (![C_750, B_751, A_752]: (v5_relat_1(C_750, B_751) | ~m1_subset_1(C_750, k1_zfmisc_1(k2_zfmisc_1(A_752, B_751))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.70/2.53  tff(c_7929, plain, (![C_757, B_758]: (v5_relat_1(C_757, B_758) | ~m1_subset_1(C_757, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_7774, c_7903])).
% 7.70/2.53  tff(c_7935, plain, (![B_758]: (v5_relat_1('#skF_4', B_758))), inference(resolution, [status(thm)], [c_7773, c_7929])).
% 7.70/2.53  tff(c_5888, plain, (![B_565, A_566]: (r1_tarski(k7_relat_1(B_565, A_566), B_565) | ~v1_relat_1(B_565))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.70/2.53  tff(c_5892, plain, (![A_566]: (k7_relat_1('#skF_1', A_566)='#skF_1' | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_5888, c_5868])).
% 7.70/2.53  tff(c_5895, plain, (![A_566]: (k7_relat_1('#skF_1', A_566)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5843, c_5892])).
% 7.70/2.53  tff(c_7769, plain, (![A_566]: (k7_relat_1('#skF_4', A_566)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5925, c_5925, c_5895])).
% 7.70/2.53  tff(c_7776, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5925, c_5925, c_5838])).
% 7.70/2.53  tff(c_7940, plain, (![A_762, B_763, A_764]: (v5_relat_1(A_762, B_763) | ~r1_tarski(A_762, k2_zfmisc_1(A_764, B_763)))), inference(resolution, [status(thm)], [c_20, c_7903])).
% 7.70/2.53  tff(c_7950, plain, (![A_764, B_763, A_22]: (v5_relat_1(k7_relat_1(k2_zfmisc_1(A_764, B_763), A_22), B_763) | ~v1_relat_1(k2_zfmisc_1(A_764, B_763)))), inference(resolution, [status(thm)], [c_34, c_7940])).
% 7.70/2.53  tff(c_7957, plain, (![A_764, B_763, A_22]: (v5_relat_1(k7_relat_1(k2_zfmisc_1(A_764, B_763), A_22), B_763))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_7950])).
% 7.70/2.53  tff(c_8074, plain, (![B_792, A_793]: (r1_tarski(k2_relat_1(B_792), A_793) | ~v5_relat_1(B_792, A_793) | ~v1_relat_1(B_792))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.70/2.53  tff(c_7771, plain, (![A_6]: (A_6='#skF_4' | ~r1_tarski(A_6, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5925, c_5925, c_5868])).
% 7.70/2.53  tff(c_8139, plain, (![B_796]: (k2_relat_1(B_796)='#skF_4' | ~v5_relat_1(B_796, '#skF_4') | ~v1_relat_1(B_796))), inference(resolution, [status(thm)], [c_8074, c_7771])).
% 7.70/2.53  tff(c_8143, plain, (![A_764, A_22]: (k2_relat_1(k7_relat_1(k2_zfmisc_1(A_764, '#skF_4'), A_22))='#skF_4' | ~v1_relat_1(k7_relat_1(k2_zfmisc_1(A_764, '#skF_4'), A_22)))), inference(resolution, [status(thm)], [c_7957, c_8139])).
% 7.70/2.53  tff(c_8158, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7775, c_7769, c_7776, c_7769, c_7776, c_8143])).
% 7.70/2.53  tff(c_8169, plain, (![A_14]: (r1_tarski('#skF_4', A_14) | ~v5_relat_1('#skF_4', A_14) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8158, c_26])).
% 7.70/2.53  tff(c_8179, plain, (![A_14]: (r1_tarski('#skF_4', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_7775, c_7935, c_8169])).
% 7.70/2.53  tff(c_9076, plain, (![A_887, B_888, C_889, D_890]: (k2_partfun1(A_887, B_888, C_889, D_890)=k7_relat_1(C_889, D_890) | ~m1_subset_1(C_889, k1_zfmisc_1(k2_zfmisc_1(A_887, B_888))) | ~v1_funct_1(C_889))), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.70/2.53  tff(c_9747, plain, (![A_973, B_974, A_975, D_976]: (k2_partfun1(A_973, B_974, A_975, D_976)=k7_relat_1(A_975, D_976) | ~v1_funct_1(A_975) | ~r1_tarski(A_975, k2_zfmisc_1(A_973, B_974)))), inference(resolution, [status(thm)], [c_20, c_9076])).
% 7.70/2.53  tff(c_9753, plain, (![A_973, B_974, D_976]: (k2_partfun1(A_973, B_974, '#skF_4', D_976)=k7_relat_1('#skF_4', D_976) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_8179, c_9747])).
% 7.70/2.53  tff(c_9770, plain, (![A_973, B_974, D_976]: (k2_partfun1(A_973, B_974, '#skF_4', D_976)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_7769, c_9753])).
% 7.70/2.53  tff(c_5933, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5925, c_5867])).
% 7.70/2.53  tff(c_5936, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5925, c_5925, c_5838])).
% 7.70/2.53  tff(c_7744, plain, (![A_731, B_732, C_733, D_734]: (v1_funct_1(k2_partfun1(A_731, B_732, C_733, D_734)) | ~m1_subset_1(C_733, k1_zfmisc_1(k2_zfmisc_1(A_731, B_732))) | ~v1_funct_1(C_733))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.70/2.53  tff(c_7753, plain, (![A_735, C_736, D_737]: (v1_funct_1(k2_partfun1(A_735, '#skF_4', C_736, D_737)) | ~m1_subset_1(C_736, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_736))), inference(superposition, [status(thm), theory('equality')], [c_5936, c_7744])).
% 7.70/2.53  tff(c_7755, plain, (![A_735, D_737]: (v1_funct_1(k2_partfun1(A_735, '#skF_4', '#skF_4', D_737)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_5933, c_7753])).
% 7.70/2.53  tff(c_7761, plain, (![A_735, D_737]: (v1_funct_1(k2_partfun1(A_735, '#skF_4', '#skF_4', D_737)))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_7755])).
% 7.70/2.53  tff(c_5869, plain, (![A_560]: (A_560='#skF_1' | ~r1_tarski(A_560, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5825, c_5825, c_10])).
% 7.70/2.53  tff(c_5879, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_68, c_5869])).
% 7.70/2.53  tff(c_5926, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5879, c_5831, c_5879, c_5879, c_5831, c_5831, c_5879, c_5838, c_5831, c_5831, c_64])).
% 7.70/2.53  tff(c_5927, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(splitLeft, [status(thm)], [c_5926])).
% 7.70/2.53  tff(c_6030, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5925, c_5925, c_5925, c_5927])).
% 7.70/2.53  tff(c_7765, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7761, c_6030])).
% 7.70/2.53  tff(c_7766, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_5926])).
% 7.70/2.53  tff(c_7927, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5925, c_5925, c_5925, c_5925, c_5925, c_5925, c_5925, c_5925, c_5925, c_7766])).
% 7.70/2.53  tff(c_7928, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_7927])).
% 7.70/2.53  tff(c_7987, plain, (~r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_20, c_7928])).
% 7.70/2.53  tff(c_9781, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9770, c_7987])).
% 7.70/2.53  tff(c_9787, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8179, c_9781])).
% 7.70/2.53  tff(c_9789, plain, (m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_7927])).
% 7.70/2.53  tff(c_18, plain, (![A_9, B_10]: (r1_tarski(A_9, B_10) | ~m1_subset_1(A_9, k1_zfmisc_1(B_10)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.70/2.53  tff(c_9857, plain, (r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_9789, c_18])).
% 7.70/2.53  tff(c_9873, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_9857, c_7771])).
% 7.70/2.53  tff(c_9788, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_7927])).
% 7.70/2.53  tff(c_9879, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_9873, c_9788])).
% 7.70/2.53  tff(c_9887, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7772, c_9879])).
% 7.70/2.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.70/2.53  
% 7.70/2.53  Inference rules
% 7.70/2.53  ----------------------
% 7.70/2.53  #Ref     : 0
% 7.70/2.53  #Sup     : 2061
% 7.70/2.53  #Fact    : 0
% 7.70/2.53  #Define  : 0
% 7.70/2.53  #Split   : 36
% 7.70/2.53  #Chain   : 0
% 7.70/2.53  #Close   : 0
% 7.70/2.53  
% 7.70/2.53  Ordering : KBO
% 7.70/2.53  
% 7.70/2.53  Simplification rules
% 7.70/2.53  ----------------------
% 7.70/2.53  #Subsume      : 479
% 7.70/2.53  #Demod        : 1900
% 7.70/2.53  #Tautology    : 966
% 7.70/2.53  #SimpNegUnit  : 72
% 7.70/2.53  #BackRed      : 76
% 7.70/2.53  
% 7.70/2.53  #Partial instantiations: 0
% 7.70/2.53  #Strategies tried      : 1
% 7.70/2.53  
% 7.70/2.53  Timing (in seconds)
% 7.70/2.53  ----------------------
% 7.70/2.53  Preprocessing        : 0.35
% 7.70/2.53  Parsing              : 0.19
% 7.70/2.53  CNF conversion       : 0.02
% 7.70/2.53  Main loop            : 1.47
% 7.70/2.53  Inferencing          : 0.51
% 7.70/2.53  Reduction            : 0.49
% 7.70/2.53  Demodulation         : 0.35
% 7.70/2.53  BG Simplification    : 0.05
% 7.70/2.53  Subsumption          : 0.30
% 7.70/2.53  Abstraction          : 0.06
% 7.70/2.53  MUC search           : 0.00
% 7.70/2.53  Cooper               : 0.00
% 7.70/2.53  Total                : 1.89
% 7.70/2.53  Index Insertion      : 0.00
% 7.70/2.53  Index Deletion       : 0.00
% 7.70/2.53  Index Matching       : 0.00
% 7.70/2.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
