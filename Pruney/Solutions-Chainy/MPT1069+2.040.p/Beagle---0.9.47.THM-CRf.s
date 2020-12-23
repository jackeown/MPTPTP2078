%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:50 EST 2020

% Result     : Theorem 6.28s
% Output     : CNFRefutation 6.40s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 480 expanded)
%              Number of leaves         :   47 ( 191 expanded)
%              Depth                    :   23
%              Number of atoms          :  279 (1684 expanded)
%              Number of equality atoms :   55 ( 384 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_1 > #skF_5 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_158,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ! [E] :
                ( ( v1_funct_1(E)
                  & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                     => ( B = k1_xboole_0
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k7_partfun1(A,E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_133,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ! [E] :
              ( ( v1_funct_1(E)
                & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
             => ! [F] :
                  ( m1_subset_1(F,B)
                 => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                   => ( B = k1_xboole_0
                      | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k1_funct_1(E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_98,axiom,(
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

tff(f_109,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_62,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

tff(c_78,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_66,plain,(
    m1_subset_1('#skF_12','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_70,plain,(
    v1_funct_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_68,plain,(
    m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_218,plain,(
    ! [A_137,B_138,C_139] :
      ( k1_relset_1(A_137,B_138,C_139) = k1_relat_1(C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_231,plain,(
    k1_relset_1('#skF_9','#skF_7','#skF_11') = k1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_68,c_218])).

tff(c_72,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_185,plain,(
    ! [A_132,B_133,C_134] :
      ( k2_relset_1(A_132,B_133,C_134) = k2_relat_1(C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_196,plain,(
    k2_relset_1('#skF_8','#skF_9','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_72,c_185])).

tff(c_64,plain,(
    r1_tarski(k2_relset_1('#skF_8','#skF_9','#skF_10'),k1_relset_1('#skF_9','#skF_7','#skF_11')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_199,plain,(
    r1_tarski(k2_relat_1('#skF_10'),k1_relset_1('#skF_9','#skF_7','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_64])).

tff(c_236,plain,(
    r1_tarski(k2_relat_1('#skF_10'),k1_relat_1('#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_199])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_76,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_74,plain,(
    v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_3471,plain,(
    ! [E_540,F_536,D_535,A_537,B_539,C_538] :
      ( k1_funct_1(k8_funct_2(B_539,C_538,A_537,D_535,E_540),F_536) = k1_funct_1(E_540,k1_funct_1(D_535,F_536))
      | k1_xboole_0 = B_539
      | ~ r1_tarski(k2_relset_1(B_539,C_538,D_535),k1_relset_1(C_538,A_537,E_540))
      | ~ m1_subset_1(F_536,B_539)
      | ~ m1_subset_1(E_540,k1_zfmisc_1(k2_zfmisc_1(C_538,A_537)))
      | ~ v1_funct_1(E_540)
      | ~ m1_subset_1(D_535,k1_zfmisc_1(k2_zfmisc_1(B_539,C_538)))
      | ~ v1_funct_2(D_535,B_539,C_538)
      | ~ v1_funct_1(D_535)
      | v1_xboole_0(C_538) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_3483,plain,(
    ! [A_537,E_540,F_536] :
      ( k1_funct_1(k8_funct_2('#skF_8','#skF_9',A_537,'#skF_10',E_540),F_536) = k1_funct_1(E_540,k1_funct_1('#skF_10',F_536))
      | k1_xboole_0 = '#skF_8'
      | ~ r1_tarski(k2_relat_1('#skF_10'),k1_relset_1('#skF_9',A_537,E_540))
      | ~ m1_subset_1(F_536,'#skF_8')
      | ~ m1_subset_1(E_540,k1_zfmisc_1(k2_zfmisc_1('#skF_9',A_537)))
      | ~ v1_funct_1(E_540)
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9')))
      | ~ v1_funct_2('#skF_10','#skF_8','#skF_9')
      | ~ v1_funct_1('#skF_10')
      | v1_xboole_0('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_3471])).

tff(c_3497,plain,(
    ! [A_537,E_540,F_536] :
      ( k1_funct_1(k8_funct_2('#skF_8','#skF_9',A_537,'#skF_10',E_540),F_536) = k1_funct_1(E_540,k1_funct_1('#skF_10',F_536))
      | k1_xboole_0 = '#skF_8'
      | ~ r1_tarski(k2_relat_1('#skF_10'),k1_relset_1('#skF_9',A_537,E_540))
      | ~ m1_subset_1(F_536,'#skF_8')
      | ~ m1_subset_1(E_540,k1_zfmisc_1(k2_zfmisc_1('#skF_9',A_537)))
      | ~ v1_funct_1(E_540)
      | v1_xboole_0('#skF_9') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_3483])).

tff(c_3649,plain,(
    ! [A_556,E_557,F_558] :
      ( k1_funct_1(k8_funct_2('#skF_8','#skF_9',A_556,'#skF_10',E_557),F_558) = k1_funct_1(E_557,k1_funct_1('#skF_10',F_558))
      | ~ r1_tarski(k2_relat_1('#skF_10'),k1_relset_1('#skF_9',A_556,E_557))
      | ~ m1_subset_1(F_558,'#skF_8')
      | ~ m1_subset_1(E_557,k1_zfmisc_1(k2_zfmisc_1('#skF_9',A_556)))
      | ~ v1_funct_1(E_557) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_62,c_3497])).

tff(c_3657,plain,(
    ! [F_558] :
      ( k1_funct_1(k8_funct_2('#skF_8','#skF_9','#skF_7','#skF_10','#skF_11'),F_558) = k1_funct_1('#skF_11',k1_funct_1('#skF_10',F_558))
      | ~ r1_tarski(k2_relat_1('#skF_10'),k1_relat_1('#skF_11'))
      | ~ m1_subset_1(F_558,'#skF_8')
      | ~ m1_subset_1('#skF_11',k1_zfmisc_1(k2_zfmisc_1('#skF_9','#skF_7')))
      | ~ v1_funct_1('#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_3649])).

tff(c_3663,plain,(
    ! [F_559] :
      ( k1_funct_1(k8_funct_2('#skF_8','#skF_9','#skF_7','#skF_10','#skF_11'),F_559) = k1_funct_1('#skF_11',k1_funct_1('#skF_10',F_559))
      | ~ m1_subset_1(F_559,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_236,c_3657])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( r2_hidden(A_9,B_10)
      | v1_xboole_0(B_10)
      | ~ m1_subset_1(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_114,plain,(
    ! [C_109,A_110,B_111] :
      ( v1_relat_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_125,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_72,c_114])).

tff(c_229,plain,(
    k1_relset_1('#skF_8','#skF_9','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_72,c_218])).

tff(c_1560,plain,(
    ! [B_317,A_318,C_319] :
      ( k1_xboole_0 = B_317
      | k1_relset_1(A_318,B_317,C_319) = A_318
      | ~ v1_funct_2(C_319,A_318,B_317)
      | ~ m1_subset_1(C_319,k1_zfmisc_1(k2_zfmisc_1(A_318,B_317))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1563,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relset_1('#skF_8','#skF_9','#skF_10') = '#skF_8'
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_72,c_1560])).

tff(c_1573,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_229,c_1563])).

tff(c_1579,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1573])).

tff(c_1613,plain,(
    ! [A_325,B_326,C_327] :
      ( k7_partfun1(A_325,B_326,C_327) = k1_funct_1(B_326,C_327)
      | ~ r2_hidden(C_327,k1_relat_1(B_326))
      | ~ v1_funct_1(B_326)
      | ~ v5_relat_1(B_326,A_325)
      | ~ v1_relat_1(B_326) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1618,plain,(
    ! [A_325,C_327] :
      ( k7_partfun1(A_325,'#skF_10',C_327) = k1_funct_1('#skF_10',C_327)
      | ~ r2_hidden(C_327,'#skF_8')
      | ~ v1_funct_1('#skF_10')
      | ~ v5_relat_1('#skF_10',A_325)
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1579,c_1613])).

tff(c_1651,plain,(
    ! [A_328,C_329] :
      ( k7_partfun1(A_328,'#skF_10',C_329) = k1_funct_1('#skF_10',C_329)
      | ~ r2_hidden(C_329,'#skF_8')
      | ~ v5_relat_1('#skF_10',A_328) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_76,c_1618])).

tff(c_1676,plain,(
    ! [A_328,A_9] :
      ( k7_partfun1(A_328,'#skF_10',A_9) = k1_funct_1('#skF_10',A_9)
      | ~ v5_relat_1('#skF_10',A_328)
      | v1_xboole_0('#skF_8')
      | ~ m1_subset_1(A_9,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_14,c_1651])).

tff(c_1689,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1676])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1692,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_1689,c_8])).

tff(c_1696,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1692])).

tff(c_1698,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_1676])).

tff(c_128,plain,(
    ! [C_112,B_113,A_114] :
      ( v5_relat_1(C_112,B_113)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_114,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_141,plain,(
    v5_relat_1('#skF_11','#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_128])).

tff(c_127,plain,(
    v1_relat_1('#skF_11') ),
    inference(resolution,[status(thm)],[c_68,c_114])).

tff(c_16,plain,(
    ! [A_11,D_50] :
      ( r2_hidden(k1_funct_1(A_11,D_50),k2_relat_1(A_11))
      | ~ r2_hidden(D_50,k1_relat_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_107,plain,(
    ! [A_106,B_107] :
      ( r2_hidden('#skF_1'(A_106,B_107),A_106)
      | r1_tarski(A_106,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_112,plain,(
    ! [A_106] : r1_tarski(A_106,A_106) ),
    inference(resolution,[status(thm)],[c_107,c_4])).

tff(c_1506,plain,(
    ! [A_303,C_304] :
      ( r2_hidden('#skF_6'(A_303,k2_relat_1(A_303),C_304),k1_relat_1(A_303))
      | ~ r2_hidden(C_304,k2_relat_1(A_303))
      | ~ v1_funct_1(A_303)
      | ~ v1_relat_1(A_303) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1509,plain,(
    ! [A_303,C_304,B_2] :
      ( r2_hidden('#skF_6'(A_303,k2_relat_1(A_303),C_304),B_2)
      | ~ r1_tarski(k1_relat_1(A_303),B_2)
      | ~ r2_hidden(C_304,k2_relat_1(A_303))
      | ~ v1_funct_1(A_303)
      | ~ v1_relat_1(A_303) ) ),
    inference(resolution,[status(thm)],[c_1506,c_2])).

tff(c_18,plain,(
    ! [A_11,C_47] :
      ( k1_funct_1(A_11,'#skF_6'(A_11,k2_relat_1(A_11),C_47)) = C_47
      | ~ r2_hidden(C_47,k2_relat_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_244,plain,(
    ! [A_140,D_141] :
      ( r2_hidden(k1_funct_1(A_140,D_141),k2_relat_1(A_140))
      | ~ r2_hidden(D_141,k1_relat_1(A_140))
      | ~ v1_funct_1(A_140)
      | ~ v1_relat_1(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1761,plain,(
    ! [A_348,D_349,B_350] :
      ( r2_hidden(k1_funct_1(A_348,D_349),B_350)
      | ~ r1_tarski(k2_relat_1(A_348),B_350)
      | ~ r2_hidden(D_349,k1_relat_1(A_348))
      | ~ v1_funct_1(A_348)
      | ~ v1_relat_1(A_348) ) ),
    inference(resolution,[status(thm)],[c_244,c_2])).

tff(c_1861,plain,(
    ! [A_367,D_368,B_369,B_370] :
      ( r2_hidden(k1_funct_1(A_367,D_368),B_369)
      | ~ r1_tarski(B_370,B_369)
      | ~ r1_tarski(k2_relat_1(A_367),B_370)
      | ~ r2_hidden(D_368,k1_relat_1(A_367))
      | ~ v1_funct_1(A_367)
      | ~ v1_relat_1(A_367) ) ),
    inference(resolution,[status(thm)],[c_1761,c_2])).

tff(c_1868,plain,(
    ! [A_371,D_372] :
      ( r2_hidden(k1_funct_1(A_371,D_372),k1_relat_1('#skF_11'))
      | ~ r1_tarski(k2_relat_1(A_371),k2_relat_1('#skF_10'))
      | ~ r2_hidden(D_372,k1_relat_1(A_371))
      | ~ v1_funct_1(A_371)
      | ~ v1_relat_1(A_371) ) ),
    inference(resolution,[status(thm)],[c_236,c_1861])).

tff(c_3191,plain,(
    ! [A_512,D_513,B_514] :
      ( r2_hidden(k1_funct_1(A_512,D_513),B_514)
      | ~ r1_tarski(k1_relat_1('#skF_11'),B_514)
      | ~ r1_tarski(k2_relat_1(A_512),k2_relat_1('#skF_10'))
      | ~ r2_hidden(D_513,k1_relat_1(A_512))
      | ~ v1_funct_1(A_512)
      | ~ v1_relat_1(A_512) ) ),
    inference(resolution,[status(thm)],[c_1868,c_2])).

tff(c_3194,plain,(
    ! [D_513,B_514] :
      ( r2_hidden(k1_funct_1('#skF_10',D_513),B_514)
      | ~ r1_tarski(k1_relat_1('#skF_11'),B_514)
      | ~ r2_hidden(D_513,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_112,c_3191])).

tff(c_3198,plain,(
    ! [D_515,B_516] :
      ( r2_hidden(k1_funct_1('#skF_10',D_515),B_516)
      | ~ r1_tarski(k1_relat_1('#skF_11'),B_516)
      | ~ r2_hidden(D_515,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_76,c_1579,c_3194])).

tff(c_3212,plain,(
    ! [C_47,B_516] :
      ( r2_hidden(C_47,B_516)
      | ~ r1_tarski(k1_relat_1('#skF_11'),B_516)
      | ~ r2_hidden('#skF_6'('#skF_10',k2_relat_1('#skF_10'),C_47),'#skF_8')
      | ~ r2_hidden(C_47,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_3198])).

tff(c_3226,plain,(
    ! [C_520,B_521] :
      ( r2_hidden(C_520,B_521)
      | ~ r1_tarski(k1_relat_1('#skF_11'),B_521)
      | ~ r2_hidden('#skF_6'('#skF_10',k2_relat_1('#skF_10'),C_520),'#skF_8')
      | ~ r2_hidden(C_520,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_76,c_3212])).

tff(c_3236,plain,(
    ! [C_525] :
      ( r2_hidden(C_525,k1_relat_1('#skF_11'))
      | ~ r2_hidden('#skF_6'('#skF_10',k2_relat_1('#skF_10'),C_525),'#skF_8')
      | ~ r2_hidden(C_525,k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_112,c_3226])).

tff(c_3240,plain,(
    ! [C_304] :
      ( r2_hidden(C_304,k1_relat_1('#skF_11'))
      | ~ r1_tarski(k1_relat_1('#skF_10'),'#skF_8')
      | ~ r2_hidden(C_304,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_1509,c_3236])).

tff(c_3261,plain,(
    ! [C_526] :
      ( r2_hidden(C_526,k1_relat_1('#skF_11'))
      | ~ r2_hidden(C_526,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_76,c_112,c_1579,c_3240])).

tff(c_3321,plain,(
    ! [D_50] :
      ( r2_hidden(k1_funct_1('#skF_10',D_50),k1_relat_1('#skF_11'))
      | ~ r2_hidden(D_50,k1_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(resolution,[status(thm)],[c_16,c_3261])).

tff(c_3375,plain,(
    ! [D_530] :
      ( r2_hidden(k1_funct_1('#skF_10',D_530),k1_relat_1('#skF_11'))
      | ~ r2_hidden(D_530,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_76,c_1579,c_3321])).

tff(c_56,plain,(
    ! [A_66,B_67,C_69] :
      ( k7_partfun1(A_66,B_67,C_69) = k1_funct_1(B_67,C_69)
      | ~ r2_hidden(C_69,k1_relat_1(B_67))
      | ~ v1_funct_1(B_67)
      | ~ v5_relat_1(B_67,A_66)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_3377,plain,(
    ! [A_66,D_530] :
      ( k7_partfun1(A_66,'#skF_11',k1_funct_1('#skF_10',D_530)) = k1_funct_1('#skF_11',k1_funct_1('#skF_10',D_530))
      | ~ v1_funct_1('#skF_11')
      | ~ v5_relat_1('#skF_11',A_66)
      | ~ v1_relat_1('#skF_11')
      | ~ r2_hidden(D_530,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_3375,c_56])).

tff(c_3499,plain,(
    ! [A_541,D_542] :
      ( k7_partfun1(A_541,'#skF_11',k1_funct_1('#skF_10',D_542)) = k1_funct_1('#skF_11',k1_funct_1('#skF_10',D_542))
      | ~ v5_relat_1('#skF_11',A_541)
      | ~ r2_hidden(D_542,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_70,c_3377])).

tff(c_60,plain,(
    k7_partfun1('#skF_7','#skF_11',k1_funct_1('#skF_10','#skF_12')) != k1_funct_1(k8_funct_2('#skF_8','#skF_9','#skF_7','#skF_10','#skF_11'),'#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_3505,plain,
    ( k1_funct_1(k8_funct_2('#skF_8','#skF_9','#skF_7','#skF_10','#skF_11'),'#skF_12') != k1_funct_1('#skF_11',k1_funct_1('#skF_10','#skF_12'))
    | ~ v5_relat_1('#skF_11','#skF_7')
    | ~ r2_hidden('#skF_12','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_3499,c_60])).

tff(c_3517,plain,
    ( k1_funct_1(k8_funct_2('#skF_8','#skF_9','#skF_7','#skF_10','#skF_11'),'#skF_12') != k1_funct_1('#skF_11',k1_funct_1('#skF_10','#skF_12'))
    | ~ r2_hidden('#skF_12','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_3505])).

tff(c_3521,plain,(
    ~ r2_hidden('#skF_12','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_3517])).

tff(c_3538,plain,
    ( v1_xboole_0('#skF_8')
    | ~ m1_subset_1('#skF_12','#skF_8') ),
    inference(resolution,[status(thm)],[c_14,c_3521])).

tff(c_3541,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3538])).

tff(c_3543,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1698,c_3541])).

tff(c_3544,plain,(
    k1_funct_1(k8_funct_2('#skF_8','#skF_9','#skF_7','#skF_10','#skF_11'),'#skF_12') != k1_funct_1('#skF_11',k1_funct_1('#skF_10','#skF_12')) ),
    inference(splitRight,[status(thm)],[c_3517])).

tff(c_3669,plain,(
    ~ m1_subset_1('#skF_12','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_3663,c_3544])).

tff(c_3714,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_3669])).

tff(c_3715,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1573])).

tff(c_10,plain,(
    ! [A_7] : v1_xboole_0('#skF_2'(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_80,plain,(
    ! [A_99] :
      ( k1_xboole_0 = A_99
      | ~ v1_xboole_0(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_84,plain,(
    ! [A_7] : '#skF_2'(A_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_80])).

tff(c_85,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_10])).

tff(c_3732,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3715,c_85])).

tff(c_3737,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3732])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:06:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.28/2.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.28/2.35  
% 6.28/2.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.28/2.35  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_7 > #skF_3 > #skF_10 > #skF_9 > #skF_8 > #skF_1 > #skF_5 > #skF_12 > #skF_4
% 6.28/2.35  
% 6.28/2.35  %Foreground sorts:
% 6.28/2.35  
% 6.28/2.35  
% 6.28/2.35  %Background operators:
% 6.28/2.35  
% 6.28/2.35  
% 6.28/2.35  %Foreground operators:
% 6.28/2.35  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.28/2.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.28/2.35  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.28/2.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.28/2.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.28/2.35  tff('#skF_11', type, '#skF_11': $i).
% 6.28/2.35  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 6.28/2.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.28/2.35  tff('#skF_7', type, '#skF_7': $i).
% 6.28/2.35  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.28/2.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.28/2.35  tff('#skF_10', type, '#skF_10': $i).
% 6.28/2.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.28/2.35  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 6.28/2.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.28/2.35  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 6.28/2.35  tff('#skF_9', type, '#skF_9': $i).
% 6.28/2.35  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.28/2.35  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.28/2.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.28/2.35  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.28/2.35  tff('#skF_8', type, '#skF_8': $i).
% 6.28/2.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.28/2.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.28/2.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.28/2.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.28/2.35  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.28/2.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.28/2.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.28/2.35  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 6.28/2.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.28/2.35  tff('#skF_12', type, '#skF_12': $i).
% 6.28/2.35  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.28/2.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.28/2.35  
% 6.40/2.37  tff(f_158, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_funct_2)).
% 6.40/2.37  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.40/2.37  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.40/2.37  tff(f_133, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 6.40/2.37  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 6.40/2.37  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.40/2.37  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.40/2.37  tff(f_109, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 6.40/2.37  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 6.40/2.37  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.40/2.37  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 6.40/2.37  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.40/2.37  tff(f_41, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc2_subset_1)).
% 6.40/2.37  tff(c_78, plain, (~v1_xboole_0('#skF_9')), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.40/2.37  tff(c_66, plain, (m1_subset_1('#skF_12', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.40/2.37  tff(c_70, plain, (v1_funct_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.40/2.37  tff(c_68, plain, (m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.40/2.37  tff(c_218, plain, (![A_137, B_138, C_139]: (k1_relset_1(A_137, B_138, C_139)=k1_relat_1(C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.40/2.37  tff(c_231, plain, (k1_relset_1('#skF_9', '#skF_7', '#skF_11')=k1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_68, c_218])).
% 6.40/2.37  tff(c_72, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.40/2.37  tff(c_185, plain, (![A_132, B_133, C_134]: (k2_relset_1(A_132, B_133, C_134)=k2_relat_1(C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.40/2.37  tff(c_196, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_72, c_185])).
% 6.40/2.37  tff(c_64, plain, (r1_tarski(k2_relset_1('#skF_8', '#skF_9', '#skF_10'), k1_relset_1('#skF_9', '#skF_7', '#skF_11'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.40/2.37  tff(c_199, plain, (r1_tarski(k2_relat_1('#skF_10'), k1_relset_1('#skF_9', '#skF_7', '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_196, c_64])).
% 6.40/2.37  tff(c_236, plain, (r1_tarski(k2_relat_1('#skF_10'), k1_relat_1('#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_199])).
% 6.40/2.37  tff(c_62, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.40/2.37  tff(c_76, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.40/2.37  tff(c_74, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.40/2.37  tff(c_3471, plain, (![E_540, F_536, D_535, A_537, B_539, C_538]: (k1_funct_1(k8_funct_2(B_539, C_538, A_537, D_535, E_540), F_536)=k1_funct_1(E_540, k1_funct_1(D_535, F_536)) | k1_xboole_0=B_539 | ~r1_tarski(k2_relset_1(B_539, C_538, D_535), k1_relset_1(C_538, A_537, E_540)) | ~m1_subset_1(F_536, B_539) | ~m1_subset_1(E_540, k1_zfmisc_1(k2_zfmisc_1(C_538, A_537))) | ~v1_funct_1(E_540) | ~m1_subset_1(D_535, k1_zfmisc_1(k2_zfmisc_1(B_539, C_538))) | ~v1_funct_2(D_535, B_539, C_538) | ~v1_funct_1(D_535) | v1_xboole_0(C_538))), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.40/2.37  tff(c_3483, plain, (![A_537, E_540, F_536]: (k1_funct_1(k8_funct_2('#skF_8', '#skF_9', A_537, '#skF_10', E_540), F_536)=k1_funct_1(E_540, k1_funct_1('#skF_10', F_536)) | k1_xboole_0='#skF_8' | ~r1_tarski(k2_relat_1('#skF_10'), k1_relset_1('#skF_9', A_537, E_540)) | ~m1_subset_1(F_536, '#skF_8') | ~m1_subset_1(E_540, k1_zfmisc_1(k2_zfmisc_1('#skF_9', A_537))) | ~v1_funct_1(E_540) | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9'))) | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9') | ~v1_funct_1('#skF_10') | v1_xboole_0('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_196, c_3471])).
% 6.40/2.37  tff(c_3497, plain, (![A_537, E_540, F_536]: (k1_funct_1(k8_funct_2('#skF_8', '#skF_9', A_537, '#skF_10', E_540), F_536)=k1_funct_1(E_540, k1_funct_1('#skF_10', F_536)) | k1_xboole_0='#skF_8' | ~r1_tarski(k2_relat_1('#skF_10'), k1_relset_1('#skF_9', A_537, E_540)) | ~m1_subset_1(F_536, '#skF_8') | ~m1_subset_1(E_540, k1_zfmisc_1(k2_zfmisc_1('#skF_9', A_537))) | ~v1_funct_1(E_540) | v1_xboole_0('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_3483])).
% 6.40/2.37  tff(c_3649, plain, (![A_556, E_557, F_558]: (k1_funct_1(k8_funct_2('#skF_8', '#skF_9', A_556, '#skF_10', E_557), F_558)=k1_funct_1(E_557, k1_funct_1('#skF_10', F_558)) | ~r1_tarski(k2_relat_1('#skF_10'), k1_relset_1('#skF_9', A_556, E_557)) | ~m1_subset_1(F_558, '#skF_8') | ~m1_subset_1(E_557, k1_zfmisc_1(k2_zfmisc_1('#skF_9', A_556))) | ~v1_funct_1(E_557))), inference(negUnitSimplification, [status(thm)], [c_78, c_62, c_3497])).
% 6.40/2.37  tff(c_3657, plain, (![F_558]: (k1_funct_1(k8_funct_2('#skF_8', '#skF_9', '#skF_7', '#skF_10', '#skF_11'), F_558)=k1_funct_1('#skF_11', k1_funct_1('#skF_10', F_558)) | ~r1_tarski(k2_relat_1('#skF_10'), k1_relat_1('#skF_11')) | ~m1_subset_1(F_558, '#skF_8') | ~m1_subset_1('#skF_11', k1_zfmisc_1(k2_zfmisc_1('#skF_9', '#skF_7'))) | ~v1_funct_1('#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_231, c_3649])).
% 6.40/2.37  tff(c_3663, plain, (![F_559]: (k1_funct_1(k8_funct_2('#skF_8', '#skF_9', '#skF_7', '#skF_10', '#skF_11'), F_559)=k1_funct_1('#skF_11', k1_funct_1('#skF_10', F_559)) | ~m1_subset_1(F_559, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_236, c_3657])).
% 6.40/2.37  tff(c_14, plain, (![A_9, B_10]: (r2_hidden(A_9, B_10) | v1_xboole_0(B_10) | ~m1_subset_1(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.40/2.37  tff(c_114, plain, (![C_109, A_110, B_111]: (v1_relat_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.40/2.37  tff(c_125, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_72, c_114])).
% 6.40/2.37  tff(c_229, plain, (k1_relset_1('#skF_8', '#skF_9', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_72, c_218])).
% 6.40/2.37  tff(c_1560, plain, (![B_317, A_318, C_319]: (k1_xboole_0=B_317 | k1_relset_1(A_318, B_317, C_319)=A_318 | ~v1_funct_2(C_319, A_318, B_317) | ~m1_subset_1(C_319, k1_zfmisc_1(k2_zfmisc_1(A_318, B_317))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.40/2.37  tff(c_1563, plain, (k1_xboole_0='#skF_9' | k1_relset_1('#skF_8', '#skF_9', '#skF_10')='#skF_8' | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_72, c_1560])).
% 6.40/2.37  tff(c_1573, plain, (k1_xboole_0='#skF_9' | k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_229, c_1563])).
% 6.40/2.37  tff(c_1579, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(splitLeft, [status(thm)], [c_1573])).
% 6.40/2.37  tff(c_1613, plain, (![A_325, B_326, C_327]: (k7_partfun1(A_325, B_326, C_327)=k1_funct_1(B_326, C_327) | ~r2_hidden(C_327, k1_relat_1(B_326)) | ~v1_funct_1(B_326) | ~v5_relat_1(B_326, A_325) | ~v1_relat_1(B_326))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.40/2.37  tff(c_1618, plain, (![A_325, C_327]: (k7_partfun1(A_325, '#skF_10', C_327)=k1_funct_1('#skF_10', C_327) | ~r2_hidden(C_327, '#skF_8') | ~v1_funct_1('#skF_10') | ~v5_relat_1('#skF_10', A_325) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_1579, c_1613])).
% 6.40/2.37  tff(c_1651, plain, (![A_328, C_329]: (k7_partfun1(A_328, '#skF_10', C_329)=k1_funct_1('#skF_10', C_329) | ~r2_hidden(C_329, '#skF_8') | ~v5_relat_1('#skF_10', A_328))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_76, c_1618])).
% 6.40/2.37  tff(c_1676, plain, (![A_328, A_9]: (k7_partfun1(A_328, '#skF_10', A_9)=k1_funct_1('#skF_10', A_9) | ~v5_relat_1('#skF_10', A_328) | v1_xboole_0('#skF_8') | ~m1_subset_1(A_9, '#skF_8'))), inference(resolution, [status(thm)], [c_14, c_1651])).
% 6.40/2.37  tff(c_1689, plain, (v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_1676])).
% 6.40/2.37  tff(c_8, plain, (![A_6]: (k1_xboole_0=A_6 | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.40/2.37  tff(c_1692, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_1689, c_8])).
% 6.40/2.37  tff(c_1696, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_1692])).
% 6.40/2.37  tff(c_1698, plain, (~v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_1676])).
% 6.40/2.37  tff(c_128, plain, (![C_112, B_113, A_114]: (v5_relat_1(C_112, B_113) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_114, B_113))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.40/2.37  tff(c_141, plain, (v5_relat_1('#skF_11', '#skF_7')), inference(resolution, [status(thm)], [c_68, c_128])).
% 6.40/2.37  tff(c_127, plain, (v1_relat_1('#skF_11')), inference(resolution, [status(thm)], [c_68, c_114])).
% 6.40/2.37  tff(c_16, plain, (![A_11, D_50]: (r2_hidden(k1_funct_1(A_11, D_50), k2_relat_1(A_11)) | ~r2_hidden(D_50, k1_relat_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.40/2.37  tff(c_107, plain, (![A_106, B_107]: (r2_hidden('#skF_1'(A_106, B_107), A_106) | r1_tarski(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.40/2.37  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.40/2.37  tff(c_112, plain, (![A_106]: (r1_tarski(A_106, A_106))), inference(resolution, [status(thm)], [c_107, c_4])).
% 6.40/2.37  tff(c_1506, plain, (![A_303, C_304]: (r2_hidden('#skF_6'(A_303, k2_relat_1(A_303), C_304), k1_relat_1(A_303)) | ~r2_hidden(C_304, k2_relat_1(A_303)) | ~v1_funct_1(A_303) | ~v1_relat_1(A_303))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.40/2.37  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.40/2.37  tff(c_1509, plain, (![A_303, C_304, B_2]: (r2_hidden('#skF_6'(A_303, k2_relat_1(A_303), C_304), B_2) | ~r1_tarski(k1_relat_1(A_303), B_2) | ~r2_hidden(C_304, k2_relat_1(A_303)) | ~v1_funct_1(A_303) | ~v1_relat_1(A_303))), inference(resolution, [status(thm)], [c_1506, c_2])).
% 6.40/2.37  tff(c_18, plain, (![A_11, C_47]: (k1_funct_1(A_11, '#skF_6'(A_11, k2_relat_1(A_11), C_47))=C_47 | ~r2_hidden(C_47, k2_relat_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.40/2.37  tff(c_244, plain, (![A_140, D_141]: (r2_hidden(k1_funct_1(A_140, D_141), k2_relat_1(A_140)) | ~r2_hidden(D_141, k1_relat_1(A_140)) | ~v1_funct_1(A_140) | ~v1_relat_1(A_140))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.40/2.37  tff(c_1761, plain, (![A_348, D_349, B_350]: (r2_hidden(k1_funct_1(A_348, D_349), B_350) | ~r1_tarski(k2_relat_1(A_348), B_350) | ~r2_hidden(D_349, k1_relat_1(A_348)) | ~v1_funct_1(A_348) | ~v1_relat_1(A_348))), inference(resolution, [status(thm)], [c_244, c_2])).
% 6.40/2.37  tff(c_1861, plain, (![A_367, D_368, B_369, B_370]: (r2_hidden(k1_funct_1(A_367, D_368), B_369) | ~r1_tarski(B_370, B_369) | ~r1_tarski(k2_relat_1(A_367), B_370) | ~r2_hidden(D_368, k1_relat_1(A_367)) | ~v1_funct_1(A_367) | ~v1_relat_1(A_367))), inference(resolution, [status(thm)], [c_1761, c_2])).
% 6.40/2.37  tff(c_1868, plain, (![A_371, D_372]: (r2_hidden(k1_funct_1(A_371, D_372), k1_relat_1('#skF_11')) | ~r1_tarski(k2_relat_1(A_371), k2_relat_1('#skF_10')) | ~r2_hidden(D_372, k1_relat_1(A_371)) | ~v1_funct_1(A_371) | ~v1_relat_1(A_371))), inference(resolution, [status(thm)], [c_236, c_1861])).
% 6.40/2.37  tff(c_3191, plain, (![A_512, D_513, B_514]: (r2_hidden(k1_funct_1(A_512, D_513), B_514) | ~r1_tarski(k1_relat_1('#skF_11'), B_514) | ~r1_tarski(k2_relat_1(A_512), k2_relat_1('#skF_10')) | ~r2_hidden(D_513, k1_relat_1(A_512)) | ~v1_funct_1(A_512) | ~v1_relat_1(A_512))), inference(resolution, [status(thm)], [c_1868, c_2])).
% 6.40/2.37  tff(c_3194, plain, (![D_513, B_514]: (r2_hidden(k1_funct_1('#skF_10', D_513), B_514) | ~r1_tarski(k1_relat_1('#skF_11'), B_514) | ~r2_hidden(D_513, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_112, c_3191])).
% 6.40/2.37  tff(c_3198, plain, (![D_515, B_516]: (r2_hidden(k1_funct_1('#skF_10', D_515), B_516) | ~r1_tarski(k1_relat_1('#skF_11'), B_516) | ~r2_hidden(D_515, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_76, c_1579, c_3194])).
% 6.40/2.37  tff(c_3212, plain, (![C_47, B_516]: (r2_hidden(C_47, B_516) | ~r1_tarski(k1_relat_1('#skF_11'), B_516) | ~r2_hidden('#skF_6'('#skF_10', k2_relat_1('#skF_10'), C_47), '#skF_8') | ~r2_hidden(C_47, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_18, c_3198])).
% 6.40/2.37  tff(c_3226, plain, (![C_520, B_521]: (r2_hidden(C_520, B_521) | ~r1_tarski(k1_relat_1('#skF_11'), B_521) | ~r2_hidden('#skF_6'('#skF_10', k2_relat_1('#skF_10'), C_520), '#skF_8') | ~r2_hidden(C_520, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_76, c_3212])).
% 6.40/2.37  tff(c_3236, plain, (![C_525]: (r2_hidden(C_525, k1_relat_1('#skF_11')) | ~r2_hidden('#skF_6'('#skF_10', k2_relat_1('#skF_10'), C_525), '#skF_8') | ~r2_hidden(C_525, k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_112, c_3226])).
% 6.40/2.37  tff(c_3240, plain, (![C_304]: (r2_hidden(C_304, k1_relat_1('#skF_11')) | ~r1_tarski(k1_relat_1('#skF_10'), '#skF_8') | ~r2_hidden(C_304, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_1509, c_3236])).
% 6.40/2.37  tff(c_3261, plain, (![C_526]: (r2_hidden(C_526, k1_relat_1('#skF_11')) | ~r2_hidden(C_526, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_76, c_112, c_1579, c_3240])).
% 6.40/2.37  tff(c_3321, plain, (![D_50]: (r2_hidden(k1_funct_1('#skF_10', D_50), k1_relat_1('#skF_11')) | ~r2_hidden(D_50, k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_16, c_3261])).
% 6.40/2.37  tff(c_3375, plain, (![D_530]: (r2_hidden(k1_funct_1('#skF_10', D_530), k1_relat_1('#skF_11')) | ~r2_hidden(D_530, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_76, c_1579, c_3321])).
% 6.40/2.37  tff(c_56, plain, (![A_66, B_67, C_69]: (k7_partfun1(A_66, B_67, C_69)=k1_funct_1(B_67, C_69) | ~r2_hidden(C_69, k1_relat_1(B_67)) | ~v1_funct_1(B_67) | ~v5_relat_1(B_67, A_66) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.40/2.37  tff(c_3377, plain, (![A_66, D_530]: (k7_partfun1(A_66, '#skF_11', k1_funct_1('#skF_10', D_530))=k1_funct_1('#skF_11', k1_funct_1('#skF_10', D_530)) | ~v1_funct_1('#skF_11') | ~v5_relat_1('#skF_11', A_66) | ~v1_relat_1('#skF_11') | ~r2_hidden(D_530, '#skF_8'))), inference(resolution, [status(thm)], [c_3375, c_56])).
% 6.40/2.37  tff(c_3499, plain, (![A_541, D_542]: (k7_partfun1(A_541, '#skF_11', k1_funct_1('#skF_10', D_542))=k1_funct_1('#skF_11', k1_funct_1('#skF_10', D_542)) | ~v5_relat_1('#skF_11', A_541) | ~r2_hidden(D_542, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_70, c_3377])).
% 6.40/2.37  tff(c_60, plain, (k7_partfun1('#skF_7', '#skF_11', k1_funct_1('#skF_10', '#skF_12'))!=k1_funct_1(k8_funct_2('#skF_8', '#skF_9', '#skF_7', '#skF_10', '#skF_11'), '#skF_12')), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.40/2.37  tff(c_3505, plain, (k1_funct_1(k8_funct_2('#skF_8', '#skF_9', '#skF_7', '#skF_10', '#skF_11'), '#skF_12')!=k1_funct_1('#skF_11', k1_funct_1('#skF_10', '#skF_12')) | ~v5_relat_1('#skF_11', '#skF_7') | ~r2_hidden('#skF_12', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_3499, c_60])).
% 6.40/2.37  tff(c_3517, plain, (k1_funct_1(k8_funct_2('#skF_8', '#skF_9', '#skF_7', '#skF_10', '#skF_11'), '#skF_12')!=k1_funct_1('#skF_11', k1_funct_1('#skF_10', '#skF_12')) | ~r2_hidden('#skF_12', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_3505])).
% 6.40/2.37  tff(c_3521, plain, (~r2_hidden('#skF_12', '#skF_8')), inference(splitLeft, [status(thm)], [c_3517])).
% 6.40/2.37  tff(c_3538, plain, (v1_xboole_0('#skF_8') | ~m1_subset_1('#skF_12', '#skF_8')), inference(resolution, [status(thm)], [c_14, c_3521])).
% 6.40/2.37  tff(c_3541, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_3538])).
% 6.40/2.37  tff(c_3543, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1698, c_3541])).
% 6.40/2.37  tff(c_3544, plain, (k1_funct_1(k8_funct_2('#skF_8', '#skF_9', '#skF_7', '#skF_10', '#skF_11'), '#skF_12')!=k1_funct_1('#skF_11', k1_funct_1('#skF_10', '#skF_12'))), inference(splitRight, [status(thm)], [c_3517])).
% 6.40/2.37  tff(c_3669, plain, (~m1_subset_1('#skF_12', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_3663, c_3544])).
% 6.40/2.37  tff(c_3714, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_3669])).
% 6.40/2.37  tff(c_3715, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_1573])).
% 6.40/2.37  tff(c_10, plain, (![A_7]: (v1_xboole_0('#skF_2'(A_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.40/2.37  tff(c_80, plain, (![A_99]: (k1_xboole_0=A_99 | ~v1_xboole_0(A_99))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.40/2.37  tff(c_84, plain, (![A_7]: ('#skF_2'(A_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_80])).
% 6.40/2.37  tff(c_85, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_84, c_10])).
% 6.40/2.37  tff(c_3732, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_3715, c_85])).
% 6.40/2.37  tff(c_3737, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_3732])).
% 6.40/2.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.40/2.37  
% 6.40/2.37  Inference rules
% 6.40/2.37  ----------------------
% 6.40/2.37  #Ref     : 0
% 6.40/2.37  #Sup     : 797
% 6.40/2.37  #Fact    : 0
% 6.40/2.37  #Define  : 0
% 6.40/2.37  #Split   : 28
% 6.40/2.37  #Chain   : 0
% 6.40/2.37  #Close   : 0
% 6.40/2.37  
% 6.40/2.37  Ordering : KBO
% 6.40/2.37  
% 6.40/2.37  Simplification rules
% 6.40/2.37  ----------------------
% 6.40/2.37  #Subsume      : 200
% 6.40/2.37  #Demod        : 540
% 6.40/2.37  #Tautology    : 144
% 6.40/2.37  #SimpNegUnit  : 37
% 6.40/2.37  #BackRed      : 102
% 6.40/2.37  
% 6.40/2.37  #Partial instantiations: 0
% 6.40/2.37  #Strategies tried      : 1
% 6.40/2.37  
% 6.40/2.37  Timing (in seconds)
% 6.40/2.37  ----------------------
% 6.40/2.38  Preprocessing        : 0.46
% 6.40/2.38  Parsing              : 0.21
% 6.40/2.38  CNF conversion       : 0.05
% 6.40/2.38  Main loop            : 1.07
% 6.40/2.38  Inferencing          : 0.37
% 6.40/2.38  Reduction            : 0.35
% 6.40/2.38  Demodulation         : 0.24
% 6.40/2.38  BG Simplification    : 0.05
% 6.40/2.38  Subsumption          : 0.22
% 6.40/2.38  Abstraction          : 0.05
% 6.40/2.38  MUC search           : 0.00
% 6.40/2.38  Cooper               : 0.00
% 6.40/2.38  Total                : 1.58
% 6.40/2.38  Index Insertion      : 0.00
% 6.40/2.38  Index Deletion       : 0.00
% 6.40/2.38  Index Matching       : 0.00
% 6.40/2.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
