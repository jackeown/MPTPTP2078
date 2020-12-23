%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:50 EST 2020

% Result     : Theorem 6.51s
% Output     : CNFRefutation 6.51s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 476 expanded)
%              Number of leaves         :   46 ( 189 expanded)
%              Depth                    :   23
%              Number of atoms          :  273 (1680 expanded)
%              Number of equality atoms :   53 ( 382 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

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

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

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

tff(c_76,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_64,plain,(
    m1_subset_1('#skF_11','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_68,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_66,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_70,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_170,plain,(
    ! [A_130,B_131,C_132] :
      ( k2_relset_1(A_130,B_131,C_132) = k2_relat_1(C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_177,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_70,c_170])).

tff(c_145,plain,(
    ! [A_124,B_125,C_126] :
      ( k1_relset_1(A_124,B_125,C_126) = k1_relat_1(C_126)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_153,plain,(
    k1_relset_1('#skF_8','#skF_6','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_66,c_145])).

tff(c_62,plain,(
    r1_tarski(k2_relset_1('#skF_7','#skF_8','#skF_9'),k1_relset_1('#skF_8','#skF_6','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_158,plain,(
    r1_tarski(k2_relset_1('#skF_7','#skF_8','#skF_9'),k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_62])).

tff(c_180,plain,(
    r1_tarski(k2_relat_1('#skF_9'),k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_158])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_74,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_72,plain,(
    v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_3407,plain,(
    ! [A_543,C_544,E_545,D_546,F_541,B_542] :
      ( k1_funct_1(k8_funct_2(B_542,C_544,A_543,D_546,E_545),F_541) = k1_funct_1(E_545,k1_funct_1(D_546,F_541))
      | k1_xboole_0 = B_542
      | ~ r1_tarski(k2_relset_1(B_542,C_544,D_546),k1_relset_1(C_544,A_543,E_545))
      | ~ m1_subset_1(F_541,B_542)
      | ~ m1_subset_1(E_545,k1_zfmisc_1(k2_zfmisc_1(C_544,A_543)))
      | ~ v1_funct_1(E_545)
      | ~ m1_subset_1(D_546,k1_zfmisc_1(k2_zfmisc_1(B_542,C_544)))
      | ~ v1_funct_2(D_546,B_542,C_544)
      | ~ v1_funct_1(D_546)
      | v1_xboole_0(C_544) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_3413,plain,(
    ! [A_543,E_545,F_541] :
      ( k1_funct_1(k8_funct_2('#skF_7','#skF_8',A_543,'#skF_9',E_545),F_541) = k1_funct_1(E_545,k1_funct_1('#skF_9',F_541))
      | k1_xboole_0 = '#skF_7'
      | ~ r1_tarski(k2_relat_1('#skF_9'),k1_relset_1('#skF_8',A_543,E_545))
      | ~ m1_subset_1(F_541,'#skF_7')
      | ~ m1_subset_1(E_545,k1_zfmisc_1(k2_zfmisc_1('#skF_8',A_543)))
      | ~ v1_funct_1(E_545)
      | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8')))
      | ~ v1_funct_2('#skF_9','#skF_7','#skF_8')
      | ~ v1_funct_1('#skF_9')
      | v1_xboole_0('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_3407])).

tff(c_3422,plain,(
    ! [A_543,E_545,F_541] :
      ( k1_funct_1(k8_funct_2('#skF_7','#skF_8',A_543,'#skF_9',E_545),F_541) = k1_funct_1(E_545,k1_funct_1('#skF_9',F_541))
      | k1_xboole_0 = '#skF_7'
      | ~ r1_tarski(k2_relat_1('#skF_9'),k1_relset_1('#skF_8',A_543,E_545))
      | ~ m1_subset_1(F_541,'#skF_7')
      | ~ m1_subset_1(E_545,k1_zfmisc_1(k2_zfmisc_1('#skF_8',A_543)))
      | ~ v1_funct_1(E_545)
      | v1_xboole_0('#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_3413])).

tff(c_3570,plain,(
    ! [A_549,E_550,F_551] :
      ( k1_funct_1(k8_funct_2('#skF_7','#skF_8',A_549,'#skF_9',E_550),F_551) = k1_funct_1(E_550,k1_funct_1('#skF_9',F_551))
      | ~ r1_tarski(k2_relat_1('#skF_9'),k1_relset_1('#skF_8',A_549,E_550))
      | ~ m1_subset_1(F_551,'#skF_7')
      | ~ m1_subset_1(E_550,k1_zfmisc_1(k2_zfmisc_1('#skF_8',A_549)))
      | ~ v1_funct_1(E_550) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_60,c_3422])).

tff(c_3572,plain,(
    ! [F_551] :
      ( k1_funct_1(k8_funct_2('#skF_7','#skF_8','#skF_6','#skF_9','#skF_10'),F_551) = k1_funct_1('#skF_10',k1_funct_1('#skF_9',F_551))
      | ~ r1_tarski(k2_relat_1('#skF_9'),k1_relat_1('#skF_10'))
      | ~ m1_subset_1(F_551,'#skF_7')
      | ~ m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_6')))
      | ~ v1_funct_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_3570])).

tff(c_3574,plain,(
    ! [F_551] :
      ( k1_funct_1(k8_funct_2('#skF_7','#skF_8','#skF_6','#skF_9','#skF_10'),F_551) = k1_funct_1('#skF_10',k1_funct_1('#skF_9',F_551))
      | ~ m1_subset_1(F_551,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_180,c_3572])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r2_hidden(A_8,B_9)
      | v1_xboole_0(B_9)
      | ~ m1_subset_1(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_87,plain,(
    ! [C_100,A_101,B_102] :
      ( v1_relat_1(C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_94,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_70,c_87])).

tff(c_152,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_70,c_145])).

tff(c_1562,plain,(
    ! [B_322,A_323,C_324] :
      ( k1_xboole_0 = B_322
      | k1_relset_1(A_323,B_322,C_324) = A_323
      | ~ v1_funct_2(C_324,A_323,B_322)
      | ~ m1_subset_1(C_324,k1_zfmisc_1(k2_zfmisc_1(A_323,B_322))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1565,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_9') = '#skF_7'
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_70,c_1562])).

tff(c_1571,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_9') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_152,c_1565])).

tff(c_1575,plain,(
    k1_relat_1('#skF_9') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_1571])).

tff(c_54,plain,(
    ! [A_65,B_66,C_68] :
      ( k7_partfun1(A_65,B_66,C_68) = k1_funct_1(B_66,C_68)
      | ~ r2_hidden(C_68,k1_relat_1(B_66))
      | ~ v1_funct_1(B_66)
      | ~ v5_relat_1(B_66,A_65)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1609,plain,(
    ! [A_65,C_68] :
      ( k7_partfun1(A_65,'#skF_9',C_68) = k1_funct_1('#skF_9',C_68)
      | ~ r2_hidden(C_68,'#skF_7')
      | ~ v1_funct_1('#skF_9')
      | ~ v5_relat_1('#skF_9',A_65)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1575,c_54])).

tff(c_1629,plain,(
    ! [A_329,C_330] :
      ( k7_partfun1(A_329,'#skF_9',C_330) = k1_funct_1('#skF_9',C_330)
      | ~ r2_hidden(C_330,'#skF_7')
      | ~ v5_relat_1('#skF_9',A_329) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_74,c_1609])).

tff(c_1648,plain,(
    ! [A_329,A_8] :
      ( k7_partfun1(A_329,'#skF_9',A_8) = k1_funct_1('#skF_9',A_8)
      | ~ v5_relat_1('#skF_9',A_329)
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_8,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_12,c_1629])).

tff(c_1703,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1648])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_77,plain,(
    ! [B_97,A_98] :
      ( ~ v1_xboole_0(B_97)
      | B_97 = A_98
      | ~ v1_xboole_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_80,plain,(
    ! [A_98] :
      ( k1_xboole_0 = A_98
      | ~ v1_xboole_0(A_98) ) ),
    inference(resolution,[status(thm)],[c_8,c_77])).

tff(c_1706,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1703,c_80])).

tff(c_1712,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1706])).

tff(c_1714,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_1648])).

tff(c_110,plain,(
    ! [C_110,B_111,A_112] :
      ( v5_relat_1(C_110,B_111)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_112,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_118,plain,(
    v5_relat_1('#skF_10','#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_110])).

tff(c_95,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_66,c_87])).

tff(c_14,plain,(
    ! [A_10,D_49] :
      ( r2_hidden(k1_funct_1(A_10,D_49),k2_relat_1(A_10))
      | ~ r2_hidden(D_49,k1_relat_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_103,plain,(
    ! [A_107,B_108] :
      ( r2_hidden('#skF_1'(A_107,B_108),A_107)
      | r1_tarski(A_107,B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_108,plain,(
    ! [A_107] : r1_tarski(A_107,A_107) ),
    inference(resolution,[status(thm)],[c_103,c_4])).

tff(c_1502,plain,(
    ! [A_304,C_305] :
      ( r2_hidden('#skF_5'(A_304,k2_relat_1(A_304),C_305),k1_relat_1(A_304))
      | ~ r2_hidden(C_305,k2_relat_1(A_304))
      | ~ v1_funct_1(A_304)
      | ~ v1_relat_1(A_304) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1505,plain,(
    ! [A_304,C_305,B_2] :
      ( r2_hidden('#skF_5'(A_304,k2_relat_1(A_304),C_305),B_2)
      | ~ r1_tarski(k1_relat_1(A_304),B_2)
      | ~ r2_hidden(C_305,k2_relat_1(A_304))
      | ~ v1_funct_1(A_304)
      | ~ v1_relat_1(A_304) ) ),
    inference(resolution,[status(thm)],[c_1502,c_2])).

tff(c_16,plain,(
    ! [A_10,C_46] :
      ( k1_funct_1(A_10,'#skF_5'(A_10,k2_relat_1(A_10),C_46)) = C_46
      | ~ r2_hidden(C_46,k2_relat_1(A_10))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1466,plain,(
    ! [A_286,D_287] :
      ( r2_hidden(k1_funct_1(A_286,D_287),k2_relat_1(A_286))
      | ~ r2_hidden(D_287,k1_relat_1(A_286))
      | ~ v1_funct_1(A_286)
      | ~ v1_relat_1(A_286) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1793,plain,(
    ! [A_351,D_352,B_353] :
      ( r2_hidden(k1_funct_1(A_351,D_352),B_353)
      | ~ r1_tarski(k2_relat_1(A_351),B_353)
      | ~ r2_hidden(D_352,k1_relat_1(A_351))
      | ~ v1_funct_1(A_351)
      | ~ v1_relat_1(A_351) ) ),
    inference(resolution,[status(thm)],[c_1466,c_2])).

tff(c_1917,plain,(
    ! [A_378,D_379,B_380,B_381] :
      ( r2_hidden(k1_funct_1(A_378,D_379),B_380)
      | ~ r1_tarski(B_381,B_380)
      | ~ r1_tarski(k2_relat_1(A_378),B_381)
      | ~ r2_hidden(D_379,k1_relat_1(A_378))
      | ~ v1_funct_1(A_378)
      | ~ v1_relat_1(A_378) ) ),
    inference(resolution,[status(thm)],[c_1793,c_2])).

tff(c_1924,plain,(
    ! [A_382,D_383] :
      ( r2_hidden(k1_funct_1(A_382,D_383),k1_relat_1('#skF_10'))
      | ~ r1_tarski(k2_relat_1(A_382),k2_relat_1('#skF_9'))
      | ~ r2_hidden(D_383,k1_relat_1(A_382))
      | ~ v1_funct_1(A_382)
      | ~ v1_relat_1(A_382) ) ),
    inference(resolution,[status(thm)],[c_180,c_1917])).

tff(c_3367,plain,(
    ! [A_531,D_532,B_533] :
      ( r2_hidden(k1_funct_1(A_531,D_532),B_533)
      | ~ r1_tarski(k1_relat_1('#skF_10'),B_533)
      | ~ r1_tarski(k2_relat_1(A_531),k2_relat_1('#skF_9'))
      | ~ r2_hidden(D_532,k1_relat_1(A_531))
      | ~ v1_funct_1(A_531)
      | ~ v1_relat_1(A_531) ) ),
    inference(resolution,[status(thm)],[c_1924,c_2])).

tff(c_3370,plain,(
    ! [D_532,B_533] :
      ( r2_hidden(k1_funct_1('#skF_9',D_532),B_533)
      | ~ r1_tarski(k1_relat_1('#skF_10'),B_533)
      | ~ r2_hidden(D_532,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_108,c_3367])).

tff(c_3374,plain,(
    ! [D_534,B_535] :
      ( r2_hidden(k1_funct_1('#skF_9',D_534),B_535)
      | ~ r1_tarski(k1_relat_1('#skF_10'),B_535)
      | ~ r2_hidden(D_534,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_74,c_1575,c_3370])).

tff(c_3388,plain,(
    ! [C_46,B_535] :
      ( r2_hidden(C_46,B_535)
      | ~ r1_tarski(k1_relat_1('#skF_10'),B_535)
      | ~ r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_46),'#skF_7')
      | ~ r2_hidden(C_46,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_3374])).

tff(c_3402,plain,(
    ! [C_539,B_540] :
      ( r2_hidden(C_539,B_540)
      | ~ r1_tarski(k1_relat_1('#skF_10'),B_540)
      | ~ r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_539),'#skF_7')
      | ~ r2_hidden(C_539,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_74,c_3388])).

tff(c_3427,plain,(
    ! [C_547] :
      ( r2_hidden(C_547,k1_relat_1('#skF_10'))
      | ~ r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_547),'#skF_7')
      | ~ r2_hidden(C_547,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_108,c_3402])).

tff(c_3431,plain,(
    ! [C_305] :
      ( r2_hidden(C_305,k1_relat_1('#skF_10'))
      | ~ r1_tarski(k1_relat_1('#skF_9'),'#skF_7')
      | ~ r2_hidden(C_305,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_1505,c_3427])).

tff(c_3452,plain,(
    ! [C_548] :
      ( r2_hidden(C_548,k1_relat_1('#skF_10'))
      | ~ r2_hidden(C_548,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_74,c_108,c_1575,c_3431])).

tff(c_3528,plain,(
    ! [D_49] :
      ( r2_hidden(k1_funct_1('#skF_9',D_49),k1_relat_1('#skF_10'))
      | ~ r2_hidden(D_49,k1_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_14,c_3452])).

tff(c_3575,plain,(
    ! [D_552] :
      ( r2_hidden(k1_funct_1('#skF_9',D_552),k1_relat_1('#skF_10'))
      | ~ r2_hidden(D_552,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_74,c_1575,c_3528])).

tff(c_3577,plain,(
    ! [A_65,D_552] :
      ( k7_partfun1(A_65,'#skF_10',k1_funct_1('#skF_9',D_552)) = k1_funct_1('#skF_10',k1_funct_1('#skF_9',D_552))
      | ~ v1_funct_1('#skF_10')
      | ~ v5_relat_1('#skF_10',A_65)
      | ~ v1_relat_1('#skF_10')
      | ~ r2_hidden(D_552,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_3575,c_54])).

tff(c_3774,plain,(
    ! [A_561,D_562] :
      ( k7_partfun1(A_561,'#skF_10',k1_funct_1('#skF_9',D_562)) = k1_funct_1('#skF_10',k1_funct_1('#skF_9',D_562))
      | ~ v5_relat_1('#skF_10',A_561)
      | ~ r2_hidden(D_562,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_68,c_3577])).

tff(c_58,plain,(
    k7_partfun1('#skF_6','#skF_10',k1_funct_1('#skF_9','#skF_11')) != k1_funct_1(k8_funct_2('#skF_7','#skF_8','#skF_6','#skF_9','#skF_10'),'#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_3780,plain,
    ( k1_funct_1(k8_funct_2('#skF_7','#skF_8','#skF_6','#skF_9','#skF_10'),'#skF_11') != k1_funct_1('#skF_10',k1_funct_1('#skF_9','#skF_11'))
    | ~ v5_relat_1('#skF_10','#skF_6')
    | ~ r2_hidden('#skF_11','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_3774,c_58])).

tff(c_3794,plain,
    ( k1_funct_1(k8_funct_2('#skF_7','#skF_8','#skF_6','#skF_9','#skF_10'),'#skF_11') != k1_funct_1('#skF_10',k1_funct_1('#skF_9','#skF_11'))
    | ~ r2_hidden('#skF_11','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_3780])).

tff(c_3804,plain,(
    ~ r2_hidden('#skF_11','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_3794])).

tff(c_3807,plain,
    ( v1_xboole_0('#skF_7')
    | ~ m1_subset_1('#skF_11','#skF_7') ),
    inference(resolution,[status(thm)],[c_12,c_3804])).

tff(c_3810,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3807])).

tff(c_3812,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1714,c_3810])).

tff(c_3813,plain,(
    k1_funct_1(k8_funct_2('#skF_7','#skF_8','#skF_6','#skF_9','#skF_10'),'#skF_11') != k1_funct_1('#skF_10',k1_funct_1('#skF_9','#skF_11')) ),
    inference(splitRight,[status(thm)],[c_3794])).

tff(c_3884,plain,(
    ~ m1_subset_1('#skF_11','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_3574,c_3813])).

tff(c_3888,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3884])).

tff(c_3889,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1571])).

tff(c_3898,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3889,c_8])).

tff(c_3901,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_3898])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:09:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.51/2.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.51/2.32  
% 6.51/2.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.51/2.33  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_11 > #skF_7 > #skF_3 > #skF_10 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 6.51/2.33  
% 6.51/2.33  %Foreground sorts:
% 6.51/2.33  
% 6.51/2.33  
% 6.51/2.33  %Background operators:
% 6.51/2.33  
% 6.51/2.33  
% 6.51/2.33  %Foreground operators:
% 6.51/2.33  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.51/2.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.51/2.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.51/2.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.51/2.33  tff('#skF_11', type, '#skF_11': $i).
% 6.51/2.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.51/2.33  tff('#skF_7', type, '#skF_7': $i).
% 6.51/2.33  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.51/2.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.51/2.33  tff('#skF_10', type, '#skF_10': $i).
% 6.51/2.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.51/2.33  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 6.51/2.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.51/2.33  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 6.51/2.33  tff('#skF_6', type, '#skF_6': $i).
% 6.51/2.33  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 6.51/2.33  tff('#skF_9', type, '#skF_9': $i).
% 6.51/2.33  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.51/2.33  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.51/2.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.51/2.33  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.51/2.33  tff('#skF_8', type, '#skF_8': $i).
% 6.51/2.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.51/2.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.51/2.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.51/2.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.51/2.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.51/2.33  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.51/2.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.51/2.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.51/2.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.51/2.33  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.51/2.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.51/2.33  
% 6.51/2.35  tff(f_158, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_funct_2)).
% 6.51/2.35  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.51/2.35  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.51/2.35  tff(f_133, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 6.51/2.35  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 6.51/2.35  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.51/2.35  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.51/2.35  tff(f_109, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 6.51/2.35  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.51/2.35  tff(f_41, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 6.51/2.35  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.51/2.35  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 6.51/2.35  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.51/2.35  tff(c_76, plain, (~v1_xboole_0('#skF_8')), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.51/2.35  tff(c_64, plain, (m1_subset_1('#skF_11', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.51/2.35  tff(c_68, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.51/2.35  tff(c_66, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.51/2.35  tff(c_70, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.51/2.35  tff(c_170, plain, (![A_130, B_131, C_132]: (k2_relset_1(A_130, B_131, C_132)=k2_relat_1(C_132) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.51/2.35  tff(c_177, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_70, c_170])).
% 6.51/2.35  tff(c_145, plain, (![A_124, B_125, C_126]: (k1_relset_1(A_124, B_125, C_126)=k1_relat_1(C_126) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.51/2.35  tff(c_153, plain, (k1_relset_1('#skF_8', '#skF_6', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_66, c_145])).
% 6.51/2.35  tff(c_62, plain, (r1_tarski(k2_relset_1('#skF_7', '#skF_8', '#skF_9'), k1_relset_1('#skF_8', '#skF_6', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.51/2.35  tff(c_158, plain, (r1_tarski(k2_relset_1('#skF_7', '#skF_8', '#skF_9'), k1_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_153, c_62])).
% 6.51/2.35  tff(c_180, plain, (r1_tarski(k2_relat_1('#skF_9'), k1_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_158])).
% 6.51/2.35  tff(c_60, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.51/2.35  tff(c_74, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.51/2.35  tff(c_72, plain, (v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.51/2.35  tff(c_3407, plain, (![A_543, C_544, E_545, D_546, F_541, B_542]: (k1_funct_1(k8_funct_2(B_542, C_544, A_543, D_546, E_545), F_541)=k1_funct_1(E_545, k1_funct_1(D_546, F_541)) | k1_xboole_0=B_542 | ~r1_tarski(k2_relset_1(B_542, C_544, D_546), k1_relset_1(C_544, A_543, E_545)) | ~m1_subset_1(F_541, B_542) | ~m1_subset_1(E_545, k1_zfmisc_1(k2_zfmisc_1(C_544, A_543))) | ~v1_funct_1(E_545) | ~m1_subset_1(D_546, k1_zfmisc_1(k2_zfmisc_1(B_542, C_544))) | ~v1_funct_2(D_546, B_542, C_544) | ~v1_funct_1(D_546) | v1_xboole_0(C_544))), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.51/2.35  tff(c_3413, plain, (![A_543, E_545, F_541]: (k1_funct_1(k8_funct_2('#skF_7', '#skF_8', A_543, '#skF_9', E_545), F_541)=k1_funct_1(E_545, k1_funct_1('#skF_9', F_541)) | k1_xboole_0='#skF_7' | ~r1_tarski(k2_relat_1('#skF_9'), k1_relset_1('#skF_8', A_543, E_545)) | ~m1_subset_1(F_541, '#skF_7') | ~m1_subset_1(E_545, k1_zfmisc_1(k2_zfmisc_1('#skF_8', A_543))) | ~v1_funct_1(E_545) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8'))) | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8') | ~v1_funct_1('#skF_9') | v1_xboole_0('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_177, c_3407])).
% 6.51/2.35  tff(c_3422, plain, (![A_543, E_545, F_541]: (k1_funct_1(k8_funct_2('#skF_7', '#skF_8', A_543, '#skF_9', E_545), F_541)=k1_funct_1(E_545, k1_funct_1('#skF_9', F_541)) | k1_xboole_0='#skF_7' | ~r1_tarski(k2_relat_1('#skF_9'), k1_relset_1('#skF_8', A_543, E_545)) | ~m1_subset_1(F_541, '#skF_7') | ~m1_subset_1(E_545, k1_zfmisc_1(k2_zfmisc_1('#skF_8', A_543))) | ~v1_funct_1(E_545) | v1_xboole_0('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_3413])).
% 6.51/2.35  tff(c_3570, plain, (![A_549, E_550, F_551]: (k1_funct_1(k8_funct_2('#skF_7', '#skF_8', A_549, '#skF_9', E_550), F_551)=k1_funct_1(E_550, k1_funct_1('#skF_9', F_551)) | ~r1_tarski(k2_relat_1('#skF_9'), k1_relset_1('#skF_8', A_549, E_550)) | ~m1_subset_1(F_551, '#skF_7') | ~m1_subset_1(E_550, k1_zfmisc_1(k2_zfmisc_1('#skF_8', A_549))) | ~v1_funct_1(E_550))), inference(negUnitSimplification, [status(thm)], [c_76, c_60, c_3422])).
% 6.51/2.35  tff(c_3572, plain, (![F_551]: (k1_funct_1(k8_funct_2('#skF_7', '#skF_8', '#skF_6', '#skF_9', '#skF_10'), F_551)=k1_funct_1('#skF_10', k1_funct_1('#skF_9', F_551)) | ~r1_tarski(k2_relat_1('#skF_9'), k1_relat_1('#skF_10')) | ~m1_subset_1(F_551, '#skF_7') | ~m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_6'))) | ~v1_funct_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_153, c_3570])).
% 6.51/2.35  tff(c_3574, plain, (![F_551]: (k1_funct_1(k8_funct_2('#skF_7', '#skF_8', '#skF_6', '#skF_9', '#skF_10'), F_551)=k1_funct_1('#skF_10', k1_funct_1('#skF_9', F_551)) | ~m1_subset_1(F_551, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_180, c_3572])).
% 6.51/2.35  tff(c_12, plain, (![A_8, B_9]: (r2_hidden(A_8, B_9) | v1_xboole_0(B_9) | ~m1_subset_1(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.51/2.35  tff(c_87, plain, (![C_100, A_101, B_102]: (v1_relat_1(C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.51/2.35  tff(c_94, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_70, c_87])).
% 6.51/2.35  tff(c_152, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_70, c_145])).
% 6.51/2.35  tff(c_1562, plain, (![B_322, A_323, C_324]: (k1_xboole_0=B_322 | k1_relset_1(A_323, B_322, C_324)=A_323 | ~v1_funct_2(C_324, A_323, B_322) | ~m1_subset_1(C_324, k1_zfmisc_1(k2_zfmisc_1(A_323, B_322))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.51/2.35  tff(c_1565, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_9')='#skF_7' | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_70, c_1562])).
% 6.51/2.35  tff(c_1571, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_9')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_152, c_1565])).
% 6.51/2.35  tff(c_1575, plain, (k1_relat_1('#skF_9')='#skF_7'), inference(splitLeft, [status(thm)], [c_1571])).
% 6.51/2.35  tff(c_54, plain, (![A_65, B_66, C_68]: (k7_partfun1(A_65, B_66, C_68)=k1_funct_1(B_66, C_68) | ~r2_hidden(C_68, k1_relat_1(B_66)) | ~v1_funct_1(B_66) | ~v5_relat_1(B_66, A_65) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.51/2.35  tff(c_1609, plain, (![A_65, C_68]: (k7_partfun1(A_65, '#skF_9', C_68)=k1_funct_1('#skF_9', C_68) | ~r2_hidden(C_68, '#skF_7') | ~v1_funct_1('#skF_9') | ~v5_relat_1('#skF_9', A_65) | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1575, c_54])).
% 6.51/2.35  tff(c_1629, plain, (![A_329, C_330]: (k7_partfun1(A_329, '#skF_9', C_330)=k1_funct_1('#skF_9', C_330) | ~r2_hidden(C_330, '#skF_7') | ~v5_relat_1('#skF_9', A_329))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_74, c_1609])).
% 6.51/2.35  tff(c_1648, plain, (![A_329, A_8]: (k7_partfun1(A_329, '#skF_9', A_8)=k1_funct_1('#skF_9', A_8) | ~v5_relat_1('#skF_9', A_329) | v1_xboole_0('#skF_7') | ~m1_subset_1(A_8, '#skF_7'))), inference(resolution, [status(thm)], [c_12, c_1629])).
% 6.51/2.35  tff(c_1703, plain, (v1_xboole_0('#skF_7')), inference(splitLeft, [status(thm)], [c_1648])).
% 6.51/2.35  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.51/2.35  tff(c_77, plain, (![B_97, A_98]: (~v1_xboole_0(B_97) | B_97=A_98 | ~v1_xboole_0(A_98))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.51/2.35  tff(c_80, plain, (![A_98]: (k1_xboole_0=A_98 | ~v1_xboole_0(A_98))), inference(resolution, [status(thm)], [c_8, c_77])).
% 6.51/2.35  tff(c_1706, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_1703, c_80])).
% 6.51/2.35  tff(c_1712, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_1706])).
% 6.51/2.35  tff(c_1714, plain, (~v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_1648])).
% 6.51/2.35  tff(c_110, plain, (![C_110, B_111, A_112]: (v5_relat_1(C_110, B_111) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_112, B_111))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.51/2.35  tff(c_118, plain, (v5_relat_1('#skF_10', '#skF_6')), inference(resolution, [status(thm)], [c_66, c_110])).
% 6.51/2.35  tff(c_95, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_66, c_87])).
% 6.51/2.35  tff(c_14, plain, (![A_10, D_49]: (r2_hidden(k1_funct_1(A_10, D_49), k2_relat_1(A_10)) | ~r2_hidden(D_49, k1_relat_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.51/2.35  tff(c_103, plain, (![A_107, B_108]: (r2_hidden('#skF_1'(A_107, B_108), A_107) | r1_tarski(A_107, B_108))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.51/2.35  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.51/2.35  tff(c_108, plain, (![A_107]: (r1_tarski(A_107, A_107))), inference(resolution, [status(thm)], [c_103, c_4])).
% 6.51/2.35  tff(c_1502, plain, (![A_304, C_305]: (r2_hidden('#skF_5'(A_304, k2_relat_1(A_304), C_305), k1_relat_1(A_304)) | ~r2_hidden(C_305, k2_relat_1(A_304)) | ~v1_funct_1(A_304) | ~v1_relat_1(A_304))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.51/2.35  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.51/2.35  tff(c_1505, plain, (![A_304, C_305, B_2]: (r2_hidden('#skF_5'(A_304, k2_relat_1(A_304), C_305), B_2) | ~r1_tarski(k1_relat_1(A_304), B_2) | ~r2_hidden(C_305, k2_relat_1(A_304)) | ~v1_funct_1(A_304) | ~v1_relat_1(A_304))), inference(resolution, [status(thm)], [c_1502, c_2])).
% 6.51/2.35  tff(c_16, plain, (![A_10, C_46]: (k1_funct_1(A_10, '#skF_5'(A_10, k2_relat_1(A_10), C_46))=C_46 | ~r2_hidden(C_46, k2_relat_1(A_10)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.51/2.35  tff(c_1466, plain, (![A_286, D_287]: (r2_hidden(k1_funct_1(A_286, D_287), k2_relat_1(A_286)) | ~r2_hidden(D_287, k1_relat_1(A_286)) | ~v1_funct_1(A_286) | ~v1_relat_1(A_286))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.51/2.35  tff(c_1793, plain, (![A_351, D_352, B_353]: (r2_hidden(k1_funct_1(A_351, D_352), B_353) | ~r1_tarski(k2_relat_1(A_351), B_353) | ~r2_hidden(D_352, k1_relat_1(A_351)) | ~v1_funct_1(A_351) | ~v1_relat_1(A_351))), inference(resolution, [status(thm)], [c_1466, c_2])).
% 6.51/2.35  tff(c_1917, plain, (![A_378, D_379, B_380, B_381]: (r2_hidden(k1_funct_1(A_378, D_379), B_380) | ~r1_tarski(B_381, B_380) | ~r1_tarski(k2_relat_1(A_378), B_381) | ~r2_hidden(D_379, k1_relat_1(A_378)) | ~v1_funct_1(A_378) | ~v1_relat_1(A_378))), inference(resolution, [status(thm)], [c_1793, c_2])).
% 6.51/2.35  tff(c_1924, plain, (![A_382, D_383]: (r2_hidden(k1_funct_1(A_382, D_383), k1_relat_1('#skF_10')) | ~r1_tarski(k2_relat_1(A_382), k2_relat_1('#skF_9')) | ~r2_hidden(D_383, k1_relat_1(A_382)) | ~v1_funct_1(A_382) | ~v1_relat_1(A_382))), inference(resolution, [status(thm)], [c_180, c_1917])).
% 6.51/2.35  tff(c_3367, plain, (![A_531, D_532, B_533]: (r2_hidden(k1_funct_1(A_531, D_532), B_533) | ~r1_tarski(k1_relat_1('#skF_10'), B_533) | ~r1_tarski(k2_relat_1(A_531), k2_relat_1('#skF_9')) | ~r2_hidden(D_532, k1_relat_1(A_531)) | ~v1_funct_1(A_531) | ~v1_relat_1(A_531))), inference(resolution, [status(thm)], [c_1924, c_2])).
% 6.51/2.35  tff(c_3370, plain, (![D_532, B_533]: (r2_hidden(k1_funct_1('#skF_9', D_532), B_533) | ~r1_tarski(k1_relat_1('#skF_10'), B_533) | ~r2_hidden(D_532, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_108, c_3367])).
% 6.51/2.35  tff(c_3374, plain, (![D_534, B_535]: (r2_hidden(k1_funct_1('#skF_9', D_534), B_535) | ~r1_tarski(k1_relat_1('#skF_10'), B_535) | ~r2_hidden(D_534, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_74, c_1575, c_3370])).
% 6.51/2.35  tff(c_3388, plain, (![C_46, B_535]: (r2_hidden(C_46, B_535) | ~r1_tarski(k1_relat_1('#skF_10'), B_535) | ~r2_hidden('#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_46), '#skF_7') | ~r2_hidden(C_46, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_3374])).
% 6.51/2.35  tff(c_3402, plain, (![C_539, B_540]: (r2_hidden(C_539, B_540) | ~r1_tarski(k1_relat_1('#skF_10'), B_540) | ~r2_hidden('#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_539), '#skF_7') | ~r2_hidden(C_539, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_74, c_3388])).
% 6.51/2.35  tff(c_3427, plain, (![C_547]: (r2_hidden(C_547, k1_relat_1('#skF_10')) | ~r2_hidden('#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_547), '#skF_7') | ~r2_hidden(C_547, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_108, c_3402])).
% 6.51/2.35  tff(c_3431, plain, (![C_305]: (r2_hidden(C_305, k1_relat_1('#skF_10')) | ~r1_tarski(k1_relat_1('#skF_9'), '#skF_7') | ~r2_hidden(C_305, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_1505, c_3427])).
% 6.51/2.35  tff(c_3452, plain, (![C_548]: (r2_hidden(C_548, k1_relat_1('#skF_10')) | ~r2_hidden(C_548, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_74, c_108, c_1575, c_3431])).
% 6.51/2.35  tff(c_3528, plain, (![D_49]: (r2_hidden(k1_funct_1('#skF_9', D_49), k1_relat_1('#skF_10')) | ~r2_hidden(D_49, k1_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_14, c_3452])).
% 6.51/2.35  tff(c_3575, plain, (![D_552]: (r2_hidden(k1_funct_1('#skF_9', D_552), k1_relat_1('#skF_10')) | ~r2_hidden(D_552, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_74, c_1575, c_3528])).
% 6.51/2.35  tff(c_3577, plain, (![A_65, D_552]: (k7_partfun1(A_65, '#skF_10', k1_funct_1('#skF_9', D_552))=k1_funct_1('#skF_10', k1_funct_1('#skF_9', D_552)) | ~v1_funct_1('#skF_10') | ~v5_relat_1('#skF_10', A_65) | ~v1_relat_1('#skF_10') | ~r2_hidden(D_552, '#skF_7'))), inference(resolution, [status(thm)], [c_3575, c_54])).
% 6.51/2.35  tff(c_3774, plain, (![A_561, D_562]: (k7_partfun1(A_561, '#skF_10', k1_funct_1('#skF_9', D_562))=k1_funct_1('#skF_10', k1_funct_1('#skF_9', D_562)) | ~v5_relat_1('#skF_10', A_561) | ~r2_hidden(D_562, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_68, c_3577])).
% 6.51/2.35  tff(c_58, plain, (k7_partfun1('#skF_6', '#skF_10', k1_funct_1('#skF_9', '#skF_11'))!=k1_funct_1(k8_funct_2('#skF_7', '#skF_8', '#skF_6', '#skF_9', '#skF_10'), '#skF_11')), inference(cnfTransformation, [status(thm)], [f_158])).
% 6.51/2.35  tff(c_3780, plain, (k1_funct_1(k8_funct_2('#skF_7', '#skF_8', '#skF_6', '#skF_9', '#skF_10'), '#skF_11')!=k1_funct_1('#skF_10', k1_funct_1('#skF_9', '#skF_11')) | ~v5_relat_1('#skF_10', '#skF_6') | ~r2_hidden('#skF_11', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_3774, c_58])).
% 6.51/2.35  tff(c_3794, plain, (k1_funct_1(k8_funct_2('#skF_7', '#skF_8', '#skF_6', '#skF_9', '#skF_10'), '#skF_11')!=k1_funct_1('#skF_10', k1_funct_1('#skF_9', '#skF_11')) | ~r2_hidden('#skF_11', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_3780])).
% 6.51/2.35  tff(c_3804, plain, (~r2_hidden('#skF_11', '#skF_7')), inference(splitLeft, [status(thm)], [c_3794])).
% 6.51/2.35  tff(c_3807, plain, (v1_xboole_0('#skF_7') | ~m1_subset_1('#skF_11', '#skF_7')), inference(resolution, [status(thm)], [c_12, c_3804])).
% 6.51/2.35  tff(c_3810, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_3807])).
% 6.51/2.35  tff(c_3812, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1714, c_3810])).
% 6.51/2.35  tff(c_3813, plain, (k1_funct_1(k8_funct_2('#skF_7', '#skF_8', '#skF_6', '#skF_9', '#skF_10'), '#skF_11')!=k1_funct_1('#skF_10', k1_funct_1('#skF_9', '#skF_11'))), inference(splitRight, [status(thm)], [c_3794])).
% 6.51/2.35  tff(c_3884, plain, (~m1_subset_1('#skF_11', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_3574, c_3813])).
% 6.51/2.35  tff(c_3888, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_3884])).
% 6.51/2.35  tff(c_3889, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_1571])).
% 6.51/2.35  tff(c_3898, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_3889, c_8])).
% 6.51/2.35  tff(c_3901, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_3898])).
% 6.51/2.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.51/2.35  
% 6.51/2.35  Inference rules
% 6.51/2.35  ----------------------
% 6.51/2.35  #Ref     : 0
% 6.51/2.35  #Sup     : 839
% 6.51/2.35  #Fact    : 0
% 6.51/2.35  #Define  : 0
% 6.51/2.35  #Split   : 22
% 6.51/2.35  #Chain   : 0
% 6.51/2.35  #Close   : 0
% 6.51/2.35  
% 6.51/2.35  Ordering : KBO
% 6.51/2.35  
% 6.51/2.35  Simplification rules
% 6.51/2.35  ----------------------
% 6.51/2.35  #Subsume      : 215
% 6.51/2.35  #Demod        : 539
% 6.51/2.35  #Tautology    : 136
% 6.51/2.35  #SimpNegUnit  : 35
% 6.51/2.35  #BackRed      : 83
% 6.51/2.35  
% 6.51/2.35  #Partial instantiations: 0
% 6.51/2.35  #Strategies tried      : 1
% 6.51/2.35  
% 6.51/2.35  Timing (in seconds)
% 6.51/2.35  ----------------------
% 6.51/2.35  Preprocessing        : 0.39
% 6.51/2.35  Parsing              : 0.20
% 6.51/2.35  CNF conversion       : 0.03
% 6.51/2.35  Main loop            : 1.13
% 6.51/2.35  Inferencing          : 0.41
% 6.51/2.35  Reduction            : 0.34
% 6.51/2.35  Demodulation         : 0.23
% 6.51/2.35  BG Simplification    : 0.05
% 6.51/2.35  Subsumption          : 0.24
% 6.51/2.35  Abstraction          : 0.07
% 6.51/2.35  MUC search           : 0.00
% 6.51/2.35  Cooper               : 0.00
% 6.51/2.35  Total                : 1.56
% 6.51/2.35  Index Insertion      : 0.00
% 6.51/2.35  Index Deletion       : 0.00
% 6.51/2.35  Index Matching       : 0.00
% 6.51/2.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
