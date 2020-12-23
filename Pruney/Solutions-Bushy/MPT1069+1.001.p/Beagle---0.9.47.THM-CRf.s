%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1069+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:21 EST 2020

% Result     : Theorem 5.31s
% Output     : CNFRefutation 5.31s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 523 expanded)
%              Number of leaves         :   41 ( 197 expanded)
%              Depth                    :   14
%              Number of atoms          :  285 (1775 expanded)
%              Number of equality atoms :   58 ( 334 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_138,negated_conjecture,(
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
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_46,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_101,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_74,axiom,(
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

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_113,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_16,plain,(
    ! [A_31,B_32] :
      ( r2_hidden(A_31,B_32)
      | v1_xboole_0(B_32)
      | ~ m1_subset_1(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_44,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_10,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_49,plain,(
    ! [A_57] :
      ( k1_xboole_0 = A_57
      | ~ v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_53,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_49])).

tff(c_54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_10])).

tff(c_36,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_171,plain,(
    ! [A_90,B_91,C_92] :
      ( k1_relset_1(A_90,B_91,C_92) = k1_relat_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_90,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_184,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_171])).

tff(c_34,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_189,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_34])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_2754,plain,(
    ! [C_487,F_486,D_484,A_489,B_488,E_485] :
      ( k1_funct_1(k8_funct_2(B_488,C_487,A_489,D_484,E_485),F_486) = k1_funct_1(E_485,k1_funct_1(D_484,F_486))
      | k1_xboole_0 = B_488
      | ~ r1_tarski(k2_relset_1(B_488,C_487,D_484),k1_relset_1(C_487,A_489,E_485))
      | ~ m1_subset_1(F_486,B_488)
      | ~ m1_subset_1(E_485,k1_zfmisc_1(k2_zfmisc_1(C_487,A_489)))
      | ~ v1_funct_1(E_485)
      | ~ m1_subset_1(D_484,k1_zfmisc_1(k2_zfmisc_1(B_488,C_487)))
      | ~ v1_funct_2(D_484,B_488,C_487)
      | ~ v1_funct_1(D_484)
      | v1_xboole_0(C_487) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2756,plain,(
    ! [B_488,D_484,F_486] :
      ( k1_funct_1(k8_funct_2(B_488,'#skF_3','#skF_1',D_484,'#skF_5'),F_486) = k1_funct_1('#skF_5',k1_funct_1(D_484,F_486))
      | k1_xboole_0 = B_488
      | ~ r1_tarski(k2_relset_1(B_488,'#skF_3',D_484),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_486,B_488)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_484,k1_zfmisc_1(k2_zfmisc_1(B_488,'#skF_3')))
      | ~ v1_funct_2(D_484,B_488,'#skF_3')
      | ~ v1_funct_1(D_484)
      | v1_xboole_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_2754])).

tff(c_2760,plain,(
    ! [B_488,D_484,F_486] :
      ( k1_funct_1(k8_funct_2(B_488,'#skF_3','#skF_1',D_484,'#skF_5'),F_486) = k1_funct_1('#skF_5',k1_funct_1(D_484,F_486))
      | k1_xboole_0 = B_488
      | ~ r1_tarski(k2_relset_1(B_488,'#skF_3',D_484),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_486,B_488)
      | ~ m1_subset_1(D_484,k1_zfmisc_1(k2_zfmisc_1(B_488,'#skF_3')))
      | ~ v1_funct_2(D_484,B_488,'#skF_3')
      | ~ v1_funct_1(D_484)
      | v1_xboole_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_2756])).

tff(c_2777,plain,(
    ! [B_494,D_495,F_496] :
      ( k1_funct_1(k8_funct_2(B_494,'#skF_3','#skF_1',D_495,'#skF_5'),F_496) = k1_funct_1('#skF_5',k1_funct_1(D_495,F_496))
      | k1_xboole_0 = B_494
      | ~ r1_tarski(k2_relset_1(B_494,'#skF_3',D_495),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_496,B_494)
      | ~ m1_subset_1(D_495,k1_zfmisc_1(k2_zfmisc_1(B_494,'#skF_3')))
      | ~ v1_funct_2(D_495,B_494,'#skF_3')
      | ~ v1_funct_1(D_495) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_2760])).

tff(c_2779,plain,(
    ! [F_496] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_496) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_496))
      | k1_xboole_0 = '#skF_2'
      | ~ m1_subset_1(F_496,'#skF_2')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_189,c_2777])).

tff(c_2782,plain,(
    ! [F_496] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_496) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_496))
      | k1_xboole_0 = '#skF_2'
      | ~ m1_subset_1(F_496,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_2779])).

tff(c_2783,plain,(
    ! [F_496] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_496) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_496))
      | ~ m1_subset_1(F_496,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_2782])).

tff(c_79,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_91,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_79])).

tff(c_104,plain,(
    ! [C_70,B_71,A_72] :
      ( v5_relat_1(C_70,B_71)
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_72,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_116,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_104])).

tff(c_209,plain,(
    ! [A_99,B_100,C_101] :
      ( k7_partfun1(A_99,B_100,C_101) = k1_funct_1(B_100,C_101)
      | ~ r2_hidden(C_101,k1_relat_1(B_100))
      | ~ v1_funct_1(B_100)
      | ~ v5_relat_1(B_100,A_99)
      | ~ v1_relat_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2765,plain,(
    ! [A_491,B_492,A_493] :
      ( k7_partfun1(A_491,B_492,A_493) = k1_funct_1(B_492,A_493)
      | ~ v1_funct_1(B_492)
      | ~ v5_relat_1(B_492,A_491)
      | ~ v1_relat_1(B_492)
      | v1_xboole_0(k1_relat_1(B_492))
      | ~ m1_subset_1(A_493,k1_relat_1(B_492)) ) ),
    inference(resolution,[status(thm)],[c_16,c_209])).

tff(c_2769,plain,(
    ! [A_493] :
      ( k7_partfun1('#skF_3','#skF_4',A_493) = k1_funct_1('#skF_4',A_493)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | v1_xboole_0(k1_relat_1('#skF_4'))
      | ~ m1_subset_1(A_493,k1_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_116,c_2765])).

tff(c_2776,plain,(
    ! [A_493] :
      ( k7_partfun1('#skF_3','#skF_4',A_493) = k1_funct_1('#skF_4',A_493)
      | v1_xboole_0(k1_relat_1('#skF_4'))
      | ~ m1_subset_1(A_493,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_46,c_2769])).

tff(c_2785,plain,(
    v1_xboole_0(k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_2776])).

tff(c_26,plain,(
    ! [A_41] :
      ( k1_xboole_0 = A_41
      | ~ v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2789,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2785,c_26])).

tff(c_183,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_171])).

tff(c_2758,plain,(
    ! [B_488,D_484,F_486] :
      ( k1_funct_1(k8_funct_2(B_488,'#skF_2','#skF_3',D_484,'#skF_4'),F_486) = k1_funct_1('#skF_4',k1_funct_1(D_484,F_486))
      | k1_xboole_0 = B_488
      | ~ r1_tarski(k2_relset_1(B_488,'#skF_2',D_484),k1_relat_1('#skF_4'))
      | ~ m1_subset_1(F_486,B_488)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(D_484,k1_zfmisc_1(k2_zfmisc_1(B_488,'#skF_2')))
      | ~ v1_funct_2(D_484,B_488,'#skF_2')
      | ~ v1_funct_1(D_484)
      | v1_xboole_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_2754])).

tff(c_2763,plain,(
    ! [B_488,D_484,F_486] :
      ( k1_funct_1(k8_funct_2(B_488,'#skF_2','#skF_3',D_484,'#skF_4'),F_486) = k1_funct_1('#skF_4',k1_funct_1(D_484,F_486))
      | k1_xboole_0 = B_488
      | ~ r1_tarski(k2_relset_1(B_488,'#skF_2',D_484),k1_relat_1('#skF_4'))
      | ~ m1_subset_1(F_486,B_488)
      | ~ m1_subset_1(D_484,k1_zfmisc_1(k2_zfmisc_1(B_488,'#skF_2')))
      | ~ v1_funct_2(D_484,B_488,'#skF_2')
      | ~ v1_funct_1(D_484)
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42,c_2758])).

tff(c_2862,plain,(
    ! [B_488,D_484,F_486] :
      ( k1_funct_1(k8_funct_2(B_488,'#skF_2','#skF_3',D_484,'#skF_4'),F_486) = k1_funct_1('#skF_4',k1_funct_1(D_484,F_486))
      | k1_xboole_0 = B_488
      | ~ r1_tarski(k2_relset_1(B_488,'#skF_2',D_484),k1_xboole_0)
      | ~ m1_subset_1(F_486,B_488)
      | ~ m1_subset_1(D_484,k1_zfmisc_1(k2_zfmisc_1(B_488,'#skF_2')))
      | ~ v1_funct_2(D_484,B_488,'#skF_2')
      | ~ v1_funct_1(D_484)
      | v1_xboole_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2789,c_2763])).

tff(c_2863,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2862])).

tff(c_2866,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2863,c_26])).

tff(c_2870,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_2866])).

tff(c_2872,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2862])).

tff(c_2409,plain,(
    ! [D_430,C_431,A_432,B_433] :
      ( r2_hidden(k1_funct_1(D_430,C_431),k2_relset_1(A_432,B_433,D_430))
      | k1_xboole_0 = B_433
      | ~ r2_hidden(C_431,A_432)
      | ~ m1_subset_1(D_430,k1_zfmisc_1(k2_zfmisc_1(A_432,B_433)))
      | ~ v1_funct_2(D_430,A_432,B_433)
      | ~ v1_funct_1(D_430) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_20,plain,(
    ! [A_33,B_34] :
      ( m1_subset_1(A_33,k1_zfmisc_1(B_34))
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_159,plain,(
    ! [A_85,C_86,B_87] :
      ( m1_subset_1(A_85,C_86)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(C_86))
      | ~ r2_hidden(A_85,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_166,plain,(
    ! [A_85,B_34,A_33] :
      ( m1_subset_1(A_85,B_34)
      | ~ r2_hidden(A_85,A_33)
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(resolution,[status(thm)],[c_20,c_159])).

tff(c_2833,plain,(
    ! [C_507,A_510,B_508,D_506,B_509] :
      ( m1_subset_1(k1_funct_1(D_506,C_507),B_509)
      | ~ r1_tarski(k2_relset_1(A_510,B_508,D_506),B_509)
      | k1_xboole_0 = B_508
      | ~ r2_hidden(C_507,A_510)
      | ~ m1_subset_1(D_506,k1_zfmisc_1(k2_zfmisc_1(A_510,B_508)))
      | ~ v1_funct_2(D_506,A_510,B_508)
      | ~ v1_funct_1(D_506) ) ),
    inference(resolution,[status(thm)],[c_2409,c_166])).

tff(c_2835,plain,(
    ! [C_507] :
      ( m1_subset_1(k1_funct_1('#skF_4',C_507),k1_relat_1('#skF_5'))
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_507,'#skF_2')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_189,c_2833])).

tff(c_2838,plain,(
    ! [C_507] :
      ( m1_subset_1(k1_funct_1('#skF_4',C_507),k1_relat_1('#skF_5'))
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_507,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_2835])).

tff(c_2840,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2838])).

tff(c_2849,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2840,c_54])).

tff(c_2854,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_2849])).

tff(c_2857,plain,(
    ! [C_511] :
      ( m1_subset_1(k1_funct_1('#skF_4',C_511),k1_relat_1('#skF_5'))
      | ~ r2_hidden(C_511,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_2838])).

tff(c_118,plain,(
    ! [C_73,B_74,A_75] :
      ( ~ v1_xboole_0(C_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(C_73))
      | ~ r2_hidden(A_75,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_130,plain,(
    ! [B_76,A_77,A_78] :
      ( ~ v1_xboole_0(B_76)
      | ~ r2_hidden(A_77,A_78)
      | ~ r1_tarski(A_78,B_76) ) ),
    inference(resolution,[status(thm)],[c_20,c_118])).

tff(c_214,plain,(
    ! [B_102,B_103,A_104] :
      ( ~ v1_xboole_0(B_102)
      | ~ r1_tarski(B_103,B_102)
      | v1_xboole_0(B_103)
      | ~ m1_subset_1(A_104,B_103) ) ),
    inference(resolution,[status(thm)],[c_16,c_130])).

tff(c_221,plain,(
    ! [A_104] :
      ( ~ v1_xboole_0(k1_relat_1('#skF_5'))
      | v1_xboole_0(k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(A_104,k2_relset_1('#skF_2','#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_189,c_214])).

tff(c_2416,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_92,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_79])).

tff(c_117,plain,(
    v5_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_104])).

tff(c_2767,plain,(
    ! [A_493] :
      ( k7_partfun1('#skF_1','#skF_5',A_493) = k1_funct_1('#skF_5',A_493)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | v1_xboole_0(k1_relat_1('#skF_5'))
      | ~ m1_subset_1(A_493,k1_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_117,c_2765])).

tff(c_2772,plain,(
    ! [A_493] :
      ( k7_partfun1('#skF_1','#skF_5',A_493) = k1_funct_1('#skF_5',A_493)
      | v1_xboole_0(k1_relat_1('#skF_5'))
      | ~ m1_subset_1(A_493,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_40,c_2767])).

tff(c_2773,plain,(
    ! [A_493] :
      ( k7_partfun1('#skF_1','#skF_5',A_493) = k1_funct_1('#skF_5',A_493)
      | ~ m1_subset_1(A_493,k1_relat_1('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2416,c_2772])).

tff(c_2873,plain,(
    ! [C_512] :
      ( k7_partfun1('#skF_1','#skF_5',k1_funct_1('#skF_4',C_512)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',C_512))
      | ~ r2_hidden(C_512,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_2857,c_2773])).

tff(c_30,plain,(
    k7_partfun1('#skF_1','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_2879,plain,
    ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ r2_hidden('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2873,c_30])).

tff(c_2885,plain,(
    ~ r2_hidden('#skF_6','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2879])).

tff(c_2888,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_2885])).

tff(c_2891,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2888])).

tff(c_2893,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2872,c_2891])).

tff(c_2894,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_2879])).

tff(c_2906,plain,(
    ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2783,c_2894])).

tff(c_2910,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2906])).

tff(c_2912,plain,(
    v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_2926,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2912,c_26])).

tff(c_2928,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2926,c_189])).

tff(c_125,plain,(
    ! [B_34,A_75,A_33] :
      ( ~ v1_xboole_0(B_34)
      | ~ r2_hidden(A_75,A_33)
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(resolution,[status(thm)],[c_20,c_118])).

tff(c_3031,plain,(
    ! [D_533,B_536,B_535,A_537,C_534] :
      ( ~ v1_xboole_0(B_536)
      | ~ r1_tarski(k2_relset_1(A_537,B_535,D_533),B_536)
      | k1_xboole_0 = B_535
      | ~ r2_hidden(C_534,A_537)
      | ~ m1_subset_1(D_533,k1_zfmisc_1(k2_zfmisc_1(A_537,B_535)))
      | ~ v1_funct_2(D_533,A_537,B_535)
      | ~ v1_funct_1(D_533) ) ),
    inference(resolution,[status(thm)],[c_2409,c_125])).

tff(c_3033,plain,(
    ! [C_534] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_534,'#skF_2')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2928,c_3031])).

tff(c_3036,plain,(
    ! [C_534] :
      ( k1_xboole_0 = '#skF_3'
      | ~ r2_hidden(C_534,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_54,c_3033])).

tff(c_3044,plain,(
    ! [C_543] : ~ r2_hidden(C_543,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3036])).

tff(c_3049,plain,(
    ! [A_31] :
      ( v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_31,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_3044])).

tff(c_3050,plain,(
    ! [A_31] : ~ m1_subset_1(A_31,'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_3049])).

tff(c_3053,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3050,c_36])).

tff(c_3054,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3049])).

tff(c_3057,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_3054,c_26])).

tff(c_3061,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_3057])).

tff(c_3062,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3036])).

tff(c_3075,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3062,c_54])).

tff(c_3080,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_3075])).

%------------------------------------------------------------------------------
