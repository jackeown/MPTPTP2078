%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:08 EST 2020

% Result     : Theorem 7.08s
% Output     : CNFRefutation 7.36s
% Verified   : 
% Statistics : Number of formulae       :  198 (13716 expanded)
%              Number of leaves         :   43 (4770 expanded)
%              Depth                    :   26
%              Number of atoms          :  547 (59319 expanded)
%              Number of equality atoms :  185 (21706 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_225,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( ( k2_relset_1(A,B,C) = B
                & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
                & v2_funct_1(C) )
             => ( A = k1_xboole_0
                | B = k1_xboole_0
                | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_138,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_140,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_116,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_114,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_128,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_37,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(B) = k1_relat_1(A)
              & k5_relat_1(B,A) = k6_relat_1(k2_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_199,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_157,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
           => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_183,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
              & k2_relset_1(A,B,D) = B )
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | ( v2_funct_1(D)
                & v2_funct_1(E) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

tff(f_98,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(c_64,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_86,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_74,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_82,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_205,plain,(
    ! [A_69,B_70,C_71] :
      ( k2_relset_1(A_69,B_70,C_71) = k2_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_211,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_205])).

tff(c_218,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_211])).

tff(c_80,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_76,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_373,plain,(
    ! [D_100,B_99,F_95,E_96,C_98,A_97] :
      ( k1_partfun1(A_97,B_99,C_98,D_100,E_96,F_95) = k5_relat_1(E_96,F_95)
      | ~ m1_subset_1(F_95,k1_zfmisc_1(k2_zfmisc_1(C_98,D_100)))
      | ~ v1_funct_1(F_95)
      | ~ m1_subset_1(E_96,k1_zfmisc_1(k2_zfmisc_1(A_97,B_99)))
      | ~ v1_funct_1(E_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_379,plain,(
    ! [A_97,B_99,E_96] :
      ( k1_partfun1(A_97,B_99,'#skF_2','#skF_1',E_96,'#skF_4') = k5_relat_1(E_96,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_96,k1_zfmisc_1(k2_zfmisc_1(A_97,B_99)))
      | ~ v1_funct_1(E_96) ) ),
    inference(resolution,[status(thm)],[c_76,c_373])).

tff(c_418,plain,(
    ! [A_107,B_108,E_109] :
      ( k1_partfun1(A_107,B_108,'#skF_2','#skF_1',E_109,'#skF_4') = k5_relat_1(E_109,'#skF_4')
      | ~ m1_subset_1(E_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108)))
      | ~ v1_funct_1(E_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_379])).

tff(c_424,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_418])).

tff(c_431,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_424])).

tff(c_48,plain,(
    ! [A_34] : k6_relat_1(A_34) = k6_partfun1(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_40,plain,(
    ! [A_21] : m1_subset_1(k6_relat_1(A_21),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_87,plain,(
    ! [A_21] : m1_subset_1(k6_partfun1(A_21),k1_zfmisc_1(k2_zfmisc_1(A_21,A_21))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40])).

tff(c_72,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_261,plain,(
    ! [D_75,C_76,A_77,B_78] :
      ( D_75 = C_76
      | ~ r2_relset_1(A_77,B_78,C_76,D_75)
      | ~ m1_subset_1(D_75,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78)))
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_269,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_72,c_261])).

tff(c_284,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_269])).

tff(c_285,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_284])).

tff(c_478,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_285])).

tff(c_547,plain,(
    ! [E_121,A_119,D_123,B_124,C_120,F_122] :
      ( m1_subset_1(k1_partfun1(A_119,B_124,C_120,D_123,E_121,F_122),k1_zfmisc_1(k2_zfmisc_1(A_119,D_123)))
      | ~ m1_subset_1(F_122,k1_zfmisc_1(k2_zfmisc_1(C_120,D_123)))
      | ~ v1_funct_1(F_122)
      | ~ m1_subset_1(E_121,k1_zfmisc_1(k2_zfmisc_1(A_119,B_124)))
      | ~ v1_funct_1(E_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_581,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_547])).

tff(c_602,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_82,c_80,c_76,c_581])).

tff(c_604,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_478,c_602])).

tff(c_605,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_284])).

tff(c_2673,plain,(
    ! [C_334,A_333,F_331,D_336,B_335,E_332] :
      ( k1_partfun1(A_333,B_335,C_334,D_336,E_332,F_331) = k5_relat_1(E_332,F_331)
      | ~ m1_subset_1(F_331,k1_zfmisc_1(k2_zfmisc_1(C_334,D_336)))
      | ~ v1_funct_1(F_331)
      | ~ m1_subset_1(E_332,k1_zfmisc_1(k2_zfmisc_1(A_333,B_335)))
      | ~ v1_funct_1(E_332) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_2679,plain,(
    ! [A_333,B_335,E_332] :
      ( k1_partfun1(A_333,B_335,'#skF_2','#skF_1',E_332,'#skF_4') = k5_relat_1(E_332,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_332,k1_zfmisc_1(k2_zfmisc_1(A_333,B_335)))
      | ~ v1_funct_1(E_332) ) ),
    inference(resolution,[status(thm)],[c_76,c_2673])).

tff(c_2986,plain,(
    ! [A_361,B_362,E_363] :
      ( k1_partfun1(A_361,B_362,'#skF_2','#skF_1',E_363,'#skF_4') = k5_relat_1(E_363,'#skF_4')
      | ~ m1_subset_1(E_363,k1_zfmisc_1(k2_zfmisc_1(A_361,B_362)))
      | ~ v1_funct_1(E_363) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2679])).

tff(c_2992,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_2986])).

tff(c_2999,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_605,c_2992])).

tff(c_129,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_141,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_129])).

tff(c_142,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_129])).

tff(c_8,plain,(
    ! [A_2] :
      ( v1_relat_1(k2_funct_1(A_2))
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_654,plain,(
    ! [D_133,C_130,E_131,F_132,A_129,B_134] :
      ( v1_funct_1(k1_partfun1(A_129,B_134,C_130,D_133,E_131,F_132))
      | ~ m1_subset_1(F_132,k1_zfmisc_1(k2_zfmisc_1(C_130,D_133)))
      | ~ v1_funct_1(F_132)
      | ~ m1_subset_1(E_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_134)))
      | ~ v1_funct_1(E_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_660,plain,(
    ! [A_129,B_134,E_131] :
      ( v1_funct_1(k1_partfun1(A_129,B_134,'#skF_2','#skF_1',E_131,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_134)))
      | ~ v1_funct_1(E_131) ) ),
    inference(resolution,[status(thm)],[c_76,c_654])).

tff(c_685,plain,(
    ! [A_138,B_139,E_140] :
      ( v1_funct_1(k1_partfun1(A_138,B_139,'#skF_2','#skF_1',E_140,'#skF_4'))
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139)))
      | ~ v1_funct_1(E_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_660])).

tff(c_691,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_685])).

tff(c_698,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_605,c_691])).

tff(c_4,plain,(
    ! [A_1] : k2_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_91,plain,(
    ! [A_1] : k2_relat_1(k6_partfun1(A_1)) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_4])).

tff(c_10,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_90,plain,(
    ! [A_3] : v1_relat_1(k6_partfun1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_10])).

tff(c_70,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_28,plain,(
    ! [A_7,B_9] :
      ( k2_funct_1(A_7) = B_9
      | k6_relat_1(k2_relat_1(A_7)) != k5_relat_1(B_9,A_7)
      | k2_relat_1(B_9) != k1_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_614,plain,(
    ! [A_125,B_126] :
      ( k2_funct_1(A_125) = B_126
      | k6_partfun1(k2_relat_1(A_125)) != k5_relat_1(B_126,A_125)
      | k2_relat_1(B_126) != k1_relat_1(A_125)
      | ~ v2_funct_1(A_125)
      | ~ v1_funct_1(B_126)
      | ~ v1_relat_1(B_126)
      | ~ v1_funct_1(A_125)
      | ~ v1_relat_1(A_125) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_28])).

tff(c_618,plain,(
    ! [B_126] :
      ( k2_funct_1('#skF_3') = B_126
      | k5_relat_1(B_126,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_126) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_126)
      | ~ v1_relat_1(B_126)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_614])).

tff(c_627,plain,(
    ! [B_127] :
      ( k2_funct_1('#skF_3') = B_127
      | k5_relat_1(B_127,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_127) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_127)
      | ~ v1_relat_1(B_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_86,c_70,c_618])).

tff(c_639,plain,(
    ! [A_3] :
      ( k6_partfun1(A_3) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_3),'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(k6_partfun1(A_3)) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(k6_partfun1(A_3)) ) ),
    inference(resolution,[status(thm)],[c_90,c_627])).

tff(c_649,plain,(
    ! [A_3] :
      ( k6_partfun1(A_3) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_3),'#skF_3') != k6_partfun1('#skF_2')
      | k1_relat_1('#skF_3') != A_3
      | ~ v1_funct_1(k6_partfun1(A_3)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_639])).

tff(c_705,plain,
    ( k6_partfun1('#skF_1') = k2_funct_1('#skF_3')
    | k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_698,c_649])).

tff(c_708,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_705])).

tff(c_2,plain,(
    ! [A_1] : k1_relat_1(k6_relat_1(A_1)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_92,plain,(
    ! [A_1] : k1_relat_1(k6_partfun1(A_1)) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_84,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_830,plain,(
    ! [A_160,C_161,B_162] :
      ( k6_partfun1(A_160) = k5_relat_1(C_161,k2_funct_1(C_161))
      | k1_xboole_0 = B_162
      | ~ v2_funct_1(C_161)
      | k2_relset_1(A_160,B_162,C_161) != B_162
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_160,B_162)))
      | ~ v1_funct_2(C_161,A_160,B_162)
      | ~ v1_funct_1(C_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_834,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_830])).

tff(c_842,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_74,c_70,c_834])).

tff(c_843,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_842])).

tff(c_26,plain,(
    ! [A_6] :
      ( k1_relat_1(k5_relat_1(A_6,k2_funct_1(A_6))) = k1_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_851,plain,
    ( k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_843,c_26])).

tff(c_858,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_86,c_70,c_92,c_851])).

tff(c_860,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_708,c_858])).

tff(c_862,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_705])).

tff(c_630,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_142,c_627])).

tff(c_642,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_630])).

tff(c_643,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_642])).

tff(c_650,plain,(
    k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_643])).

tff(c_865,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_862,c_650])).

tff(c_78,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_182,plain,(
    ! [A_64,B_65,D_66] :
      ( r2_relset_1(A_64,B_65,D_66,D_66)
      | ~ m1_subset_1(D_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_189,plain,(
    ! [A_21] : r2_relset_1(A_21,A_21,k6_partfun1(A_21),k6_partfun1(A_21)) ),
    inference(resolution,[status(thm)],[c_87,c_182])).

tff(c_219,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_205])).

tff(c_1575,plain,(
    ! [A_218,B_219,C_220,D_221] :
      ( k2_relset_1(A_218,B_219,C_220) = B_219
      | ~ r2_relset_1(B_219,B_219,k1_partfun1(B_219,A_218,A_218,B_219,D_221,C_220),k6_partfun1(B_219))
      | ~ m1_subset_1(D_221,k1_zfmisc_1(k2_zfmisc_1(B_219,A_218)))
      | ~ v1_funct_2(D_221,B_219,A_218)
      | ~ v1_funct_1(D_221)
      | ~ m1_subset_1(C_220,k1_zfmisc_1(k2_zfmisc_1(A_218,B_219)))
      | ~ v1_funct_2(C_220,A_218,B_219)
      | ~ v1_funct_1(C_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_1581,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_605,c_1575])).

tff(c_1585,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_86,c_84,c_82,c_189,c_219,c_1581])).

tff(c_1587,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_865,c_1585])).

tff(c_1589,plain,(
    k2_relat_1('#skF_4') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_643])).

tff(c_88,plain,(
    ! [A_7,B_9] :
      ( k2_funct_1(A_7) = B_9
      | k6_partfun1(k2_relat_1(A_7)) != k5_relat_1(B_9,A_7)
      | k2_relat_1(B_9) != k1_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_28])).

tff(c_1593,plain,(
    ! [B_9] :
      ( k2_funct_1('#skF_4') = B_9
      | k6_partfun1(k1_relat_1('#skF_3')) != k5_relat_1(B_9,'#skF_4')
      | k2_relat_1(B_9) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1589,c_88])).

tff(c_1597,plain,(
    ! [B_9] :
      ( k2_funct_1('#skF_4') = B_9
      | k6_partfun1(k1_relat_1('#skF_3')) != k5_relat_1(B_9,'#skF_4')
      | k2_relat_1(B_9) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_80,c_1593])).

tff(c_1605,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1597])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_12,plain,(
    ! [A_3] : v2_funct_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_89,plain,(
    ! [A_3] : v2_funct_1(k6_partfun1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_12])).

tff(c_2578,plain,(
    ! [D_312,C_313,A_311,B_314,E_310] :
      ( k1_xboole_0 = C_313
      | v2_funct_1(E_310)
      | k2_relset_1(A_311,B_314,D_312) != B_314
      | ~ v2_funct_1(k1_partfun1(A_311,B_314,B_314,C_313,D_312,E_310))
      | ~ m1_subset_1(E_310,k1_zfmisc_1(k2_zfmisc_1(B_314,C_313)))
      | ~ v1_funct_2(E_310,B_314,C_313)
      | ~ v1_funct_1(E_310)
      | ~ m1_subset_1(D_312,k1_zfmisc_1(k2_zfmisc_1(A_311,B_314)))
      | ~ v1_funct_2(D_312,A_311,B_314)
      | ~ v1_funct_1(D_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_183])).

tff(c_2586,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_605,c_2578])).

tff(c_2597,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_82,c_80,c_78,c_76,c_89,c_74,c_2586])).

tff(c_2599,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1605,c_68,c_2597])).

tff(c_2601,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1597])).

tff(c_2642,plain,(
    ! [C_323,B_327,F_325,E_324,D_326,A_322] :
      ( v1_funct_1(k1_partfun1(A_322,B_327,C_323,D_326,E_324,F_325))
      | ~ m1_subset_1(F_325,k1_zfmisc_1(k2_zfmisc_1(C_323,D_326)))
      | ~ v1_funct_1(F_325)
      | ~ m1_subset_1(E_324,k1_zfmisc_1(k2_zfmisc_1(A_322,B_327)))
      | ~ v1_funct_1(E_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_2648,plain,(
    ! [A_322,B_327,E_324] :
      ( v1_funct_1(k1_partfun1(A_322,B_327,'#skF_2','#skF_1',E_324,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_324,k1_zfmisc_1(k2_zfmisc_1(A_322,B_327)))
      | ~ v1_funct_1(E_324) ) ),
    inference(resolution,[status(thm)],[c_76,c_2642])).

tff(c_2688,plain,(
    ! [A_338,B_339,E_340] :
      ( v1_funct_1(k1_partfun1(A_338,B_339,'#skF_2','#skF_1',E_340,'#skF_4'))
      | ~ m1_subset_1(E_340,k1_zfmisc_1(k2_zfmisc_1(A_338,B_339)))
      | ~ v1_funct_1(E_340) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2648])).

tff(c_2694,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_2688])).

tff(c_2701,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_605,c_2694])).

tff(c_2708,plain,
    ( k6_partfun1('#skF_1') = k2_funct_1('#skF_3')
    | k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_2701,c_649])).

tff(c_2710,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2708])).

tff(c_2857,plain,(
    ! [A_352,C_353,B_354] :
      ( k6_partfun1(A_352) = k5_relat_1(C_353,k2_funct_1(C_353))
      | k1_xboole_0 = B_354
      | ~ v2_funct_1(C_353)
      | k2_relset_1(A_352,B_354,C_353) != B_354
      | ~ m1_subset_1(C_353,k1_zfmisc_1(k2_zfmisc_1(A_352,B_354)))
      | ~ v1_funct_2(C_353,A_352,B_354)
      | ~ v1_funct_1(C_353) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_2861,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_82,c_2857])).

tff(c_2869,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_74,c_70,c_2861])).

tff(c_2870,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2869])).

tff(c_2878,plain,
    ( k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2870,c_26])).

tff(c_2885,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_86,c_70,c_92,c_2878])).

tff(c_2887,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2710,c_2885])).

tff(c_2889,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2708])).

tff(c_1590,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1589,c_219])).

tff(c_2894,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2889,c_1590])).

tff(c_3017,plain,(
    ! [B_364,C_365,A_366] :
      ( k6_partfun1(B_364) = k5_relat_1(k2_funct_1(C_365),C_365)
      | k1_xboole_0 = B_364
      | ~ v2_funct_1(C_365)
      | k2_relset_1(A_366,B_364,C_365) != B_364
      | ~ m1_subset_1(C_365,k1_zfmisc_1(k2_zfmisc_1(A_366,B_364)))
      | ~ v1_funct_2(C_365,A_366,B_364)
      | ~ v1_funct_1(C_365) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_3023,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_3017])).

tff(c_3033,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_2894,c_2601,c_3023])).

tff(c_3034,plain,(
    k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_3033])).

tff(c_30,plain,(
    ! [A_10] :
      ( k2_funct_1(k2_funct_1(A_10)) = A_10
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_237,plain,(
    ! [A_73] :
      ( k2_relat_1(k5_relat_1(A_73,k2_funct_1(A_73))) = k1_relat_1(A_73)
      | ~ v2_funct_1(A_73)
      | ~ v1_funct_1(A_73)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_246,plain,(
    ! [A_10] :
      ( k2_relat_1(k5_relat_1(k2_funct_1(A_10),A_10)) = k1_relat_1(k2_funct_1(A_10))
      | ~ v2_funct_1(k2_funct_1(A_10))
      | ~ v1_funct_1(k2_funct_1(A_10))
      | ~ v1_relat_1(k2_funct_1(A_10))
      | ~ v2_funct_1(A_10)
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_237])).

tff(c_3060,plain,
    ( k2_relat_1(k6_partfun1('#skF_1')) = k1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3034,c_246])).

tff(c_3068,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) = '#skF_1'
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_80,c_2601,c_91,c_3060])).

tff(c_3404,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3068])).

tff(c_3407,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_3404])).

tff(c_3411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_80,c_3407])).

tff(c_3413,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3068])).

tff(c_6,plain,(
    ! [A_2] :
      ( v1_funct_1(k2_funct_1(A_2))
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_4] :
      ( v2_funct_1(k2_funct_1(A_4))
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3412,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | k1_relat_1(k2_funct_1('#skF_4')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3068])).

tff(c_3425,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3412])).

tff(c_3428,plain,
    ( ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_3425])).

tff(c_3432,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_80,c_2601,c_3428])).

tff(c_3433,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_4'))
    | k1_relat_1(k2_funct_1('#skF_4')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3412])).

tff(c_3436,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_3433])).

tff(c_3439,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_3436])).

tff(c_3443,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_80,c_3439])).

tff(c_3445,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3433])).

tff(c_3434,plain,(
    v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3412])).

tff(c_3444,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3433])).

tff(c_2895,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2889,c_1589])).

tff(c_2940,plain,(
    ! [A_358,C_359,B_360] :
      ( k6_partfun1(A_358) = k5_relat_1(C_359,k2_funct_1(C_359))
      | k1_xboole_0 = B_360
      | ~ v2_funct_1(C_359)
      | k2_relset_1(A_358,B_360,C_359) != B_360
      | ~ m1_subset_1(C_359,k1_zfmisc_1(k2_zfmisc_1(A_358,B_360)))
      | ~ v1_funct_2(C_359,A_358,B_360)
      | ~ v1_funct_1(C_359) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_2946,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_76,c_2940])).

tff(c_2956,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_2894,c_2601,c_2946])).

tff(c_2957,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_2956])).

tff(c_2975,plain,
    ( k1_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2957,c_26])).

tff(c_2982,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_80,c_2601,c_92,c_2975])).

tff(c_20,plain,(
    ! [A_5] :
      ( k2_relat_1(k2_funct_1(A_5)) = k1_relat_1(A_5)
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4387,plain,(
    ! [A_429,B_430] :
      ( k2_funct_1(k2_funct_1(A_429)) = B_430
      | k5_relat_1(B_430,k2_funct_1(A_429)) != k6_partfun1(k1_relat_1(A_429))
      | k2_relat_1(B_430) != k1_relat_1(k2_funct_1(A_429))
      | ~ v2_funct_1(k2_funct_1(A_429))
      | ~ v1_funct_1(B_430)
      | ~ v1_relat_1(B_430)
      | ~ v1_funct_1(k2_funct_1(A_429))
      | ~ v1_relat_1(k2_funct_1(A_429))
      | ~ v2_funct_1(A_429)
      | ~ v1_funct_1(A_429)
      | ~ v1_relat_1(A_429) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_614])).

tff(c_4389,plain,
    ( k2_funct_1(k2_funct_1('#skF_4')) = '#skF_4'
    | k6_partfun1(k1_relat_1('#skF_4')) != k6_partfun1('#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != k2_relat_1('#skF_4')
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2957,c_4387])).

tff(c_4395,plain,(
    k2_funct_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_80,c_2601,c_3413,c_3445,c_142,c_80,c_3434,c_3444,c_2895,c_2982,c_4389])).

tff(c_620,plain,(
    ! [A_5,B_126] :
      ( k2_funct_1(k2_funct_1(A_5)) = B_126
      | k5_relat_1(B_126,k2_funct_1(A_5)) != k6_partfun1(k1_relat_1(A_5))
      | k2_relat_1(B_126) != k1_relat_1(k2_funct_1(A_5))
      | ~ v2_funct_1(k2_funct_1(A_5))
      | ~ v1_funct_1(B_126)
      | ~ v1_relat_1(B_126)
      | ~ v1_funct_1(k2_funct_1(A_5))
      | ~ v1_relat_1(k2_funct_1(A_5))
      | ~ v2_funct_1(A_5)
      | ~ v1_funct_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_614])).

tff(c_4471,plain,(
    ! [B_126] :
      ( k2_funct_1(k2_funct_1(k2_funct_1('#skF_4'))) = B_126
      | k6_partfun1(k1_relat_1(k2_funct_1('#skF_4'))) != k5_relat_1(B_126,'#skF_4')
      | k2_relat_1(B_126) != k1_relat_1(k2_funct_1(k2_funct_1('#skF_4')))
      | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_4')))
      | ~ v1_funct_1(B_126)
      | ~ v1_relat_1(B_126)
      | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_4')))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_4')))
      | ~ v2_funct_1(k2_funct_1('#skF_4'))
      | ~ v1_funct_1(k2_funct_1('#skF_4'))
      | ~ v1_relat_1(k2_funct_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4395,c_620])).

tff(c_5096,plain,(
    ! [B_457] :
      ( k2_funct_1('#skF_4') = B_457
      | k5_relat_1(B_457,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_457) != '#skF_2'
      | ~ v1_funct_1(B_457)
      | ~ v1_relat_1(B_457) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3413,c_3445,c_3434,c_142,c_4395,c_80,c_4395,c_2601,c_4395,c_2982,c_4395,c_3444,c_4395,c_4471])).

tff(c_5141,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_141,c_5096])).

tff(c_5193,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_218,c_2999,c_5141])).

tff(c_5199,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5193,c_4395])).

tff(c_5208,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_5199])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:18:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.08/2.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.08/2.50  
% 7.08/2.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.08/2.50  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.08/2.50  
% 7.08/2.50  %Foreground sorts:
% 7.08/2.50  
% 7.08/2.50  
% 7.08/2.50  %Background operators:
% 7.08/2.50  
% 7.08/2.50  
% 7.08/2.50  %Foreground operators:
% 7.08/2.50  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.08/2.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.08/2.50  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.08/2.50  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.08/2.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.08/2.50  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.08/2.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.08/2.50  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.08/2.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.08/2.50  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.08/2.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.08/2.50  tff('#skF_2', type, '#skF_2': $i).
% 7.08/2.50  tff('#skF_3', type, '#skF_3': $i).
% 7.08/2.50  tff('#skF_1', type, '#skF_1': $i).
% 7.08/2.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.08/2.50  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.08/2.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.08/2.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.08/2.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.08/2.50  tff('#skF_4', type, '#skF_4': $i).
% 7.08/2.50  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.08/2.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.08/2.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.08/2.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.08/2.50  
% 7.36/2.53  tff(f_225, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 7.36/2.53  tff(f_106, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.36/2.53  tff(f_138, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.36/2.53  tff(f_140, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.36/2.53  tff(f_116, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_relset_1)).
% 7.36/2.53  tff(f_114, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.36/2.53  tff(f_128, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.36/2.53  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.36/2.53  tff(f_37, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 7.36/2.53  tff(f_29, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 7.36/2.53  tff(f_41, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 7.36/2.53  tff(f_90, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 7.36/2.53  tff(f_199, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 7.36/2.53  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_funct_1)).
% 7.36/2.53  tff(f_157, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 7.36/2.53  tff(f_183, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 7.36/2.53  tff(f_98, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_funct_1)).
% 7.36/2.53  tff(f_53, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 7.36/2.53  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 7.36/2.53  tff(c_64, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.36/2.53  tff(c_86, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.36/2.53  tff(c_74, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.36/2.53  tff(c_82, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.36/2.53  tff(c_205, plain, (![A_69, B_70, C_71]: (k2_relset_1(A_69, B_70, C_71)=k2_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.36/2.53  tff(c_211, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_205])).
% 7.36/2.53  tff(c_218, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_211])).
% 7.36/2.53  tff(c_80, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.36/2.53  tff(c_76, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.36/2.53  tff(c_373, plain, (![D_100, B_99, F_95, E_96, C_98, A_97]: (k1_partfun1(A_97, B_99, C_98, D_100, E_96, F_95)=k5_relat_1(E_96, F_95) | ~m1_subset_1(F_95, k1_zfmisc_1(k2_zfmisc_1(C_98, D_100))) | ~v1_funct_1(F_95) | ~m1_subset_1(E_96, k1_zfmisc_1(k2_zfmisc_1(A_97, B_99))) | ~v1_funct_1(E_96))), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.36/2.53  tff(c_379, plain, (![A_97, B_99, E_96]: (k1_partfun1(A_97, B_99, '#skF_2', '#skF_1', E_96, '#skF_4')=k5_relat_1(E_96, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_96, k1_zfmisc_1(k2_zfmisc_1(A_97, B_99))) | ~v1_funct_1(E_96))), inference(resolution, [status(thm)], [c_76, c_373])).
% 7.36/2.53  tff(c_418, plain, (![A_107, B_108, E_109]: (k1_partfun1(A_107, B_108, '#skF_2', '#skF_1', E_109, '#skF_4')=k5_relat_1(E_109, '#skF_4') | ~m1_subset_1(E_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))) | ~v1_funct_1(E_109))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_379])).
% 7.36/2.53  tff(c_424, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_418])).
% 7.36/2.53  tff(c_431, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_424])).
% 7.36/2.53  tff(c_48, plain, (![A_34]: (k6_relat_1(A_34)=k6_partfun1(A_34))), inference(cnfTransformation, [status(thm)], [f_140])).
% 7.36/2.53  tff(c_40, plain, (![A_21]: (m1_subset_1(k6_relat_1(A_21), k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.36/2.53  tff(c_87, plain, (![A_21]: (m1_subset_1(k6_partfun1(A_21), k1_zfmisc_1(k2_zfmisc_1(A_21, A_21))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40])).
% 7.36/2.53  tff(c_72, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.36/2.53  tff(c_261, plain, (![D_75, C_76, A_77, B_78]: (D_75=C_76 | ~r2_relset_1(A_77, B_78, C_76, D_75) | ~m1_subset_1(D_75, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.36/2.53  tff(c_269, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_72, c_261])).
% 7.36/2.53  tff(c_284, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_269])).
% 7.36/2.53  tff(c_285, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_284])).
% 7.36/2.53  tff(c_478, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_431, c_285])).
% 7.36/2.53  tff(c_547, plain, (![E_121, A_119, D_123, B_124, C_120, F_122]: (m1_subset_1(k1_partfun1(A_119, B_124, C_120, D_123, E_121, F_122), k1_zfmisc_1(k2_zfmisc_1(A_119, D_123))) | ~m1_subset_1(F_122, k1_zfmisc_1(k2_zfmisc_1(C_120, D_123))) | ~v1_funct_1(F_122) | ~m1_subset_1(E_121, k1_zfmisc_1(k2_zfmisc_1(A_119, B_124))) | ~v1_funct_1(E_121))), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.36/2.53  tff(c_581, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_431, c_547])).
% 7.36/2.53  tff(c_602, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_82, c_80, c_76, c_581])).
% 7.36/2.53  tff(c_604, plain, $false, inference(negUnitSimplification, [status(thm)], [c_478, c_602])).
% 7.36/2.53  tff(c_605, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_284])).
% 7.36/2.53  tff(c_2673, plain, (![C_334, A_333, F_331, D_336, B_335, E_332]: (k1_partfun1(A_333, B_335, C_334, D_336, E_332, F_331)=k5_relat_1(E_332, F_331) | ~m1_subset_1(F_331, k1_zfmisc_1(k2_zfmisc_1(C_334, D_336))) | ~v1_funct_1(F_331) | ~m1_subset_1(E_332, k1_zfmisc_1(k2_zfmisc_1(A_333, B_335))) | ~v1_funct_1(E_332))), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.36/2.53  tff(c_2679, plain, (![A_333, B_335, E_332]: (k1_partfun1(A_333, B_335, '#skF_2', '#skF_1', E_332, '#skF_4')=k5_relat_1(E_332, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_332, k1_zfmisc_1(k2_zfmisc_1(A_333, B_335))) | ~v1_funct_1(E_332))), inference(resolution, [status(thm)], [c_76, c_2673])).
% 7.36/2.53  tff(c_2986, plain, (![A_361, B_362, E_363]: (k1_partfun1(A_361, B_362, '#skF_2', '#skF_1', E_363, '#skF_4')=k5_relat_1(E_363, '#skF_4') | ~m1_subset_1(E_363, k1_zfmisc_1(k2_zfmisc_1(A_361, B_362))) | ~v1_funct_1(E_363))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2679])).
% 7.36/2.53  tff(c_2992, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_2986])).
% 7.36/2.53  tff(c_2999, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_605, c_2992])).
% 7.36/2.53  tff(c_129, plain, (![C_58, A_59, B_60]: (v1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.36/2.53  tff(c_141, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_129])).
% 7.36/2.53  tff(c_142, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_129])).
% 7.36/2.53  tff(c_8, plain, (![A_2]: (v1_relat_1(k2_funct_1(A_2)) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.36/2.53  tff(c_654, plain, (![D_133, C_130, E_131, F_132, A_129, B_134]: (v1_funct_1(k1_partfun1(A_129, B_134, C_130, D_133, E_131, F_132)) | ~m1_subset_1(F_132, k1_zfmisc_1(k2_zfmisc_1(C_130, D_133))) | ~v1_funct_1(F_132) | ~m1_subset_1(E_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_134))) | ~v1_funct_1(E_131))), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.36/2.53  tff(c_660, plain, (![A_129, B_134, E_131]: (v1_funct_1(k1_partfun1(A_129, B_134, '#skF_2', '#skF_1', E_131, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_134))) | ~v1_funct_1(E_131))), inference(resolution, [status(thm)], [c_76, c_654])).
% 7.36/2.53  tff(c_685, plain, (![A_138, B_139, E_140]: (v1_funct_1(k1_partfun1(A_138, B_139, '#skF_2', '#skF_1', E_140, '#skF_4')) | ~m1_subset_1(E_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))) | ~v1_funct_1(E_140))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_660])).
% 7.36/2.53  tff(c_691, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_685])).
% 7.36/2.53  tff(c_698, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_605, c_691])).
% 7.36/2.53  tff(c_4, plain, (![A_1]: (k2_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.36/2.53  tff(c_91, plain, (![A_1]: (k2_relat_1(k6_partfun1(A_1))=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_4])).
% 7.36/2.53  tff(c_10, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.36/2.53  tff(c_90, plain, (![A_3]: (v1_relat_1(k6_partfun1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_10])).
% 7.36/2.53  tff(c_70, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.36/2.53  tff(c_28, plain, (![A_7, B_9]: (k2_funct_1(A_7)=B_9 | k6_relat_1(k2_relat_1(A_7))!=k5_relat_1(B_9, A_7) | k2_relat_1(B_9)!=k1_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.36/2.53  tff(c_614, plain, (![A_125, B_126]: (k2_funct_1(A_125)=B_126 | k6_partfun1(k2_relat_1(A_125))!=k5_relat_1(B_126, A_125) | k2_relat_1(B_126)!=k1_relat_1(A_125) | ~v2_funct_1(A_125) | ~v1_funct_1(B_126) | ~v1_relat_1(B_126) | ~v1_funct_1(A_125) | ~v1_relat_1(A_125))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_28])).
% 7.36/2.53  tff(c_618, plain, (![B_126]: (k2_funct_1('#skF_3')=B_126 | k5_relat_1(B_126, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_126)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_126) | ~v1_relat_1(B_126) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_218, c_614])).
% 7.36/2.53  tff(c_627, plain, (![B_127]: (k2_funct_1('#skF_3')=B_127 | k5_relat_1(B_127, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_127)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_127) | ~v1_relat_1(B_127))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_86, c_70, c_618])).
% 7.36/2.53  tff(c_639, plain, (![A_3]: (k6_partfun1(A_3)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_3), '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(k6_partfun1(A_3))!=k1_relat_1('#skF_3') | ~v1_funct_1(k6_partfun1(A_3)))), inference(resolution, [status(thm)], [c_90, c_627])).
% 7.36/2.53  tff(c_649, plain, (![A_3]: (k6_partfun1(A_3)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_3), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!=A_3 | ~v1_funct_1(k6_partfun1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_639])).
% 7.36/2.53  tff(c_705, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_698, c_649])).
% 7.36/2.53  tff(c_708, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_705])).
% 7.36/2.53  tff(c_2, plain, (![A_1]: (k1_relat_1(k6_relat_1(A_1))=A_1)), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.36/2.53  tff(c_92, plain, (![A_1]: (k1_relat_1(k6_partfun1(A_1))=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2])).
% 7.36/2.53  tff(c_66, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.36/2.53  tff(c_84, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.36/2.53  tff(c_830, plain, (![A_160, C_161, B_162]: (k6_partfun1(A_160)=k5_relat_1(C_161, k2_funct_1(C_161)) | k1_xboole_0=B_162 | ~v2_funct_1(C_161) | k2_relset_1(A_160, B_162, C_161)!=B_162 | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_160, B_162))) | ~v1_funct_2(C_161, A_160, B_162) | ~v1_funct_1(C_161))), inference(cnfTransformation, [status(thm)], [f_199])).
% 7.36/2.53  tff(c_834, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_830])).
% 7.36/2.53  tff(c_842, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_74, c_70, c_834])).
% 7.36/2.53  tff(c_843, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_66, c_842])).
% 7.36/2.53  tff(c_26, plain, (![A_6]: (k1_relat_1(k5_relat_1(A_6, k2_funct_1(A_6)))=k1_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.36/2.53  tff(c_851, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_843, c_26])).
% 7.36/2.53  tff(c_858, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_141, c_86, c_70, c_92, c_851])).
% 7.36/2.53  tff(c_860, plain, $false, inference(negUnitSimplification, [status(thm)], [c_708, c_858])).
% 7.36/2.53  tff(c_862, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_705])).
% 7.36/2.53  tff(c_630, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_142, c_627])).
% 7.36/2.53  tff(c_642, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_630])).
% 7.36/2.53  tff(c_643, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_64, c_642])).
% 7.36/2.53  tff(c_650, plain, (k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_643])).
% 7.36/2.53  tff(c_865, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_862, c_650])).
% 7.36/2.53  tff(c_78, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.36/2.53  tff(c_182, plain, (![A_64, B_65, D_66]: (r2_relset_1(A_64, B_65, D_66, D_66) | ~m1_subset_1(D_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_114])).
% 7.36/2.53  tff(c_189, plain, (![A_21]: (r2_relset_1(A_21, A_21, k6_partfun1(A_21), k6_partfun1(A_21)))), inference(resolution, [status(thm)], [c_87, c_182])).
% 7.36/2.53  tff(c_219, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_205])).
% 7.36/2.53  tff(c_1575, plain, (![A_218, B_219, C_220, D_221]: (k2_relset_1(A_218, B_219, C_220)=B_219 | ~r2_relset_1(B_219, B_219, k1_partfun1(B_219, A_218, A_218, B_219, D_221, C_220), k6_partfun1(B_219)) | ~m1_subset_1(D_221, k1_zfmisc_1(k2_zfmisc_1(B_219, A_218))) | ~v1_funct_2(D_221, B_219, A_218) | ~v1_funct_1(D_221) | ~m1_subset_1(C_220, k1_zfmisc_1(k2_zfmisc_1(A_218, B_219))) | ~v1_funct_2(C_220, A_218, B_219) | ~v1_funct_1(C_220))), inference(cnfTransformation, [status(thm)], [f_157])).
% 7.36/2.53  tff(c_1581, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_605, c_1575])).
% 7.36/2.53  tff(c_1585, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_86, c_84, c_82, c_189, c_219, c_1581])).
% 7.36/2.53  tff(c_1587, plain, $false, inference(negUnitSimplification, [status(thm)], [c_865, c_1585])).
% 7.36/2.53  tff(c_1589, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_643])).
% 7.36/2.53  tff(c_88, plain, (![A_7, B_9]: (k2_funct_1(A_7)=B_9 | k6_partfun1(k2_relat_1(A_7))!=k5_relat_1(B_9, A_7) | k2_relat_1(B_9)!=k1_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(B_9) | ~v1_relat_1(B_9) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_28])).
% 7.36/2.53  tff(c_1593, plain, (![B_9]: (k2_funct_1('#skF_4')=B_9 | k6_partfun1(k1_relat_1('#skF_3'))!=k5_relat_1(B_9, '#skF_4') | k2_relat_1(B_9)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_9) | ~v1_relat_1(B_9) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1589, c_88])).
% 7.36/2.53  tff(c_1597, plain, (![B_9]: (k2_funct_1('#skF_4')=B_9 | k6_partfun1(k1_relat_1('#skF_3'))!=k5_relat_1(B_9, '#skF_4') | k2_relat_1(B_9)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_9) | ~v1_relat_1(B_9))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_80, c_1593])).
% 7.36/2.53  tff(c_1605, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_1597])).
% 7.36/2.53  tff(c_68, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_225])).
% 7.36/2.53  tff(c_12, plain, (![A_3]: (v2_funct_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.36/2.53  tff(c_89, plain, (![A_3]: (v2_funct_1(k6_partfun1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_12])).
% 7.36/2.53  tff(c_2578, plain, (![D_312, C_313, A_311, B_314, E_310]: (k1_xboole_0=C_313 | v2_funct_1(E_310) | k2_relset_1(A_311, B_314, D_312)!=B_314 | ~v2_funct_1(k1_partfun1(A_311, B_314, B_314, C_313, D_312, E_310)) | ~m1_subset_1(E_310, k1_zfmisc_1(k2_zfmisc_1(B_314, C_313))) | ~v1_funct_2(E_310, B_314, C_313) | ~v1_funct_1(E_310) | ~m1_subset_1(D_312, k1_zfmisc_1(k2_zfmisc_1(A_311, B_314))) | ~v1_funct_2(D_312, A_311, B_314) | ~v1_funct_1(D_312))), inference(cnfTransformation, [status(thm)], [f_183])).
% 7.36/2.53  tff(c_2586, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_605, c_2578])).
% 7.36/2.53  tff(c_2597, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_82, c_80, c_78, c_76, c_89, c_74, c_2586])).
% 7.36/2.53  tff(c_2599, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1605, c_68, c_2597])).
% 7.36/2.53  tff(c_2601, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_1597])).
% 7.36/2.53  tff(c_2642, plain, (![C_323, B_327, F_325, E_324, D_326, A_322]: (v1_funct_1(k1_partfun1(A_322, B_327, C_323, D_326, E_324, F_325)) | ~m1_subset_1(F_325, k1_zfmisc_1(k2_zfmisc_1(C_323, D_326))) | ~v1_funct_1(F_325) | ~m1_subset_1(E_324, k1_zfmisc_1(k2_zfmisc_1(A_322, B_327))) | ~v1_funct_1(E_324))), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.36/2.53  tff(c_2648, plain, (![A_322, B_327, E_324]: (v1_funct_1(k1_partfun1(A_322, B_327, '#skF_2', '#skF_1', E_324, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_324, k1_zfmisc_1(k2_zfmisc_1(A_322, B_327))) | ~v1_funct_1(E_324))), inference(resolution, [status(thm)], [c_76, c_2642])).
% 7.36/2.53  tff(c_2688, plain, (![A_338, B_339, E_340]: (v1_funct_1(k1_partfun1(A_338, B_339, '#skF_2', '#skF_1', E_340, '#skF_4')) | ~m1_subset_1(E_340, k1_zfmisc_1(k2_zfmisc_1(A_338, B_339))) | ~v1_funct_1(E_340))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2648])).
% 7.36/2.53  tff(c_2694, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_2688])).
% 7.36/2.53  tff(c_2701, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_605, c_2694])).
% 7.36/2.53  tff(c_2708, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_2701, c_649])).
% 7.36/2.53  tff(c_2710, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2708])).
% 7.36/2.53  tff(c_2857, plain, (![A_352, C_353, B_354]: (k6_partfun1(A_352)=k5_relat_1(C_353, k2_funct_1(C_353)) | k1_xboole_0=B_354 | ~v2_funct_1(C_353) | k2_relset_1(A_352, B_354, C_353)!=B_354 | ~m1_subset_1(C_353, k1_zfmisc_1(k2_zfmisc_1(A_352, B_354))) | ~v1_funct_2(C_353, A_352, B_354) | ~v1_funct_1(C_353))), inference(cnfTransformation, [status(thm)], [f_199])).
% 7.36/2.53  tff(c_2861, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_82, c_2857])).
% 7.36/2.53  tff(c_2869, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_74, c_70, c_2861])).
% 7.36/2.53  tff(c_2870, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_66, c_2869])).
% 7.36/2.53  tff(c_2878, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2870, c_26])).
% 7.36/2.53  tff(c_2885, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_141, c_86, c_70, c_92, c_2878])).
% 7.36/2.53  tff(c_2887, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2710, c_2885])).
% 7.36/2.53  tff(c_2889, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_2708])).
% 7.36/2.53  tff(c_1590, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1589, c_219])).
% 7.36/2.53  tff(c_2894, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2889, c_1590])).
% 7.36/2.53  tff(c_3017, plain, (![B_364, C_365, A_366]: (k6_partfun1(B_364)=k5_relat_1(k2_funct_1(C_365), C_365) | k1_xboole_0=B_364 | ~v2_funct_1(C_365) | k2_relset_1(A_366, B_364, C_365)!=B_364 | ~m1_subset_1(C_365, k1_zfmisc_1(k2_zfmisc_1(A_366, B_364))) | ~v1_funct_2(C_365, A_366, B_364) | ~v1_funct_1(C_365))), inference(cnfTransformation, [status(thm)], [f_199])).
% 7.36/2.53  tff(c_3023, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_3017])).
% 7.36/2.53  tff(c_3033, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_2894, c_2601, c_3023])).
% 7.36/2.53  tff(c_3034, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_68, c_3033])).
% 7.36/2.53  tff(c_30, plain, (![A_10]: (k2_funct_1(k2_funct_1(A_10))=A_10 | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.36/2.53  tff(c_237, plain, (![A_73]: (k2_relat_1(k5_relat_1(A_73, k2_funct_1(A_73)))=k1_relat_1(A_73) | ~v2_funct_1(A_73) | ~v1_funct_1(A_73) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.36/2.53  tff(c_246, plain, (![A_10]: (k2_relat_1(k5_relat_1(k2_funct_1(A_10), A_10))=k1_relat_1(k2_funct_1(A_10)) | ~v2_funct_1(k2_funct_1(A_10)) | ~v1_funct_1(k2_funct_1(A_10)) | ~v1_relat_1(k2_funct_1(A_10)) | ~v2_funct_1(A_10) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(superposition, [status(thm), theory('equality')], [c_30, c_237])).
% 7.36/2.53  tff(c_3060, plain, (k2_relat_1(k6_partfun1('#skF_1'))=k1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3034, c_246])).
% 7.36/2.53  tff(c_3068, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_1' | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_142, c_80, c_2601, c_91, c_3060])).
% 7.36/2.53  tff(c_3404, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_3068])).
% 7.36/2.53  tff(c_3407, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8, c_3404])).
% 7.36/2.53  tff(c_3411, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_80, c_3407])).
% 7.36/2.53  tff(c_3413, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_3068])).
% 7.36/2.53  tff(c_6, plain, (![A_2]: (v1_funct_1(k2_funct_1(A_2)) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.36/2.53  tff(c_14, plain, (![A_4]: (v2_funct_1(k2_funct_1(A_4)) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.36/2.53  tff(c_3412, plain, (~v1_funct_1(k2_funct_1('#skF_4')) | ~v2_funct_1(k2_funct_1('#skF_4')) | k1_relat_1(k2_funct_1('#skF_4'))='#skF_1'), inference(splitRight, [status(thm)], [c_3068])).
% 7.36/2.53  tff(c_3425, plain, (~v2_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_3412])).
% 7.36/2.53  tff(c_3428, plain, (~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_3425])).
% 7.36/2.53  tff(c_3432, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_80, c_2601, c_3428])).
% 7.36/2.53  tff(c_3433, plain, (~v1_funct_1(k2_funct_1('#skF_4')) | k1_relat_1(k2_funct_1('#skF_4'))='#skF_1'), inference(splitRight, [status(thm)], [c_3412])).
% 7.36/2.53  tff(c_3436, plain, (~v1_funct_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_3433])).
% 7.36/2.53  tff(c_3439, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6, c_3436])).
% 7.36/2.53  tff(c_3443, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_142, c_80, c_3439])).
% 7.36/2.53  tff(c_3445, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_3433])).
% 7.36/2.53  tff(c_3434, plain, (v2_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_3412])).
% 7.36/2.53  tff(c_3444, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_1'), inference(splitRight, [status(thm)], [c_3433])).
% 7.36/2.53  tff(c_2895, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2889, c_1589])).
% 7.36/2.53  tff(c_2940, plain, (![A_358, C_359, B_360]: (k6_partfun1(A_358)=k5_relat_1(C_359, k2_funct_1(C_359)) | k1_xboole_0=B_360 | ~v2_funct_1(C_359) | k2_relset_1(A_358, B_360, C_359)!=B_360 | ~m1_subset_1(C_359, k1_zfmisc_1(k2_zfmisc_1(A_358, B_360))) | ~v1_funct_2(C_359, A_358, B_360) | ~v1_funct_1(C_359))), inference(cnfTransformation, [status(thm)], [f_199])).
% 7.36/2.53  tff(c_2946, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_76, c_2940])).
% 7.36/2.53  tff(c_2956, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_2894, c_2601, c_2946])).
% 7.36/2.53  tff(c_2957, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_68, c_2956])).
% 7.36/2.53  tff(c_2975, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2957, c_26])).
% 7.36/2.53  tff(c_2982, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_142, c_80, c_2601, c_92, c_2975])).
% 7.36/2.53  tff(c_20, plain, (![A_5]: (k2_relat_1(k2_funct_1(A_5))=k1_relat_1(A_5) | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.36/2.53  tff(c_4387, plain, (![A_429, B_430]: (k2_funct_1(k2_funct_1(A_429))=B_430 | k5_relat_1(B_430, k2_funct_1(A_429))!=k6_partfun1(k1_relat_1(A_429)) | k2_relat_1(B_430)!=k1_relat_1(k2_funct_1(A_429)) | ~v2_funct_1(k2_funct_1(A_429)) | ~v1_funct_1(B_430) | ~v1_relat_1(B_430) | ~v1_funct_1(k2_funct_1(A_429)) | ~v1_relat_1(k2_funct_1(A_429)) | ~v2_funct_1(A_429) | ~v1_funct_1(A_429) | ~v1_relat_1(A_429))), inference(superposition, [status(thm), theory('equality')], [c_20, c_614])).
% 7.36/2.53  tff(c_4389, plain, (k2_funct_1(k2_funct_1('#skF_4'))='#skF_4' | k6_partfun1(k1_relat_1('#skF_4'))!=k6_partfun1('#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!=k2_relat_1('#skF_4') | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2957, c_4387])).
% 7.36/2.53  tff(c_4395, plain, (k2_funct_1(k2_funct_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_142, c_80, c_2601, c_3413, c_3445, c_142, c_80, c_3434, c_3444, c_2895, c_2982, c_4389])).
% 7.36/2.53  tff(c_620, plain, (![A_5, B_126]: (k2_funct_1(k2_funct_1(A_5))=B_126 | k5_relat_1(B_126, k2_funct_1(A_5))!=k6_partfun1(k1_relat_1(A_5)) | k2_relat_1(B_126)!=k1_relat_1(k2_funct_1(A_5)) | ~v2_funct_1(k2_funct_1(A_5)) | ~v1_funct_1(B_126) | ~v1_relat_1(B_126) | ~v1_funct_1(k2_funct_1(A_5)) | ~v1_relat_1(k2_funct_1(A_5)) | ~v2_funct_1(A_5) | ~v1_funct_1(A_5) | ~v1_relat_1(A_5))), inference(superposition, [status(thm), theory('equality')], [c_20, c_614])).
% 7.36/2.53  tff(c_4471, plain, (![B_126]: (k2_funct_1(k2_funct_1(k2_funct_1('#skF_4')))=B_126 | k6_partfun1(k1_relat_1(k2_funct_1('#skF_4')))!=k5_relat_1(B_126, '#skF_4') | k2_relat_1(B_126)!=k1_relat_1(k2_funct_1(k2_funct_1('#skF_4'))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(B_126) | ~v1_relat_1(B_126) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_4'))) | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_4395, c_620])).
% 7.36/2.53  tff(c_5096, plain, (![B_457]: (k2_funct_1('#skF_4')=B_457 | k5_relat_1(B_457, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_457)!='#skF_2' | ~v1_funct_1(B_457) | ~v1_relat_1(B_457))), inference(demodulation, [status(thm), theory('equality')], [c_3413, c_3445, c_3434, c_142, c_4395, c_80, c_4395, c_2601, c_4395, c_2982, c_4395, c_3444, c_4395, c_4471])).
% 7.36/2.53  tff(c_5141, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_141, c_5096])).
% 7.36/2.53  tff(c_5193, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_218, c_2999, c_5141])).
% 7.36/2.53  tff(c_5199, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5193, c_4395])).
% 7.36/2.53  tff(c_5208, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_5199])).
% 7.36/2.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.36/2.53  
% 7.36/2.53  Inference rules
% 7.36/2.53  ----------------------
% 7.36/2.53  #Ref     : 0
% 7.36/2.53  #Sup     : 1083
% 7.36/2.53  #Fact    : 0
% 7.36/2.53  #Define  : 0
% 7.36/2.53  #Split   : 40
% 7.36/2.53  #Chain   : 0
% 7.36/2.53  #Close   : 0
% 7.36/2.53  
% 7.36/2.53  Ordering : KBO
% 7.36/2.53  
% 7.36/2.53  Simplification rules
% 7.36/2.53  ----------------------
% 7.36/2.53  #Subsume      : 65
% 7.36/2.53  #Demod        : 1770
% 7.36/2.53  #Tautology    : 348
% 7.36/2.53  #SimpNegUnit  : 107
% 7.36/2.53  #BackRed      : 60
% 7.36/2.53  
% 7.36/2.53  #Partial instantiations: 0
% 7.36/2.53  #Strategies tried      : 1
% 7.36/2.53  
% 7.36/2.53  Timing (in seconds)
% 7.36/2.53  ----------------------
% 7.36/2.53  Preprocessing        : 0.37
% 7.36/2.53  Parsing              : 0.20
% 7.36/2.53  CNF conversion       : 0.03
% 7.36/2.53  Main loop            : 1.31
% 7.36/2.53  Inferencing          : 0.43
% 7.36/2.53  Reduction            : 0.52
% 7.36/2.53  Demodulation         : 0.39
% 7.36/2.53  BG Simplification    : 0.05
% 7.36/2.53  Subsumption          : 0.24
% 7.36/2.53  Abstraction          : 0.06
% 7.36/2.53  MUC search           : 0.00
% 7.36/2.53  Cooper               : 0.00
% 7.36/2.53  Total                : 1.75
% 7.36/2.53  Index Insertion      : 0.00
% 7.36/2.53  Index Deletion       : 0.00
% 7.36/2.53  Index Matching       : 0.00
% 7.36/2.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
