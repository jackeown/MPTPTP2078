%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:24 EST 2020

% Result     : Theorem 13.31s
% Output     : CNFRefutation 13.31s
% Verified   : 
% Statistics : Number of formulae       :  167 (1028 expanded)
%              Number of leaves         :   43 ( 385 expanded)
%              Depth                    :   18
%              Number of atoms          :  399 (4265 expanded)
%              Number of equality atoms :  126 (1484 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_205,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_179,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_120,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_96,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_118,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_108,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_137,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_62,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_163,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

tff(f_60,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_48,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_72,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_58,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_122,plain,(
    ! [B_64,A_65] :
      ( v1_relat_1(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65))
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_131,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_70,c_122])).

tff(c_140,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_131])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_72,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_197,plain,(
    ! [A_75,B_76,C_77] :
      ( k2_relset_1(A_75,B_76,C_77) = k2_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_211,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_197])).

tff(c_17294,plain,(
    ! [B_540,C_541,A_542] :
      ( k6_partfun1(B_540) = k5_relat_1(k2_funct_1(C_541),C_541)
      | k1_xboole_0 = B_540
      | ~ v2_funct_1(C_541)
      | k2_relset_1(A_542,B_540,C_541) != B_540
      | ~ m1_subset_1(C_541,k1_zfmisc_1(k2_zfmisc_1(A_542,B_540)))
      | ~ v1_funct_2(C_541,A_542,B_540)
      | ~ v1_funct_1(C_541) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_17300,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_17294])).

tff(c_17310,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_211,c_17300])).

tff(c_17311,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_17310])).

tff(c_17363,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_17311])).

tff(c_80,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_78,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_76,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_42,plain,(
    ! [A_39] : k6_relat_1(A_39) = k6_partfun1(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_34,plain,(
    ! [A_26] : m1_subset_1(k6_relat_1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_81,plain,(
    ! [A_26] : m1_subset_1(k6_partfun1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_34])).

tff(c_177,plain,(
    ! [A_70,B_71,D_72] :
      ( r2_relset_1(A_70,B_71,D_72,D_72)
      | ~ m1_subset_1(D_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_184,plain,(
    ! [A_26] : r2_relset_1(A_26,A_26,k6_partfun1(A_26),k6_partfun1(A_26)) ),
    inference(resolution,[status(thm)],[c_81,c_177])).

tff(c_1033,plain,(
    ! [E_119,D_122,F_121,A_118,C_120,B_123] :
      ( k1_partfun1(A_118,B_123,C_120,D_122,E_119,F_121) = k5_relat_1(E_119,F_121)
      | ~ m1_subset_1(F_121,k1_zfmisc_1(k2_zfmisc_1(C_120,D_122)))
      | ~ v1_funct_1(F_121)
      | ~ m1_subset_1(E_119,k1_zfmisc_1(k2_zfmisc_1(A_118,B_123)))
      | ~ v1_funct_1(E_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1039,plain,(
    ! [A_118,B_123,E_119] :
      ( k1_partfun1(A_118,B_123,'#skF_2','#skF_1',E_119,'#skF_4') = k5_relat_1(E_119,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_119,k1_zfmisc_1(k2_zfmisc_1(A_118,B_123)))
      | ~ v1_funct_1(E_119) ) ),
    inference(resolution,[status(thm)],[c_70,c_1033])).

tff(c_1075,plain,(
    ! [A_128,B_129,E_130] :
      ( k1_partfun1(A_128,B_129,'#skF_2','#skF_1',E_130,'#skF_4') = k5_relat_1(E_130,'#skF_4')
      | ~ m1_subset_1(E_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129)))
      | ~ v1_funct_1(E_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1039])).

tff(c_1081,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_1075])).

tff(c_1088,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1081])).

tff(c_66,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_490,plain,(
    ! [D_91,C_92,A_93,B_94] :
      ( D_91 = C_92
      | ~ r2_relset_1(A_93,B_94,C_92,D_91)
      | ~ m1_subset_1(D_91,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94)))
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_498,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_66,c_490])).

tff(c_513,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_498])).

tff(c_644,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_513])).

tff(c_1093,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1088,c_644])).

tff(c_1488,plain,(
    ! [C_143,D_144,F_142,E_145,B_146,A_147] :
      ( m1_subset_1(k1_partfun1(A_147,B_146,C_143,D_144,E_145,F_142),k1_zfmisc_1(k2_zfmisc_1(A_147,D_144)))
      | ~ m1_subset_1(F_142,k1_zfmisc_1(k2_zfmisc_1(C_143,D_144)))
      | ~ v1_funct_1(F_142)
      | ~ m1_subset_1(E_145,k1_zfmisc_1(k2_zfmisc_1(A_147,B_146)))
      | ~ v1_funct_1(E_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1522,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1088,c_1488])).

tff(c_1545,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_1522])).

tff(c_1547,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1093,c_1545])).

tff(c_1548,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_513])).

tff(c_17929,plain,(
    ! [A_561,B_562,C_563,D_564] :
      ( k2_relset_1(A_561,B_562,C_563) = B_562
      | ~ r2_relset_1(B_562,B_562,k1_partfun1(B_562,A_561,A_561,B_562,D_564,C_563),k6_partfun1(B_562))
      | ~ m1_subset_1(D_564,k1_zfmisc_1(k2_zfmisc_1(B_562,A_561)))
      | ~ v1_funct_2(D_564,B_562,A_561)
      | ~ v1_funct_1(D_564)
      | ~ m1_subset_1(C_563,k1_zfmisc_1(k2_zfmisc_1(A_561,B_562)))
      | ~ v1_funct_2(C_563,A_561,B_562)
      | ~ v1_funct_1(C_563) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_17935,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1548,c_17929])).

tff(c_17939,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_80,c_78,c_76,c_184,c_211,c_17935])).

tff(c_17941,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17363,c_17939])).

tff(c_17943,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_17311])).

tff(c_12,plain,(
    ! [A_14] :
      ( k5_relat_1(A_14,k6_relat_1(k2_relat_1(A_14))) = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_83,plain,(
    ! [A_14] :
      ( k5_relat_1(A_14,k6_partfun1(k2_relat_1(A_14))) = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_12])).

tff(c_17954,plain,
    ( k5_relat_1('#skF_4',k6_partfun1('#skF_1')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_17943,c_83])).

tff(c_17962,plain,(
    k5_relat_1('#skF_4',k6_partfun1('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_17954])).

tff(c_17942,plain,
    ( ~ v2_funct_1('#skF_4')
    | k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_17311])).

tff(c_17987,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_17942])).

tff(c_18,plain,(
    ! [A_16] : v2_funct_1(k6_relat_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_82,plain,(
    ! [A_16] : v2_funct_1(k6_partfun1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_18])).

tff(c_68,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_18614,plain,(
    ! [E_586,B_584,C_588,A_585,D_587] :
      ( k1_xboole_0 = C_588
      | v2_funct_1(E_586)
      | k2_relset_1(A_585,B_584,D_587) != B_584
      | ~ v2_funct_1(k1_partfun1(A_585,B_584,B_584,C_588,D_587,E_586))
      | ~ m1_subset_1(E_586,k1_zfmisc_1(k2_zfmisc_1(B_584,C_588)))
      | ~ v1_funct_2(E_586,B_584,C_588)
      | ~ v1_funct_1(E_586)
      | ~ m1_subset_1(D_587,k1_zfmisc_1(k2_zfmisc_1(A_585,B_584)))
      | ~ v1_funct_2(D_587,A_585,B_584)
      | ~ v1_funct_1(D_587) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_18618,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_1548,c_18614])).

tff(c_18623,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74,c_72,c_70,c_82,c_68,c_18618])).

tff(c_18625,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17987,c_62,c_18623])).

tff(c_18626,plain,(
    k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_17942])).

tff(c_16,plain,(
    ! [A_15] :
      ( v1_relat_1(k2_funct_1(A_15))
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18627,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_17942])).

tff(c_8,plain,(
    ! [A_13] : k1_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_85,plain,(
    ! [A_13] : k1_relat_1(k6_partfun1(A_13)) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_8])).

tff(c_17944,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17943,c_211])).

tff(c_18766,plain,(
    ! [A_593,C_594,B_595] :
      ( k6_partfun1(A_593) = k5_relat_1(C_594,k2_funct_1(C_594))
      | k1_xboole_0 = B_595
      | ~ v2_funct_1(C_594)
      | k2_relset_1(A_593,B_595,C_594) != B_595
      | ~ m1_subset_1(C_594,k1_zfmisc_1(k2_zfmisc_1(A_593,B_595)))
      | ~ v1_funct_2(C_594,A_593,B_595)
      | ~ v1_funct_1(C_594) ) ),
    inference(cnfTransformation,[status(thm)],[f_179])).

tff(c_18772,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_18766])).

tff(c_18782,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_17944,c_18627,c_18772])).

tff(c_18783,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_18782])).

tff(c_26,plain,(
    ! [A_18] :
      ( k1_relat_1(k5_relat_1(A_18,k2_funct_1(A_18))) = k1_relat_1(A_18)
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_18838,plain,
    ( k1_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_18783,c_26])).

tff(c_18851,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_74,c_18627,c_85,c_18838])).

tff(c_156,plain,(
    ! [A_68] :
      ( k2_relat_1(k2_funct_1(A_68)) = k1_relat_1(A_68)
      | ~ v2_funct_1(A_68)
      | ~ v1_funct_1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_162,plain,(
    ! [A_68] :
      ( k5_relat_1(k2_funct_1(A_68),k6_partfun1(k1_relat_1(A_68))) = k2_funct_1(A_68)
      | ~ v1_relat_1(k2_funct_1(A_68))
      | ~ v2_funct_1(A_68)
      | ~ v1_funct_1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_83])).

tff(c_18858,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),k6_partfun1('#skF_2')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_18851,c_162])).

tff(c_18862,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),k6_partfun1('#skF_2')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_74,c_18627,c_18858])).

tff(c_19154,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_18862])).

tff(c_19157,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_19154])).

tff(c_19161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_74,c_19157])).

tff(c_19163,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_18862])).

tff(c_125,plain,(
    ! [A_26] :
      ( v1_relat_1(k6_partfun1(A_26))
      | ~ v1_relat_1(k2_zfmisc_1(A_26,A_26)) ) ),
    inference(resolution,[status(thm)],[c_81,c_122])).

tff(c_134,plain,(
    ! [A_26] : v1_relat_1(k6_partfun1(A_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_125])).

tff(c_259,plain,(
    ! [A_81,B_82,C_83] :
      ( k5_relat_1(k5_relat_1(A_81,B_82),C_83) = k5_relat_1(A_81,k5_relat_1(B_82,C_83))
      | ~ v1_relat_1(C_83)
      | ~ v1_relat_1(B_82)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_292,plain,(
    ! [A_14,C_83] :
      ( k5_relat_1(A_14,k5_relat_1(k6_partfun1(k2_relat_1(A_14)),C_83)) = k5_relat_1(A_14,C_83)
      | ~ v1_relat_1(C_83)
      | ~ v1_relat_1(k6_partfun1(k2_relat_1(A_14)))
      | ~ v1_relat_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_259])).

tff(c_306,plain,(
    ! [A_14,C_83] :
      ( k5_relat_1(A_14,k5_relat_1(k6_partfun1(k2_relat_1(A_14)),C_83)) = k5_relat_1(A_14,C_83)
      | ~ v1_relat_1(C_83)
      | ~ v1_relat_1(A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_292])).

tff(c_17951,plain,(
    ! [C_83] :
      ( k5_relat_1('#skF_4',k5_relat_1(k6_partfun1('#skF_1'),C_83)) = k5_relat_1('#skF_4',C_83)
      | ~ v1_relat_1(C_83)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17943,c_306])).

tff(c_17960,plain,(
    ! [C_83] :
      ( k5_relat_1('#skF_4',k5_relat_1(k6_partfun1('#skF_1'),C_83)) = k5_relat_1('#skF_4',C_83)
      | ~ v1_relat_1(C_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_17951])).

tff(c_6,plain,(
    ! [A_6,B_10,C_12] :
      ( k5_relat_1(k5_relat_1(A_6,B_10),C_12) = k5_relat_1(A_6,k5_relat_1(B_10,C_12))
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_20555,plain,(
    ! [A_646,B_647,C_648,C_649] :
      ( k5_relat_1(k5_relat_1(A_646,k5_relat_1(B_647,C_648)),C_649) = k5_relat_1(k5_relat_1(A_646,B_647),k5_relat_1(C_648,C_649))
      | ~ v1_relat_1(C_649)
      | ~ v1_relat_1(C_648)
      | ~ v1_relat_1(k5_relat_1(A_646,B_647))
      | ~ v1_relat_1(C_648)
      | ~ v1_relat_1(B_647)
      | ~ v1_relat_1(A_646) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_6])).

tff(c_20709,plain,(
    ! [C_83,C_649] :
      ( k5_relat_1(k5_relat_1('#skF_4',k6_partfun1('#skF_1')),k5_relat_1(C_83,C_649)) = k5_relat_1(k5_relat_1('#skF_4',C_83),C_649)
      | ~ v1_relat_1(C_649)
      | ~ v1_relat_1(C_83)
      | ~ v1_relat_1(k5_relat_1('#skF_4',k6_partfun1('#skF_1')))
      | ~ v1_relat_1(C_83)
      | ~ v1_relat_1(k6_partfun1('#skF_1'))
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(C_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17960,c_20555])).

tff(c_21302,plain,(
    ! [C_651,C_652] :
      ( k5_relat_1(k5_relat_1('#skF_4',C_651),C_652) = k5_relat_1('#skF_4',k5_relat_1(C_651,C_652))
      | ~ v1_relat_1(C_652)
      | ~ v1_relat_1(C_651) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_134,c_140,c_17962,c_17962,c_20709])).

tff(c_21394,plain,(
    ! [C_652] :
      ( k5_relat_1('#skF_4',k5_relat_1(k2_funct_1('#skF_4'),C_652)) = k5_relat_1(k6_partfun1('#skF_2'),C_652)
      | ~ v1_relat_1(C_652)
      | ~ v1_relat_1(k2_funct_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18783,c_21302])).

tff(c_21489,plain,(
    ! [C_653] :
      ( k5_relat_1('#skF_4',k5_relat_1(k2_funct_1('#skF_4'),C_653)) = k5_relat_1(k6_partfun1('#skF_2'),C_653)
      | ~ v1_relat_1(C_653) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19163,c_21394])).

tff(c_21532,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = k5_relat_1('#skF_4',k6_partfun1('#skF_1'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_18626,c_21489])).

tff(c_21577,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_17962,c_21532])).

tff(c_128,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_122])).

tff(c_137,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_128])).

tff(c_64,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_18770,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_18766])).

tff(c_18778,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_68,c_64,c_18770])).

tff(c_18779,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_18778])).

tff(c_18799,plain,
    ( k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18779,c_26])).

tff(c_18812,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_80,c_64,c_85,c_18799])).

tff(c_18819,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18812,c_162])).

tff(c_18823,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_80,c_64,c_18819])).

tff(c_18865,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_18823])).

tff(c_18868,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_18865])).

tff(c_18872,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_80,c_18868])).

tff(c_18873,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_18823])).

tff(c_17172,plain,(
    ! [C_532,F_533,A_530,B_535,E_531,D_534] :
      ( k1_partfun1(A_530,B_535,C_532,D_534,E_531,F_533) = k5_relat_1(E_531,F_533)
      | ~ m1_subset_1(F_533,k1_zfmisc_1(k2_zfmisc_1(C_532,D_534)))
      | ~ v1_funct_1(F_533)
      | ~ m1_subset_1(E_531,k1_zfmisc_1(k2_zfmisc_1(A_530,B_535)))
      | ~ v1_funct_1(E_531) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_17178,plain,(
    ! [A_530,B_535,E_531] :
      ( k1_partfun1(A_530,B_535,'#skF_2','#skF_1',E_531,'#skF_4') = k5_relat_1(E_531,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_531,k1_zfmisc_1(k2_zfmisc_1(A_530,B_535)))
      | ~ v1_funct_1(E_531) ) ),
    inference(resolution,[status(thm)],[c_70,c_17172])).

tff(c_18648,plain,(
    ! [A_589,B_590,E_591] :
      ( k1_partfun1(A_589,B_590,'#skF_2','#skF_1',E_591,'#skF_4') = k5_relat_1(E_591,'#skF_4')
      | ~ m1_subset_1(E_591,k1_zfmisc_1(k2_zfmisc_1(A_589,B_590)))
      | ~ v1_funct_1(E_591) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_17178])).

tff(c_18654,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_18648])).

tff(c_18661,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1548,c_18654])).

tff(c_18874,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_18823])).

tff(c_17298,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_17294])).

tff(c_17306,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_68,c_64,c_17298])).

tff(c_17307,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_17306])).

tff(c_17321,plain,(
    ! [C_12] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_12)) = k5_relat_1(k6_partfun1('#skF_2'),C_12)
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17307,c_6])).

tff(c_17329,plain,(
    ! [C_12] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_12)) = k5_relat_1(k6_partfun1('#skF_2'),C_12)
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_17321])).

tff(c_25155,plain,(
    ! [C_721] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_721)) = k5_relat_1(k6_partfun1('#skF_2'),C_721)
      | ~ v1_relat_1(C_721) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18874,c_17329])).

tff(c_25227,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_18661,c_25155])).

tff(c_25307,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_21577,c_18873,c_25227])).

tff(c_25309,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_25307])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:38:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.31/6.00  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.31/6.01  
% 13.31/6.01  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.31/6.02  %$ r2_relset_1 > v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 13.31/6.02  
% 13.31/6.02  %Foreground sorts:
% 13.31/6.02  
% 13.31/6.02  
% 13.31/6.02  %Background operators:
% 13.31/6.02  
% 13.31/6.02  
% 13.31/6.02  %Foreground operators:
% 13.31/6.02  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 13.31/6.02  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.31/6.02  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 13.31/6.02  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 13.31/6.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.31/6.02  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 13.31/6.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.31/6.02  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 13.31/6.02  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.31/6.02  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.31/6.02  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.31/6.02  tff('#skF_2', type, '#skF_2': $i).
% 13.31/6.02  tff('#skF_3', type, '#skF_3': $i).
% 13.31/6.02  tff('#skF_1', type, '#skF_1': $i).
% 13.31/6.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.31/6.02  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 13.31/6.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.31/6.02  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.31/6.02  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.31/6.02  tff('#skF_4', type, '#skF_4': $i).
% 13.31/6.02  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 13.31/6.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.31/6.02  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.31/6.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.31/6.02  
% 13.31/6.05  tff(f_205, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 13.31/6.05  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 13.31/6.05  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 13.31/6.05  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 13.31/6.05  tff(f_179, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 13.31/6.05  tff(f_120, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 13.31/6.05  tff(f_96, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 13.31/6.05  tff(f_94, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 13.31/6.05  tff(f_118, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 13.31/6.05  tff(f_108, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 13.31/6.05  tff(f_137, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 13.31/6.05  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 13.31/6.05  tff(f_62, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 13.31/6.05  tff(f_163, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 13.31/6.05  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 13.31/6.05  tff(f_48, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 13.31/6.05  tff(f_82, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 13.31/6.05  tff(f_72, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 13.31/6.05  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 13.31/6.05  tff(c_58, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_205])).
% 13.31/6.05  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 13.31/6.05  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_205])).
% 13.31/6.05  tff(c_122, plain, (![B_64, A_65]: (v1_relat_1(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_32])).
% 13.31/6.05  tff(c_131, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_70, c_122])).
% 13.31/6.05  tff(c_140, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_131])).
% 13.31/6.05  tff(c_62, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_205])).
% 13.31/6.05  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_205])).
% 13.31/6.05  tff(c_72, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_205])).
% 13.31/6.05  tff(c_197, plain, (![A_75, B_76, C_77]: (k2_relset_1(A_75, B_76, C_77)=k2_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 13.31/6.05  tff(c_211, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_197])).
% 13.31/6.05  tff(c_17294, plain, (![B_540, C_541, A_542]: (k6_partfun1(B_540)=k5_relat_1(k2_funct_1(C_541), C_541) | k1_xboole_0=B_540 | ~v2_funct_1(C_541) | k2_relset_1(A_542, B_540, C_541)!=B_540 | ~m1_subset_1(C_541, k1_zfmisc_1(k2_zfmisc_1(A_542, B_540))) | ~v1_funct_2(C_541, A_542, B_540) | ~v1_funct_1(C_541))), inference(cnfTransformation, [status(thm)], [f_179])).
% 13.31/6.05  tff(c_17300, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_17294])).
% 13.31/6.05  tff(c_17310, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_211, c_17300])).
% 13.31/6.05  tff(c_17311, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_62, c_17310])).
% 13.31/6.05  tff(c_17363, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_17311])).
% 13.31/6.05  tff(c_80, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_205])).
% 13.31/6.05  tff(c_78, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_205])).
% 13.31/6.05  tff(c_76, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_205])).
% 13.31/6.05  tff(c_42, plain, (![A_39]: (k6_relat_1(A_39)=k6_partfun1(A_39))), inference(cnfTransformation, [status(thm)], [f_120])).
% 13.31/6.05  tff(c_34, plain, (![A_26]: (m1_subset_1(k6_relat_1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 13.31/6.05  tff(c_81, plain, (![A_26]: (m1_subset_1(k6_partfun1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_34])).
% 13.31/6.05  tff(c_177, plain, (![A_70, B_71, D_72]: (r2_relset_1(A_70, B_71, D_72, D_72) | ~m1_subset_1(D_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.31/6.05  tff(c_184, plain, (![A_26]: (r2_relset_1(A_26, A_26, k6_partfun1(A_26), k6_partfun1(A_26)))), inference(resolution, [status(thm)], [c_81, c_177])).
% 13.31/6.05  tff(c_1033, plain, (![E_119, D_122, F_121, A_118, C_120, B_123]: (k1_partfun1(A_118, B_123, C_120, D_122, E_119, F_121)=k5_relat_1(E_119, F_121) | ~m1_subset_1(F_121, k1_zfmisc_1(k2_zfmisc_1(C_120, D_122))) | ~v1_funct_1(F_121) | ~m1_subset_1(E_119, k1_zfmisc_1(k2_zfmisc_1(A_118, B_123))) | ~v1_funct_1(E_119))), inference(cnfTransformation, [status(thm)], [f_118])).
% 13.31/6.05  tff(c_1039, plain, (![A_118, B_123, E_119]: (k1_partfun1(A_118, B_123, '#skF_2', '#skF_1', E_119, '#skF_4')=k5_relat_1(E_119, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_119, k1_zfmisc_1(k2_zfmisc_1(A_118, B_123))) | ~v1_funct_1(E_119))), inference(resolution, [status(thm)], [c_70, c_1033])).
% 13.31/6.05  tff(c_1075, plain, (![A_128, B_129, E_130]: (k1_partfun1(A_128, B_129, '#skF_2', '#skF_1', E_130, '#skF_4')=k5_relat_1(E_130, '#skF_4') | ~m1_subset_1(E_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))) | ~v1_funct_1(E_130))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1039])).
% 13.31/6.05  tff(c_1081, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_1075])).
% 13.31/6.05  tff(c_1088, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1081])).
% 13.31/6.05  tff(c_66, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_205])).
% 13.31/6.05  tff(c_490, plain, (![D_91, C_92, A_93, B_94]: (D_91=C_92 | ~r2_relset_1(A_93, B_94, C_92, D_91) | ~m1_subset_1(D_91, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 13.31/6.05  tff(c_498, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_66, c_490])).
% 13.31/6.05  tff(c_513, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_498])).
% 13.31/6.05  tff(c_644, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_513])).
% 13.31/6.05  tff(c_1093, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1088, c_644])).
% 13.31/6.05  tff(c_1488, plain, (![C_143, D_144, F_142, E_145, B_146, A_147]: (m1_subset_1(k1_partfun1(A_147, B_146, C_143, D_144, E_145, F_142), k1_zfmisc_1(k2_zfmisc_1(A_147, D_144))) | ~m1_subset_1(F_142, k1_zfmisc_1(k2_zfmisc_1(C_143, D_144))) | ~v1_funct_1(F_142) | ~m1_subset_1(E_145, k1_zfmisc_1(k2_zfmisc_1(A_147, B_146))) | ~v1_funct_1(E_145))), inference(cnfTransformation, [status(thm)], [f_108])).
% 13.31/6.05  tff(c_1522, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1088, c_1488])).
% 13.31/6.05  tff(c_1545, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_1522])).
% 13.31/6.05  tff(c_1547, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1093, c_1545])).
% 13.31/6.05  tff(c_1548, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_513])).
% 13.31/6.05  tff(c_17929, plain, (![A_561, B_562, C_563, D_564]: (k2_relset_1(A_561, B_562, C_563)=B_562 | ~r2_relset_1(B_562, B_562, k1_partfun1(B_562, A_561, A_561, B_562, D_564, C_563), k6_partfun1(B_562)) | ~m1_subset_1(D_564, k1_zfmisc_1(k2_zfmisc_1(B_562, A_561))) | ~v1_funct_2(D_564, B_562, A_561) | ~v1_funct_1(D_564) | ~m1_subset_1(C_563, k1_zfmisc_1(k2_zfmisc_1(A_561, B_562))) | ~v1_funct_2(C_563, A_561, B_562) | ~v1_funct_1(C_563))), inference(cnfTransformation, [status(thm)], [f_137])).
% 13.31/6.05  tff(c_17935, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1548, c_17929])).
% 13.31/6.05  tff(c_17939, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_80, c_78, c_76, c_184, c_211, c_17935])).
% 13.31/6.05  tff(c_17941, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17363, c_17939])).
% 13.31/6.05  tff(c_17943, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_17311])).
% 13.31/6.05  tff(c_12, plain, (![A_14]: (k5_relat_1(A_14, k6_relat_1(k2_relat_1(A_14)))=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 13.31/6.05  tff(c_83, plain, (![A_14]: (k5_relat_1(A_14, k6_partfun1(k2_relat_1(A_14)))=A_14 | ~v1_relat_1(A_14))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_12])).
% 13.31/6.05  tff(c_17954, plain, (k5_relat_1('#skF_4', k6_partfun1('#skF_1'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_17943, c_83])).
% 13.31/6.05  tff(c_17962, plain, (k5_relat_1('#skF_4', k6_partfun1('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_140, c_17954])).
% 13.31/6.05  tff(c_17942, plain, (~v2_funct_1('#skF_4') | k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_17311])).
% 13.31/6.05  tff(c_17987, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_17942])).
% 13.31/6.05  tff(c_18, plain, (![A_16]: (v2_funct_1(k6_relat_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 13.31/6.05  tff(c_82, plain, (![A_16]: (v2_funct_1(k6_partfun1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_18])).
% 13.31/6.05  tff(c_68, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_205])).
% 13.31/6.05  tff(c_18614, plain, (![E_586, B_584, C_588, A_585, D_587]: (k1_xboole_0=C_588 | v2_funct_1(E_586) | k2_relset_1(A_585, B_584, D_587)!=B_584 | ~v2_funct_1(k1_partfun1(A_585, B_584, B_584, C_588, D_587, E_586)) | ~m1_subset_1(E_586, k1_zfmisc_1(k2_zfmisc_1(B_584, C_588))) | ~v1_funct_2(E_586, B_584, C_588) | ~v1_funct_1(E_586) | ~m1_subset_1(D_587, k1_zfmisc_1(k2_zfmisc_1(A_585, B_584))) | ~v1_funct_2(D_587, A_585, B_584) | ~v1_funct_1(D_587))), inference(cnfTransformation, [status(thm)], [f_163])).
% 13.31/6.05  tff(c_18618, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1548, c_18614])).
% 13.31/6.05  tff(c_18623, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74, c_72, c_70, c_82, c_68, c_18618])).
% 13.31/6.05  tff(c_18625, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17987, c_62, c_18623])).
% 13.31/6.05  tff(c_18626, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_17942])).
% 13.31/6.05  tff(c_16, plain, (![A_15]: (v1_relat_1(k2_funct_1(A_15)) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_60])).
% 13.31/6.05  tff(c_18627, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_17942])).
% 13.31/6.05  tff(c_8, plain, (![A_13]: (k1_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_48])).
% 13.31/6.05  tff(c_85, plain, (![A_13]: (k1_relat_1(k6_partfun1(A_13))=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_8])).
% 13.31/6.05  tff(c_17944, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_17943, c_211])).
% 13.31/6.05  tff(c_18766, plain, (![A_593, C_594, B_595]: (k6_partfun1(A_593)=k5_relat_1(C_594, k2_funct_1(C_594)) | k1_xboole_0=B_595 | ~v2_funct_1(C_594) | k2_relset_1(A_593, B_595, C_594)!=B_595 | ~m1_subset_1(C_594, k1_zfmisc_1(k2_zfmisc_1(A_593, B_595))) | ~v1_funct_2(C_594, A_593, B_595) | ~v1_funct_1(C_594))), inference(cnfTransformation, [status(thm)], [f_179])).
% 13.31/6.05  tff(c_18772, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_18766])).
% 13.31/6.05  tff(c_18782, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_17944, c_18627, c_18772])).
% 13.31/6.05  tff(c_18783, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_62, c_18782])).
% 13.31/6.05  tff(c_26, plain, (![A_18]: (k1_relat_1(k5_relat_1(A_18, k2_funct_1(A_18)))=k1_relat_1(A_18) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_82])).
% 13.31/6.05  tff(c_18838, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_18783, c_26])).
% 13.31/6.05  tff(c_18851, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_140, c_74, c_18627, c_85, c_18838])).
% 13.31/6.05  tff(c_156, plain, (![A_68]: (k2_relat_1(k2_funct_1(A_68))=k1_relat_1(A_68) | ~v2_funct_1(A_68) | ~v1_funct_1(A_68) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_72])).
% 13.31/6.05  tff(c_162, plain, (![A_68]: (k5_relat_1(k2_funct_1(A_68), k6_partfun1(k1_relat_1(A_68)))=k2_funct_1(A_68) | ~v1_relat_1(k2_funct_1(A_68)) | ~v2_funct_1(A_68) | ~v1_funct_1(A_68) | ~v1_relat_1(A_68))), inference(superposition, [status(thm), theory('equality')], [c_156, c_83])).
% 13.31/6.05  tff(c_18858, plain, (k5_relat_1(k2_funct_1('#skF_4'), k6_partfun1('#skF_2'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_18851, c_162])).
% 13.31/6.05  tff(c_18862, plain, (k5_relat_1(k2_funct_1('#skF_4'), k6_partfun1('#skF_2'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_74, c_18627, c_18858])).
% 13.31/6.05  tff(c_19154, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_18862])).
% 13.31/6.05  tff(c_19157, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_19154])).
% 13.31/6.05  tff(c_19161, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_74, c_19157])).
% 13.31/6.05  tff(c_19163, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_18862])).
% 13.31/6.05  tff(c_125, plain, (![A_26]: (v1_relat_1(k6_partfun1(A_26)) | ~v1_relat_1(k2_zfmisc_1(A_26, A_26)))), inference(resolution, [status(thm)], [c_81, c_122])).
% 13.31/6.05  tff(c_134, plain, (![A_26]: (v1_relat_1(k6_partfun1(A_26)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_125])).
% 13.31/6.05  tff(c_259, plain, (![A_81, B_82, C_83]: (k5_relat_1(k5_relat_1(A_81, B_82), C_83)=k5_relat_1(A_81, k5_relat_1(B_82, C_83)) | ~v1_relat_1(C_83) | ~v1_relat_1(B_82) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.31/6.05  tff(c_292, plain, (![A_14, C_83]: (k5_relat_1(A_14, k5_relat_1(k6_partfun1(k2_relat_1(A_14)), C_83))=k5_relat_1(A_14, C_83) | ~v1_relat_1(C_83) | ~v1_relat_1(k6_partfun1(k2_relat_1(A_14))) | ~v1_relat_1(A_14) | ~v1_relat_1(A_14))), inference(superposition, [status(thm), theory('equality')], [c_83, c_259])).
% 13.31/6.05  tff(c_306, plain, (![A_14, C_83]: (k5_relat_1(A_14, k5_relat_1(k6_partfun1(k2_relat_1(A_14)), C_83))=k5_relat_1(A_14, C_83) | ~v1_relat_1(C_83) | ~v1_relat_1(A_14))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_292])).
% 13.31/6.05  tff(c_17951, plain, (![C_83]: (k5_relat_1('#skF_4', k5_relat_1(k6_partfun1('#skF_1'), C_83))=k5_relat_1('#skF_4', C_83) | ~v1_relat_1(C_83) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_17943, c_306])).
% 13.31/6.05  tff(c_17960, plain, (![C_83]: (k5_relat_1('#skF_4', k5_relat_1(k6_partfun1('#skF_1'), C_83))=k5_relat_1('#skF_4', C_83) | ~v1_relat_1(C_83))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_17951])).
% 13.31/6.05  tff(c_6, plain, (![A_6, B_10, C_12]: (k5_relat_1(k5_relat_1(A_6, B_10), C_12)=k5_relat_1(A_6, k5_relat_1(B_10, C_12)) | ~v1_relat_1(C_12) | ~v1_relat_1(B_10) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.31/6.05  tff(c_20555, plain, (![A_646, B_647, C_648, C_649]: (k5_relat_1(k5_relat_1(A_646, k5_relat_1(B_647, C_648)), C_649)=k5_relat_1(k5_relat_1(A_646, B_647), k5_relat_1(C_648, C_649)) | ~v1_relat_1(C_649) | ~v1_relat_1(C_648) | ~v1_relat_1(k5_relat_1(A_646, B_647)) | ~v1_relat_1(C_648) | ~v1_relat_1(B_647) | ~v1_relat_1(A_646))), inference(superposition, [status(thm), theory('equality')], [c_259, c_6])).
% 13.31/6.05  tff(c_20709, plain, (![C_83, C_649]: (k5_relat_1(k5_relat_1('#skF_4', k6_partfun1('#skF_1')), k5_relat_1(C_83, C_649))=k5_relat_1(k5_relat_1('#skF_4', C_83), C_649) | ~v1_relat_1(C_649) | ~v1_relat_1(C_83) | ~v1_relat_1(k5_relat_1('#skF_4', k6_partfun1('#skF_1'))) | ~v1_relat_1(C_83) | ~v1_relat_1(k6_partfun1('#skF_1')) | ~v1_relat_1('#skF_4') | ~v1_relat_1(C_83))), inference(superposition, [status(thm), theory('equality')], [c_17960, c_20555])).
% 13.31/6.05  tff(c_21302, plain, (![C_651, C_652]: (k5_relat_1(k5_relat_1('#skF_4', C_651), C_652)=k5_relat_1('#skF_4', k5_relat_1(C_651, C_652)) | ~v1_relat_1(C_652) | ~v1_relat_1(C_651))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_134, c_140, c_17962, c_17962, c_20709])).
% 13.31/6.05  tff(c_21394, plain, (![C_652]: (k5_relat_1('#skF_4', k5_relat_1(k2_funct_1('#skF_4'), C_652))=k5_relat_1(k6_partfun1('#skF_2'), C_652) | ~v1_relat_1(C_652) | ~v1_relat_1(k2_funct_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_18783, c_21302])).
% 13.31/6.05  tff(c_21489, plain, (![C_653]: (k5_relat_1('#skF_4', k5_relat_1(k2_funct_1('#skF_4'), C_653))=k5_relat_1(k6_partfun1('#skF_2'), C_653) | ~v1_relat_1(C_653))), inference(demodulation, [status(thm), theory('equality')], [c_19163, c_21394])).
% 13.31/6.05  tff(c_21532, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')=k5_relat_1('#skF_4', k6_partfun1('#skF_1')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_18626, c_21489])).
% 13.31/6.05  tff(c_21577, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_140, c_17962, c_21532])).
% 13.31/6.05  tff(c_128, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_76, c_122])).
% 13.31/6.05  tff(c_137, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_128])).
% 13.31/6.05  tff(c_64, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_205])).
% 13.31/6.05  tff(c_60, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_205])).
% 13.31/6.05  tff(c_18770, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_18766])).
% 13.31/6.05  tff(c_18778, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_68, c_64, c_18770])).
% 13.31/6.05  tff(c_18779, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_60, c_18778])).
% 13.31/6.05  tff(c_18799, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18779, c_26])).
% 13.31/6.05  tff(c_18812, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_137, c_80, c_64, c_85, c_18799])).
% 13.31/6.05  tff(c_18819, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18812, c_162])).
% 13.31/6.05  tff(c_18823, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_80, c_64, c_18819])).
% 13.31/6.05  tff(c_18865, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_18823])).
% 13.31/6.05  tff(c_18868, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_18865])).
% 13.31/6.05  tff(c_18872, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_137, c_80, c_18868])).
% 13.31/6.05  tff(c_18873, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_18823])).
% 13.31/6.05  tff(c_17172, plain, (![C_532, F_533, A_530, B_535, E_531, D_534]: (k1_partfun1(A_530, B_535, C_532, D_534, E_531, F_533)=k5_relat_1(E_531, F_533) | ~m1_subset_1(F_533, k1_zfmisc_1(k2_zfmisc_1(C_532, D_534))) | ~v1_funct_1(F_533) | ~m1_subset_1(E_531, k1_zfmisc_1(k2_zfmisc_1(A_530, B_535))) | ~v1_funct_1(E_531))), inference(cnfTransformation, [status(thm)], [f_118])).
% 13.31/6.05  tff(c_17178, plain, (![A_530, B_535, E_531]: (k1_partfun1(A_530, B_535, '#skF_2', '#skF_1', E_531, '#skF_4')=k5_relat_1(E_531, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_531, k1_zfmisc_1(k2_zfmisc_1(A_530, B_535))) | ~v1_funct_1(E_531))), inference(resolution, [status(thm)], [c_70, c_17172])).
% 13.31/6.05  tff(c_18648, plain, (![A_589, B_590, E_591]: (k1_partfun1(A_589, B_590, '#skF_2', '#skF_1', E_591, '#skF_4')=k5_relat_1(E_591, '#skF_4') | ~m1_subset_1(E_591, k1_zfmisc_1(k2_zfmisc_1(A_589, B_590))) | ~v1_funct_1(E_591))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_17178])).
% 13.31/6.05  tff(c_18654, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_18648])).
% 13.31/6.05  tff(c_18661, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1548, c_18654])).
% 13.31/6.05  tff(c_18874, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_18823])).
% 13.31/6.05  tff(c_17298, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_17294])).
% 13.31/6.05  tff(c_17306, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_68, c_64, c_17298])).
% 13.31/6.05  tff(c_17307, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_60, c_17306])).
% 13.31/6.05  tff(c_17321, plain, (![C_12]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_12))=k5_relat_1(k6_partfun1('#skF_2'), C_12) | ~v1_relat_1(C_12) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_17307, c_6])).
% 13.31/6.05  tff(c_17329, plain, (![C_12]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_12))=k5_relat_1(k6_partfun1('#skF_2'), C_12) | ~v1_relat_1(C_12) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_17321])).
% 13.31/6.05  tff(c_25155, plain, (![C_721]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_721))=k5_relat_1(k6_partfun1('#skF_2'), C_721) | ~v1_relat_1(C_721))), inference(demodulation, [status(thm), theory('equality')], [c_18874, c_17329])).
% 13.31/6.05  tff(c_25227, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_18661, c_25155])).
% 13.31/6.05  tff(c_25307, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_140, c_21577, c_18873, c_25227])).
% 13.31/6.05  tff(c_25309, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_25307])).
% 13.31/6.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.31/6.05  
% 13.31/6.05  Inference rules
% 13.31/6.05  ----------------------
% 13.31/6.05  #Ref     : 0
% 13.31/6.05  #Sup     : 5257
% 13.31/6.05  #Fact    : 0
% 13.31/6.05  #Define  : 0
% 13.31/6.05  #Split   : 54
% 13.31/6.05  #Chain   : 0
% 13.31/6.05  #Close   : 0
% 13.31/6.05  
% 13.31/6.05  Ordering : KBO
% 13.31/6.05  
% 13.31/6.05  Simplification rules
% 13.31/6.05  ----------------------
% 13.31/6.05  #Subsume      : 200
% 13.31/6.05  #Demod        : 13466
% 13.31/6.05  #Tautology    : 1940
% 13.31/6.05  #SimpNegUnit  : 180
% 13.31/6.05  #BackRed      : 247
% 13.31/6.05  
% 13.31/6.05  #Partial instantiations: 0
% 13.31/6.05  #Strategies tried      : 1
% 13.31/6.05  
% 13.31/6.05  Timing (in seconds)
% 13.31/6.05  ----------------------
% 13.31/6.05  Preprocessing        : 0.45
% 13.31/6.05  Parsing              : 0.24
% 13.31/6.05  CNF conversion       : 0.03
% 13.31/6.05  Main loop            : 4.74
% 13.31/6.05  Inferencing          : 1.22
% 13.31/6.05  Reduction            : 2.43
% 13.31/6.05  Demodulation         : 2.02
% 13.31/6.05  BG Simplification    : 0.14
% 13.31/6.05  Subsumption          : 0.74
% 13.31/6.05  Abstraction          : 0.23
% 13.31/6.05  MUC search           : 0.00
% 13.31/6.05  Cooper               : 0.00
% 13.31/6.05  Total                : 5.25
% 13.31/6.05  Index Insertion      : 0.00
% 13.31/6.05  Index Deletion       : 0.00
% 13.31/6.05  Index Matching       : 0.00
% 13.31/6.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
