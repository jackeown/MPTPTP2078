%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:17 EST 2020

% Result     : Theorem 15.85s
% Output     : CNFRefutation 15.85s
% Verified   : 
% Statistics : Number of formulae       :  221 (1989 expanded)
%              Number of leaves         :   44 ( 715 expanded)
%              Depth                    :   25
%              Number of atoms          :  568 (7384 expanded)
%              Number of equality atoms :  194 (2497 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_217,negated_conjecture,(
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

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_191,axiom,(
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

tff(f_132,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_108,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_130,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_120,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_149,axiom,(
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

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_94,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_44,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( ? [B] :
            ( v1_relat_1(B)
            & v1_funct_1(B)
            & k5_relat_1(A,B) = k6_relat_1(k1_relat_1(A)) )
       => v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_funct_1)).

tff(f_175,axiom,(
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

tff(c_64,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_74,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_178,plain,(
    ! [A_74,B_75,C_76] :
      ( k2_relset_1(A_74,B_75,C_76) = k2_relat_1(C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_190,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_178])).

tff(c_1132,plain,(
    ! [B_185,C_186,A_187] :
      ( k6_partfun1(B_185) = k5_relat_1(k2_funct_1(C_186),C_186)
      | k1_xboole_0 = B_185
      | ~ v2_funct_1(C_186)
      | k2_relset_1(A_187,B_185,C_186) != B_185
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_187,B_185)))
      | ~ v1_funct_2(C_186,A_187,B_185)
      | ~ v1_funct_1(C_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_1136,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_1132])).

tff(c_1144,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_190,c_1136])).

tff(c_1145,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1144])).

tff(c_1169,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1145])).

tff(c_82,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_80,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_44,plain,(
    ! [A_39] : k6_relat_1(A_39) = k6_partfun1(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_36,plain,(
    ! [A_26] : m1_subset_1(k6_relat_1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_83,plain,(
    ! [A_26] : m1_subset_1(k6_partfun1(A_26),k1_zfmisc_1(k2_zfmisc_1(A_26,A_26))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36])).

tff(c_156,plain,(
    ! [A_68,B_69,D_70] :
      ( r2_relset_1(A_68,B_69,D_70,D_70)
      | ~ m1_subset_1(D_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_163,plain,(
    ! [A_26] : r2_relset_1(A_26,A_26,k6_partfun1(A_26),k6_partfun1(A_26)) ),
    inference(resolution,[status(thm)],[c_83,c_156])).

tff(c_534,plain,(
    ! [A_111,D_115,B_116,F_114,C_113,E_112] :
      ( k1_partfun1(A_111,B_116,C_113,D_115,E_112,F_114) = k5_relat_1(E_112,F_114)
      | ~ m1_subset_1(F_114,k1_zfmisc_1(k2_zfmisc_1(C_113,D_115)))
      | ~ v1_funct_1(F_114)
      | ~ m1_subset_1(E_112,k1_zfmisc_1(k2_zfmisc_1(A_111,B_116)))
      | ~ v1_funct_1(E_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_538,plain,(
    ! [A_111,B_116,E_112] :
      ( k1_partfun1(A_111,B_116,'#skF_2','#skF_1',E_112,'#skF_4') = k5_relat_1(E_112,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_112,k1_zfmisc_1(k2_zfmisc_1(A_111,B_116)))
      | ~ v1_funct_1(E_112) ) ),
    inference(resolution,[status(thm)],[c_72,c_534])).

tff(c_608,plain,(
    ! [A_128,B_129,E_130] :
      ( k1_partfun1(A_128,B_129,'#skF_2','#skF_1',E_130,'#skF_4') = k5_relat_1(E_130,'#skF_4')
      | ~ m1_subset_1(E_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129)))
      | ~ v1_funct_1(E_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_538])).

tff(c_617,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_608])).

tff(c_626,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_617])).

tff(c_68,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_327,plain,(
    ! [D_84,C_85,A_86,B_87] :
      ( D_84 = C_85
      | ~ r2_relset_1(A_86,B_87,C_85,D_84)
      | ~ m1_subset_1(D_84,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_335,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_68,c_327])).

tff(c_350,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_335])).

tff(c_449,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_350])).

tff(c_670,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_626,c_449])).

tff(c_866,plain,(
    ! [C_143,D_144,F_142,E_145,B_146,A_147] :
      ( m1_subset_1(k1_partfun1(A_147,B_146,C_143,D_144,E_145,F_142),k1_zfmisc_1(k2_zfmisc_1(A_147,D_144)))
      | ~ m1_subset_1(F_142,k1_zfmisc_1(k2_zfmisc_1(C_143,D_144)))
      | ~ v1_funct_1(F_142)
      | ~ m1_subset_1(E_145,k1_zfmisc_1(k2_zfmisc_1(A_147,B_146)))
      | ~ v1_funct_1(E_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_902,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_626,c_866])).

tff(c_923,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_76,c_72,c_902])).

tff(c_925,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_670,c_923])).

tff(c_926,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_350])).

tff(c_1870,plain,(
    ! [A_229,B_230,C_231,D_232] :
      ( k2_relset_1(A_229,B_230,C_231) = B_230
      | ~ r2_relset_1(B_230,B_230,k1_partfun1(B_230,A_229,A_229,B_230,D_232,C_231),k6_partfun1(B_230))
      | ~ m1_subset_1(D_232,k1_zfmisc_1(k2_zfmisc_1(B_230,A_229)))
      | ~ v1_funct_2(D_232,B_230,A_229)
      | ~ v1_funct_1(D_232)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_229,B_230)))
      | ~ v1_funct_2(C_231,A_229,B_230)
      | ~ v1_funct_1(C_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1876,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_926,c_1870])).

tff(c_1880,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_82,c_80,c_78,c_163,c_190,c_1876])).

tff(c_1882,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1169,c_1880])).

tff(c_1884,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1145])).

tff(c_60,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_10,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_130,plain,(
    ! [B_64,A_65] :
      ( v1_relat_1(B_64)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65))
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_136,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_72,c_130])).

tff(c_145,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_136])).

tff(c_139,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_78,c_130])).

tff(c_148,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_139])).

tff(c_66,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_70,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_187,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_178])).

tff(c_192,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_187])).

tff(c_28,plain,(
    ! [A_16,B_18] :
      ( k2_funct_1(A_16) = B_18
      | k6_relat_1(k2_relat_1(A_16)) != k5_relat_1(B_18,A_16)
      | k2_relat_1(B_18) != k1_relat_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_399,plain,(
    ! [A_93,B_94] :
      ( k2_funct_1(A_93) = B_94
      | k6_partfun1(k2_relat_1(A_93)) != k5_relat_1(B_94,A_93)
      | k2_relat_1(B_94) != k1_relat_1(A_93)
      | ~ v2_funct_1(A_93)
      | ~ v1_funct_1(B_94)
      | ~ v1_relat_1(B_94)
      | ~ v1_funct_1(A_93)
      | ~ v1_relat_1(A_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_28])).

tff(c_411,plain,(
    ! [B_94] :
      ( k2_funct_1('#skF_3') = B_94
      | k5_relat_1(B_94,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_94) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_94)
      | ~ v1_relat_1(B_94)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_399])).

tff(c_936,plain,(
    ! [B_148] :
      ( k2_funct_1('#skF_3') = B_148
      | k5_relat_1(B_148,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_148) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_148)
      | ~ v1_relat_1(B_148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_82,c_66,c_411])).

tff(c_942,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_145,c_936])).

tff(c_954,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_942])).

tff(c_955,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_954])).

tff(c_960,plain,(
    k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_955])).

tff(c_1885,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1884,c_960])).

tff(c_12,plain,(
    ! [A_8] : k1_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_92,plain,(
    ! [A_8] : k1_relat_1(k6_partfun1(A_8)) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_12])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_1988,plain,(
    ! [A_237,C_238,B_239] :
      ( k6_partfun1(A_237) = k5_relat_1(C_238,k2_funct_1(C_238))
      | k1_xboole_0 = B_239
      | ~ v2_funct_1(C_238)
      | k2_relset_1(A_237,B_239,C_238) != B_239
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_237,B_239)))
      | ~ v1_funct_2(C_238,A_237,B_239)
      | ~ v1_funct_1(C_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_1994,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_1988])).

tff(c_2004,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_70,c_66,c_1994])).

tff(c_2005,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2004])).

tff(c_26,plain,(
    ! [A_15] :
      ( k5_relat_1(A_15,k2_funct_1(A_15)) = k6_relat_1(k1_relat_1(A_15))
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_85,plain,(
    ! [A_15] :
      ( k5_relat_1(A_15,k2_funct_1(A_15)) = k6_partfun1(k1_relat_1(A_15))
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_26])).

tff(c_2011,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2005,c_85])).

tff(c_2020,plain,(
    k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_82,c_66,c_2011])).

tff(c_2093,plain,(
    k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2020,c_92])).

tff(c_2120,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_2093])).

tff(c_2122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1885,c_2120])).

tff(c_2123,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_955])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [B_10,A_9] :
      ( k5_relat_1(B_10,k6_relat_1(A_9)) = B_10
      | ~ r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_166,plain,(
    ! [B_71,A_72] :
      ( k5_relat_1(B_71,k6_partfun1(A_72)) = B_71
      | ~ r1_tarski(k2_relat_1(B_71),A_72)
      | ~ v1_relat_1(B_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_16])).

tff(c_215,plain,(
    ! [B_78] :
      ( k5_relat_1(B_78,k6_partfun1(k2_relat_1(B_78))) = B_78
      | ~ v1_relat_1(B_78) ) ),
    inference(resolution,[status(thm)],[c_6,c_166])).

tff(c_224,plain,
    ( k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_215])).

tff(c_231,plain,(
    k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_224])).

tff(c_20,plain,(
    ! [A_11] : v1_funct_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_88,plain,(
    ! [A_11] : v1_funct_1(k6_partfun1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_20])).

tff(c_2221,plain,(
    ! [E_256,F_258,A_255,D_259,C_257,B_260] :
      ( k1_partfun1(A_255,B_260,C_257,D_259,E_256,F_258) = k5_relat_1(E_256,F_258)
      | ~ m1_subset_1(F_258,k1_zfmisc_1(k2_zfmisc_1(C_257,D_259)))
      | ~ v1_funct_1(F_258)
      | ~ m1_subset_1(E_256,k1_zfmisc_1(k2_zfmisc_1(A_255,B_260)))
      | ~ v1_funct_1(E_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_2223,plain,(
    ! [A_255,B_260,A_26,E_256] :
      ( k1_partfun1(A_255,B_260,A_26,A_26,E_256,k6_partfun1(A_26)) = k5_relat_1(E_256,k6_partfun1(A_26))
      | ~ v1_funct_1(k6_partfun1(A_26))
      | ~ m1_subset_1(E_256,k1_zfmisc_1(k2_zfmisc_1(A_255,B_260)))
      | ~ v1_funct_1(E_256) ) ),
    inference(resolution,[status(thm)],[c_83,c_2221])).

tff(c_4074,plain,(
    ! [A_387,B_388,A_389,E_390] :
      ( k1_partfun1(A_387,B_388,A_389,A_389,E_390,k6_partfun1(A_389)) = k5_relat_1(E_390,k6_partfun1(A_389))
      | ~ m1_subset_1(E_390,k1_zfmisc_1(k2_zfmisc_1(A_387,B_388)))
      | ~ v1_funct_1(E_390) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2223])).

tff(c_4092,plain,(
    ! [A_389] :
      ( k1_partfun1('#skF_1','#skF_2',A_389,A_389,'#skF_3',k6_partfun1(A_389)) = k5_relat_1('#skF_3',k6_partfun1(A_389))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_78,c_4074])).

tff(c_4600,plain,(
    ! [A_419] : k1_partfun1('#skF_1','#skF_2',A_419,A_419,'#skF_3',k6_partfun1(A_419)) = k5_relat_1('#skF_3',k6_partfun1(A_419)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_4092])).

tff(c_38,plain,(
    ! [C_29,D_30,B_28,F_32,A_27,E_31] :
      ( m1_subset_1(k1_partfun1(A_27,B_28,C_29,D_30,E_31,F_32),k1_zfmisc_1(k2_zfmisc_1(A_27,D_30)))
      | ~ m1_subset_1(F_32,k1_zfmisc_1(k2_zfmisc_1(C_29,D_30)))
      | ~ v1_funct_1(F_32)
      | ~ m1_subset_1(E_31,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28)))
      | ~ v1_funct_1(E_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_4612,plain,(
    ! [A_419] :
      ( m1_subset_1(k5_relat_1('#skF_3',k6_partfun1(A_419)),k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_419)))
      | ~ m1_subset_1(k6_partfun1(A_419),k1_zfmisc_1(k2_zfmisc_1(A_419,A_419)))
      | ~ v1_funct_1(k6_partfun1(A_419))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4600,c_38])).

tff(c_4639,plain,(
    ! [A_421] : m1_subset_1(k5_relat_1('#skF_3',k6_partfun1(A_421)),k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_421))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_88,c_83,c_4612])).

tff(c_8,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4673,plain,(
    ! [A_421] :
      ( v1_relat_1(k5_relat_1('#skF_3',k6_partfun1(A_421)))
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1',A_421)) ) ),
    inference(resolution,[status(thm)],[c_4639,c_8])).

tff(c_4721,plain,(
    ! [A_421] : v1_relat_1(k5_relat_1('#skF_3',k6_partfun1(A_421))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_4673])).

tff(c_4117,plain,(
    ! [A_389] : k1_partfun1('#skF_1','#skF_2',A_389,A_389,'#skF_3',k6_partfun1(A_389)) = k5_relat_1('#skF_3',k6_partfun1(A_389)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_4092])).

tff(c_2164,plain,(
    ! [E_244,A_246,B_245,D_243,C_242,F_241] :
      ( v1_funct_1(k1_partfun1(A_246,B_245,C_242,D_243,E_244,F_241))
      | ~ m1_subset_1(F_241,k1_zfmisc_1(k2_zfmisc_1(C_242,D_243)))
      | ~ v1_funct_1(F_241)
      | ~ m1_subset_1(E_244,k1_zfmisc_1(k2_zfmisc_1(A_246,B_245)))
      | ~ v1_funct_1(E_244) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2166,plain,(
    ! [A_246,B_245,A_26,E_244] :
      ( v1_funct_1(k1_partfun1(A_246,B_245,A_26,A_26,E_244,k6_partfun1(A_26)))
      | ~ v1_funct_1(k6_partfun1(A_26))
      | ~ m1_subset_1(E_244,k1_zfmisc_1(k2_zfmisc_1(A_246,B_245)))
      | ~ v1_funct_1(E_244) ) ),
    inference(resolution,[status(thm)],[c_83,c_2164])).

tff(c_2238,plain,(
    ! [A_262,B_263,A_264,E_265] :
      ( v1_funct_1(k1_partfun1(A_262,B_263,A_264,A_264,E_265,k6_partfun1(A_264)))
      | ~ m1_subset_1(E_265,k1_zfmisc_1(k2_zfmisc_1(A_262,B_263)))
      | ~ v1_funct_1(E_265) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_2166])).

tff(c_2244,plain,(
    ! [A_264] :
      ( v1_funct_1(k1_partfun1('#skF_1','#skF_2',A_264,A_264,'#skF_3',k6_partfun1(A_264)))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_78,c_2238])).

tff(c_2253,plain,(
    ! [A_264] : v1_funct_1(k1_partfun1('#skF_1','#skF_2',A_264,A_264,'#skF_3',k6_partfun1(A_264))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2244])).

tff(c_4599,plain,(
    ! [A_264] : v1_funct_1(k5_relat_1('#skF_3',k6_partfun1(A_264))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4117,c_2253])).

tff(c_2124,plain,(
    k2_relat_1('#skF_4') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_955])).

tff(c_2125,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2124,c_190])).

tff(c_2328,plain,(
    ! [B_275,C_276,A_277] :
      ( k6_partfun1(B_275) = k5_relat_1(k2_funct_1(C_276),C_276)
      | k1_xboole_0 = B_275
      | ~ v2_funct_1(C_276)
      | k2_relset_1(A_277,B_275,C_276) != B_275
      | ~ m1_subset_1(C_276,k1_zfmisc_1(k2_zfmisc_1(A_277,B_275)))
      | ~ v1_funct_2(C_276,A_277,B_275)
      | ~ v1_funct_1(C_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_2332,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_2328])).

tff(c_2340,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_2125,c_2332])).

tff(c_2341,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_4')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2340])).

tff(c_2365,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2341])).

tff(c_2401,plain,(
    ! [A_283,C_284,B_285] :
      ( k6_partfun1(A_283) = k5_relat_1(C_284,k2_funct_1(C_284))
      | k1_xboole_0 = B_285
      | ~ v2_funct_1(C_284)
      | k2_relset_1(A_283,B_285,C_284) != B_285
      | ~ m1_subset_1(C_284,k1_zfmisc_1(k2_zfmisc_1(A_283,B_285)))
      | ~ v1_funct_2(C_284,A_283,B_285)
      | ~ v1_funct_1(C_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_2407,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_2401])).

tff(c_2417,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_70,c_66,c_2407])).

tff(c_2418,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2417])).

tff(c_2424,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2418,c_85])).

tff(c_2433,plain,(
    k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_82,c_66,c_2424])).

tff(c_2504,plain,(
    k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2433,c_92])).

tff(c_2530,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_2504])).

tff(c_2532,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2365,c_2530])).

tff(c_2533,plain,
    ( ~ v2_funct_1('#skF_4')
    | k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2341])).

tff(c_2555,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2533])).

tff(c_18,plain,(
    ! [A_11] : v1_relat_1(k6_relat_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_89,plain,(
    ! [A_11] : v1_relat_1(k6_partfun1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_18])).

tff(c_14,plain,(
    ! [A_8] : k2_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_91,plain,(
    ! [A_8] : k2_relat_1(k6_partfun1(A_8)) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_14])).

tff(c_227,plain,(
    ! [A_8] :
      ( k5_relat_1(k6_partfun1(A_8),k6_partfun1(A_8)) = k6_partfun1(A_8)
      | ~ v1_relat_1(k6_partfun1(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_215])).

tff(c_233,plain,(
    ! [A_8] : k5_relat_1(k6_partfun1(A_8),k6_partfun1(A_8)) = k6_partfun1(A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_227])).

tff(c_22,plain,(
    ! [A_12,B_14] :
      ( v2_funct_1(A_12)
      | k6_relat_1(k1_relat_1(A_12)) != k5_relat_1(A_12,B_14)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_360,plain,(
    ! [A_89,B_90] :
      ( v2_funct_1(A_89)
      | k6_partfun1(k1_relat_1(A_89)) != k5_relat_1(A_89,B_90)
      | ~ v1_funct_1(B_90)
      | ~ v1_relat_1(B_90)
      | ~ v1_funct_1(A_89)
      | ~ v1_relat_1(A_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_22])).

tff(c_368,plain,(
    ! [A_8] :
      ( v2_funct_1(k6_partfun1(A_8))
      | k6_partfun1(k1_relat_1(k6_partfun1(A_8))) != k6_partfun1(A_8)
      | ~ v1_funct_1(k6_partfun1(A_8))
      | ~ v1_relat_1(k6_partfun1(A_8))
      | ~ v1_funct_1(k6_partfun1(A_8))
      | ~ v1_relat_1(k6_partfun1(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_360])).

tff(c_382,plain,(
    ! [A_8] : v2_funct_1(k6_partfun1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_88,c_89,c_88,c_92,c_368])).

tff(c_3219,plain,(
    ! [C_338,B_334,D_337,E_336,A_335] :
      ( k1_xboole_0 = C_338
      | v2_funct_1(E_336)
      | k2_relset_1(A_335,B_334,D_337) != B_334
      | ~ v2_funct_1(k1_partfun1(A_335,B_334,B_334,C_338,D_337,E_336))
      | ~ m1_subset_1(E_336,k1_zfmisc_1(k2_zfmisc_1(B_334,C_338)))
      | ~ v1_funct_2(E_336,B_334,C_338)
      | ~ v1_funct_1(E_336)
      | ~ m1_subset_1(D_337,k1_zfmisc_1(k2_zfmisc_1(A_335,B_334)))
      | ~ v1_funct_2(D_337,A_335,B_334)
      | ~ v1_funct_1(D_337) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_3229,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_926,c_3219])).

tff(c_3240,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_76,c_74,c_72,c_382,c_70,c_3229])).

tff(c_3242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2555,c_64,c_3240])).

tff(c_3244,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2533])).

tff(c_2534,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2341])).

tff(c_2539,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2534,c_2125])).

tff(c_3363,plain,(
    ! [A_343,C_344,B_345] :
      ( k6_partfun1(A_343) = k5_relat_1(C_344,k2_funct_1(C_344))
      | k1_xboole_0 = B_345
      | ~ v2_funct_1(C_344)
      | k2_relset_1(A_343,B_345,C_344) != B_345
      | ~ m1_subset_1(C_344,k1_zfmisc_1(k2_zfmisc_1(A_343,B_345)))
      | ~ v1_funct_2(C_344,A_343,B_345)
      | ~ v1_funct_1(C_344) ) ),
    inference(cnfTransformation,[status(thm)],[f_191])).

tff(c_3367,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_3363])).

tff(c_3375,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_2539,c_3244,c_3367])).

tff(c_3376,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3375])).

tff(c_3404,plain,
    ( k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3376,c_85])).

tff(c_3413,plain,(
    k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_76,c_3244,c_3404])).

tff(c_3482,plain,(
    k1_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3413,c_92])).

tff(c_3505,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_3482])).

tff(c_2540,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2534,c_2124])).

tff(c_4624,plain,(
    ! [A_419] : m1_subset_1(k5_relat_1('#skF_3',k6_partfun1(A_419)),k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_419))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_88,c_83,c_4612])).

tff(c_3531,plain,(
    ! [B_350,D_348,A_351,F_346,E_349,C_347] :
      ( m1_subset_1(k1_partfun1(A_351,B_350,C_347,D_348,E_349,F_346),k1_zfmisc_1(k2_zfmisc_1(A_351,D_348)))
      | ~ m1_subset_1(F_346,k1_zfmisc_1(k2_zfmisc_1(C_347,D_348)))
      | ~ v1_funct_1(F_346)
      | ~ m1_subset_1(E_349,k1_zfmisc_1(k2_zfmisc_1(A_351,B_350)))
      | ~ v1_funct_1(E_349) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2225,plain,(
    ! [A_255,B_260,E_256] :
      ( k1_partfun1(A_255,B_260,'#skF_2','#skF_1',E_256,'#skF_4') = k5_relat_1(E_256,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_256,k1_zfmisc_1(k2_zfmisc_1(A_255,B_260)))
      | ~ v1_funct_1(E_256) ) ),
    inference(resolution,[status(thm)],[c_72,c_2221])).

tff(c_2233,plain,(
    ! [A_255,B_260,E_256] :
      ( k1_partfun1(A_255,B_260,'#skF_2','#skF_1',E_256,'#skF_4') = k5_relat_1(E_256,'#skF_4')
      | ~ m1_subset_1(E_256,k1_zfmisc_1(k2_zfmisc_1(A_255,B_260)))
      | ~ v1_funct_1(E_256) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2225])).

tff(c_8105,plain,(
    ! [C_674,E_673,D_672,F_675,B_676,A_677] :
      ( k1_partfun1(A_677,D_672,'#skF_2','#skF_1',k1_partfun1(A_677,B_676,C_674,D_672,E_673,F_675),'#skF_4') = k5_relat_1(k1_partfun1(A_677,B_676,C_674,D_672,E_673,F_675),'#skF_4')
      | ~ v1_funct_1(k1_partfun1(A_677,B_676,C_674,D_672,E_673,F_675))
      | ~ m1_subset_1(F_675,k1_zfmisc_1(k2_zfmisc_1(C_674,D_672)))
      | ~ v1_funct_1(F_675)
      | ~ m1_subset_1(E_673,k1_zfmisc_1(k2_zfmisc_1(A_677,B_676)))
      | ~ v1_funct_1(E_673) ) ),
    inference(resolution,[status(thm)],[c_3531,c_2233])).

tff(c_8183,plain,(
    ! [A_389] :
      ( k1_partfun1('#skF_1',A_389,'#skF_2','#skF_1',k1_partfun1('#skF_1','#skF_2',A_389,A_389,'#skF_3',k6_partfun1(A_389)),'#skF_4') = k5_relat_1(k1_partfun1('#skF_1','#skF_2',A_389,A_389,'#skF_3',k6_partfun1(A_389)),'#skF_4')
      | ~ v1_funct_1(k5_relat_1('#skF_3',k6_partfun1(A_389)))
      | ~ m1_subset_1(k6_partfun1(A_389),k1_zfmisc_1(k2_zfmisc_1(A_389,A_389)))
      | ~ v1_funct_1(k6_partfun1(A_389))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4117,c_8105])).

tff(c_12199,plain,(
    ! [A_784] : k1_partfun1('#skF_1',A_784,'#skF_2','#skF_1',k5_relat_1('#skF_3',k6_partfun1(A_784)),'#skF_4') = k5_relat_1(k5_relat_1('#skF_3',k6_partfun1(A_784)),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_88,c_83,c_4599,c_4117,c_4117,c_8183])).

tff(c_12259,plain,(
    ! [A_784] :
      ( m1_subset_1(k5_relat_1(k5_relat_1('#skF_3',k6_partfun1(A_784)),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(k5_relat_1('#skF_3',k6_partfun1(A_784)),k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_784)))
      | ~ v1_funct_1(k5_relat_1('#skF_3',k6_partfun1(A_784))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12199,c_38])).

tff(c_12325,plain,(
    ! [A_784] : m1_subset_1(k5_relat_1(k5_relat_1('#skF_3',k6_partfun1(A_784)),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4599,c_4624,c_76,c_72,c_12259])).

tff(c_2300,plain,(
    ! [A_272,B_273,E_274] :
      ( k1_partfun1(A_272,B_273,'#skF_2','#skF_1',E_274,'#skF_4') = k5_relat_1(E_274,'#skF_4')
      | ~ m1_subset_1(E_274,k1_zfmisc_1(k2_zfmisc_1(A_272,B_273)))
      | ~ v1_funct_1(E_274) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2225])).

tff(c_2309,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_2300])).

tff(c_2318,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_926,c_2309])).

tff(c_90,plain,(
    ! [B_10,A_9] :
      ( k5_relat_1(B_10,k6_partfun1(A_9)) = B_10
      | ~ r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_16])).

tff(c_196,plain,(
    ! [A_9] :
      ( k5_relat_1('#skF_3',k6_partfun1(A_9)) = '#skF_3'
      | ~ r1_tarski('#skF_2',A_9)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_90])).

tff(c_200,plain,(
    ! [A_9] :
      ( k5_relat_1('#skF_3',k6_partfun1(A_9)) = '#skF_3'
      | ~ r1_tarski('#skF_2',A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_196])).

tff(c_8340,plain,(
    ! [A_389] : k1_partfun1('#skF_1',A_389,'#skF_2','#skF_1',k5_relat_1('#skF_3',k6_partfun1(A_389)),'#skF_4') = k5_relat_1(k5_relat_1('#skF_3',k6_partfun1(A_389)),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_88,c_83,c_4599,c_4117,c_4117,c_8183])).

tff(c_32,plain,(
    ! [A_22,B_23,D_25] :
      ( r2_relset_1(A_22,B_23,D_25,D_25)
      | ~ m1_subset_1(D_25,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_3581,plain,(
    ! [B_350,D_348,A_351,F_346,E_349,C_347] :
      ( r2_relset_1(A_351,D_348,k1_partfun1(A_351,B_350,C_347,D_348,E_349,F_346),k1_partfun1(A_351,B_350,C_347,D_348,E_349,F_346))
      | ~ m1_subset_1(F_346,k1_zfmisc_1(k2_zfmisc_1(C_347,D_348)))
      | ~ v1_funct_1(F_346)
      | ~ m1_subset_1(E_349,k1_zfmisc_1(k2_zfmisc_1(A_351,B_350)))
      | ~ v1_funct_1(E_349) ) ),
    inference(resolution,[status(thm)],[c_3531,c_32])).

tff(c_12243,plain,(
    ! [A_784] :
      ( r2_relset_1('#skF_1','#skF_1',k5_relat_1(k5_relat_1('#skF_3',k6_partfun1(A_784)),'#skF_4'),k1_partfun1('#skF_1',A_784,'#skF_2','#skF_1',k5_relat_1('#skF_3',k6_partfun1(A_784)),'#skF_4'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(k5_relat_1('#skF_3',k6_partfun1(A_784)),k1_zfmisc_1(k2_zfmisc_1('#skF_1',A_784)))
      | ~ v1_funct_1(k5_relat_1('#skF_3',k6_partfun1(A_784))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12199,c_3581])).

tff(c_18308,plain,(
    ! [A_923] : r2_relset_1('#skF_1','#skF_1',k5_relat_1(k5_relat_1('#skF_3',k6_partfun1(A_923)),'#skF_4'),k5_relat_1(k5_relat_1('#skF_3',k6_partfun1(A_923)),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4599,c_4624,c_76,c_72,c_8340,c_12243])).

tff(c_18313,plain,(
    ! [A_9] :
      ( r2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_4'),k5_relat_1(k5_relat_1('#skF_3',k6_partfun1(A_9)),'#skF_4'))
      | ~ r1_tarski('#skF_2',A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_18308])).

tff(c_18515,plain,(
    ! [A_928] :
      ( r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k5_relat_1(k5_relat_1('#skF_3',k6_partfun1(A_928)),'#skF_4'))
      | ~ r1_tarski('#skF_2',A_928) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2318,c_18313])).

tff(c_34,plain,(
    ! [D_25,C_24,A_22,B_23] :
      ( D_25 = C_24
      | ~ r2_relset_1(A_22,B_23,C_24,D_25)
      | ~ m1_subset_1(D_25,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23)))
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_18517,plain,(
    ! [A_928] :
      ( k5_relat_1(k5_relat_1('#skF_3',k6_partfun1(A_928)),'#skF_4') = k6_partfun1('#skF_1')
      | ~ m1_subset_1(k5_relat_1(k5_relat_1('#skF_3',k6_partfun1(A_928)),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
      | ~ r1_tarski('#skF_2',A_928) ) ),
    inference(resolution,[status(thm)],[c_18515,c_34])).

tff(c_18536,plain,(
    ! [A_929] :
      ( k5_relat_1(k5_relat_1('#skF_3',k6_partfun1(A_929)),'#skF_4') = k6_partfun1('#skF_1')
      | ~ r1_tarski('#skF_2',A_929) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_12325,c_18517])).

tff(c_84,plain,(
    ! [A_16,B_18] :
      ( k2_funct_1(A_16) = B_18
      | k6_partfun1(k2_relat_1(A_16)) != k5_relat_1(B_18,A_16)
      | k2_relat_1(B_18) != k1_relat_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_28])).

tff(c_18574,plain,(
    ! [A_929] :
      ( k5_relat_1('#skF_3',k6_partfun1(A_929)) = k2_funct_1('#skF_4')
      | k6_partfun1(k2_relat_1('#skF_4')) != k6_partfun1('#skF_1')
      | k2_relat_1(k5_relat_1('#skF_3',k6_partfun1(A_929))) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(k5_relat_1('#skF_3',k6_partfun1(A_929)))
      | ~ v1_relat_1(k5_relat_1('#skF_3',k6_partfun1(A_929)))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_2',A_929) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18536,c_84])).

tff(c_22465,plain,(
    ! [A_1062] :
      ( k5_relat_1('#skF_3',k6_partfun1(A_1062)) = k2_funct_1('#skF_4')
      | k2_relat_1(k5_relat_1('#skF_3',k6_partfun1(A_1062))) != '#skF_2'
      | ~ r1_tarski('#skF_2',A_1062) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_76,c_4721,c_4599,c_3244,c_3505,c_2540,c_18574])).

tff(c_22474,plain,
    ( k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = k2_funct_1('#skF_4')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_22465])).

tff(c_22482,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_192,c_231,c_22474])).

tff(c_22486,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22482,c_3376])).

tff(c_22489,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2123,c_22486])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:53:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 15.85/8.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.85/8.29  
% 15.85/8.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.85/8.29  %$ r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 15.85/8.29  
% 15.85/8.29  %Foreground sorts:
% 15.85/8.29  
% 15.85/8.29  
% 15.85/8.29  %Background operators:
% 15.85/8.29  
% 15.85/8.29  
% 15.85/8.29  %Foreground operators:
% 15.85/8.29  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 15.85/8.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 15.85/8.29  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 15.85/8.29  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 15.85/8.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 15.85/8.29  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 15.85/8.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 15.85/8.29  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 15.85/8.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 15.85/8.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 15.85/8.29  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 15.85/8.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 15.85/8.29  tff('#skF_2', type, '#skF_2': $i).
% 15.85/8.29  tff('#skF_3', type, '#skF_3': $i).
% 15.85/8.29  tff('#skF_1', type, '#skF_1': $i).
% 15.85/8.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 15.85/8.29  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 15.85/8.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 15.85/8.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 15.85/8.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 15.85/8.29  tff('#skF_4', type, '#skF_4': $i).
% 15.85/8.29  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 15.85/8.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 15.85/8.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 15.85/8.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 15.85/8.29  
% 15.85/8.32  tff(f_217, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 15.85/8.32  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 15.85/8.32  tff(f_191, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 15.85/8.32  tff(f_132, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 15.85/8.32  tff(f_108, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 15.85/8.32  tff(f_106, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 15.85/8.32  tff(f_130, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 15.85/8.32  tff(f_120, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 15.85/8.32  tff(f_149, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 15.85/8.32  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 15.85/8.32  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 15.85/8.32  tff(f_94, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 15.85/8.32  tff(f_44, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 15.85/8.32  tff(f_77, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 15.85/8.32  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 15.85/8.32  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 15.85/8.32  tff(f_54, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 15.85/8.32  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((?[B]: ((v1_relat_1(B) & v1_funct_1(B)) & (k5_relat_1(A, B) = k6_relat_1(k1_relat_1(A))))) => v2_funct_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_funct_1)).
% 15.85/8.32  tff(f_175, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 15.85/8.32  tff(c_64, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_217])).
% 15.85/8.32  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_217])).
% 15.85/8.32  tff(c_74, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_217])).
% 15.85/8.32  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_217])).
% 15.85/8.32  tff(c_178, plain, (![A_74, B_75, C_76]: (k2_relset_1(A_74, B_75, C_76)=k2_relat_1(C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 15.85/8.32  tff(c_190, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_178])).
% 15.85/8.32  tff(c_1132, plain, (![B_185, C_186, A_187]: (k6_partfun1(B_185)=k5_relat_1(k2_funct_1(C_186), C_186) | k1_xboole_0=B_185 | ~v2_funct_1(C_186) | k2_relset_1(A_187, B_185, C_186)!=B_185 | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_187, B_185))) | ~v1_funct_2(C_186, A_187, B_185) | ~v1_funct_1(C_186))), inference(cnfTransformation, [status(thm)], [f_191])).
% 15.85/8.32  tff(c_1136, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_1132])).
% 15.85/8.32  tff(c_1144, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_190, c_1136])).
% 15.85/8.32  tff(c_1145, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_64, c_1144])).
% 15.85/8.32  tff(c_1169, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_1145])).
% 15.85/8.32  tff(c_82, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_217])).
% 15.85/8.32  tff(c_80, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_217])).
% 15.85/8.32  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_217])).
% 15.85/8.32  tff(c_44, plain, (![A_39]: (k6_relat_1(A_39)=k6_partfun1(A_39))), inference(cnfTransformation, [status(thm)], [f_132])).
% 15.85/8.32  tff(c_36, plain, (![A_26]: (m1_subset_1(k6_relat_1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(cnfTransformation, [status(thm)], [f_108])).
% 15.85/8.32  tff(c_83, plain, (![A_26]: (m1_subset_1(k6_partfun1(A_26), k1_zfmisc_1(k2_zfmisc_1(A_26, A_26))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36])).
% 15.85/8.32  tff(c_156, plain, (![A_68, B_69, D_70]: (r2_relset_1(A_68, B_69, D_70, D_70) | ~m1_subset_1(D_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 15.85/8.32  tff(c_163, plain, (![A_26]: (r2_relset_1(A_26, A_26, k6_partfun1(A_26), k6_partfun1(A_26)))), inference(resolution, [status(thm)], [c_83, c_156])).
% 15.85/8.32  tff(c_534, plain, (![A_111, D_115, B_116, F_114, C_113, E_112]: (k1_partfun1(A_111, B_116, C_113, D_115, E_112, F_114)=k5_relat_1(E_112, F_114) | ~m1_subset_1(F_114, k1_zfmisc_1(k2_zfmisc_1(C_113, D_115))) | ~v1_funct_1(F_114) | ~m1_subset_1(E_112, k1_zfmisc_1(k2_zfmisc_1(A_111, B_116))) | ~v1_funct_1(E_112))), inference(cnfTransformation, [status(thm)], [f_130])).
% 15.85/8.32  tff(c_538, plain, (![A_111, B_116, E_112]: (k1_partfun1(A_111, B_116, '#skF_2', '#skF_1', E_112, '#skF_4')=k5_relat_1(E_112, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_112, k1_zfmisc_1(k2_zfmisc_1(A_111, B_116))) | ~v1_funct_1(E_112))), inference(resolution, [status(thm)], [c_72, c_534])).
% 15.85/8.32  tff(c_608, plain, (![A_128, B_129, E_130]: (k1_partfun1(A_128, B_129, '#skF_2', '#skF_1', E_130, '#skF_4')=k5_relat_1(E_130, '#skF_4') | ~m1_subset_1(E_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))) | ~v1_funct_1(E_130))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_538])).
% 15.85/8.32  tff(c_617, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_608])).
% 15.85/8.32  tff(c_626, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_617])).
% 15.85/8.32  tff(c_68, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_217])).
% 15.85/8.32  tff(c_327, plain, (![D_84, C_85, A_86, B_87]: (D_84=C_85 | ~r2_relset_1(A_86, B_87, C_85, D_84) | ~m1_subset_1(D_84, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 15.85/8.32  tff(c_335, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_327])).
% 15.85/8.32  tff(c_350, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_335])).
% 15.85/8.32  tff(c_449, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_350])).
% 15.85/8.32  tff(c_670, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_626, c_449])).
% 15.85/8.32  tff(c_866, plain, (![C_143, D_144, F_142, E_145, B_146, A_147]: (m1_subset_1(k1_partfun1(A_147, B_146, C_143, D_144, E_145, F_142), k1_zfmisc_1(k2_zfmisc_1(A_147, D_144))) | ~m1_subset_1(F_142, k1_zfmisc_1(k2_zfmisc_1(C_143, D_144))) | ~v1_funct_1(F_142) | ~m1_subset_1(E_145, k1_zfmisc_1(k2_zfmisc_1(A_147, B_146))) | ~v1_funct_1(E_145))), inference(cnfTransformation, [status(thm)], [f_120])).
% 15.85/8.32  tff(c_902, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_626, c_866])).
% 15.85/8.32  tff(c_923, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_76, c_72, c_902])).
% 15.85/8.32  tff(c_925, plain, $false, inference(negUnitSimplification, [status(thm)], [c_670, c_923])).
% 15.85/8.32  tff(c_926, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_350])).
% 15.85/8.32  tff(c_1870, plain, (![A_229, B_230, C_231, D_232]: (k2_relset_1(A_229, B_230, C_231)=B_230 | ~r2_relset_1(B_230, B_230, k1_partfun1(B_230, A_229, A_229, B_230, D_232, C_231), k6_partfun1(B_230)) | ~m1_subset_1(D_232, k1_zfmisc_1(k2_zfmisc_1(B_230, A_229))) | ~v1_funct_2(D_232, B_230, A_229) | ~v1_funct_1(D_232) | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(A_229, B_230))) | ~v1_funct_2(C_231, A_229, B_230) | ~v1_funct_1(C_231))), inference(cnfTransformation, [status(thm)], [f_149])).
% 15.85/8.32  tff(c_1876, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_926, c_1870])).
% 15.85/8.32  tff(c_1880, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_82, c_80, c_78, c_163, c_190, c_1876])).
% 15.85/8.32  tff(c_1882, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1169, c_1880])).
% 15.85/8.32  tff(c_1884, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_1145])).
% 15.85/8.32  tff(c_60, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_217])).
% 15.85/8.32  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 15.85/8.32  tff(c_130, plain, (![B_64, A_65]: (v1_relat_1(B_64) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_38])).
% 15.85/8.32  tff(c_136, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_72, c_130])).
% 15.85/8.32  tff(c_145, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_136])).
% 15.85/8.32  tff(c_139, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_78, c_130])).
% 15.85/8.32  tff(c_148, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_139])).
% 15.85/8.32  tff(c_66, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_217])).
% 15.85/8.32  tff(c_70, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_217])).
% 15.85/8.32  tff(c_187, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_178])).
% 15.85/8.32  tff(c_192, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_187])).
% 15.85/8.32  tff(c_28, plain, (![A_16, B_18]: (k2_funct_1(A_16)=B_18 | k6_relat_1(k2_relat_1(A_16))!=k5_relat_1(B_18, A_16) | k2_relat_1(B_18)!=k1_relat_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_94])).
% 15.85/8.32  tff(c_399, plain, (![A_93, B_94]: (k2_funct_1(A_93)=B_94 | k6_partfun1(k2_relat_1(A_93))!=k5_relat_1(B_94, A_93) | k2_relat_1(B_94)!=k1_relat_1(A_93) | ~v2_funct_1(A_93) | ~v1_funct_1(B_94) | ~v1_relat_1(B_94) | ~v1_funct_1(A_93) | ~v1_relat_1(A_93))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_28])).
% 15.85/8.32  tff(c_411, plain, (![B_94]: (k2_funct_1('#skF_3')=B_94 | k5_relat_1(B_94, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_94)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_94) | ~v1_relat_1(B_94) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_192, c_399])).
% 15.85/8.32  tff(c_936, plain, (![B_148]: (k2_funct_1('#skF_3')=B_148 | k5_relat_1(B_148, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_148)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_148) | ~v1_relat_1(B_148))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_82, c_66, c_411])).
% 15.85/8.32  tff(c_942, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_145, c_936])).
% 15.85/8.32  tff(c_954, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_942])).
% 15.85/8.32  tff(c_955, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_60, c_954])).
% 15.85/8.32  tff(c_960, plain, (k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_955])).
% 15.85/8.32  tff(c_1885, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1884, c_960])).
% 15.85/8.32  tff(c_12, plain, (![A_8]: (k1_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_44])).
% 15.85/8.32  tff(c_92, plain, (![A_8]: (k1_relat_1(k6_partfun1(A_8))=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_12])).
% 15.85/8.32  tff(c_62, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_217])).
% 15.85/8.32  tff(c_1988, plain, (![A_237, C_238, B_239]: (k6_partfun1(A_237)=k5_relat_1(C_238, k2_funct_1(C_238)) | k1_xboole_0=B_239 | ~v2_funct_1(C_238) | k2_relset_1(A_237, B_239, C_238)!=B_239 | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_237, B_239))) | ~v1_funct_2(C_238, A_237, B_239) | ~v1_funct_1(C_238))), inference(cnfTransformation, [status(thm)], [f_191])).
% 15.85/8.32  tff(c_1994, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_1988])).
% 15.85/8.32  tff(c_2004, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_70, c_66, c_1994])).
% 15.85/8.32  tff(c_2005, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_62, c_2004])).
% 15.85/8.32  tff(c_26, plain, (![A_15]: (k5_relat_1(A_15, k2_funct_1(A_15))=k6_relat_1(k1_relat_1(A_15)) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_77])).
% 15.85/8.32  tff(c_85, plain, (![A_15]: (k5_relat_1(A_15, k2_funct_1(A_15))=k6_partfun1(k1_relat_1(A_15)) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_26])).
% 15.85/8.32  tff(c_2011, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2005, c_85])).
% 15.85/8.32  tff(c_2020, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_82, c_66, c_2011])).
% 15.85/8.32  tff(c_2093, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2020, c_92])).
% 15.85/8.32  tff(c_2120, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_2093])).
% 15.85/8.32  tff(c_2122, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1885, c_2120])).
% 15.85/8.32  tff(c_2123, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_955])).
% 15.85/8.32  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 15.85/8.32  tff(c_16, plain, (![B_10, A_9]: (k5_relat_1(B_10, k6_relat_1(A_9))=B_10 | ~r1_tarski(k2_relat_1(B_10), A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 15.85/8.32  tff(c_166, plain, (![B_71, A_72]: (k5_relat_1(B_71, k6_partfun1(A_72))=B_71 | ~r1_tarski(k2_relat_1(B_71), A_72) | ~v1_relat_1(B_71))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_16])).
% 15.85/8.32  tff(c_215, plain, (![B_78]: (k5_relat_1(B_78, k6_partfun1(k2_relat_1(B_78)))=B_78 | ~v1_relat_1(B_78))), inference(resolution, [status(thm)], [c_6, c_166])).
% 15.85/8.32  tff(c_224, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_192, c_215])).
% 15.85/8.32  tff(c_231, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_148, c_224])).
% 15.85/8.32  tff(c_20, plain, (![A_11]: (v1_funct_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 15.85/8.32  tff(c_88, plain, (![A_11]: (v1_funct_1(k6_partfun1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_20])).
% 15.85/8.32  tff(c_2221, plain, (![E_256, F_258, A_255, D_259, C_257, B_260]: (k1_partfun1(A_255, B_260, C_257, D_259, E_256, F_258)=k5_relat_1(E_256, F_258) | ~m1_subset_1(F_258, k1_zfmisc_1(k2_zfmisc_1(C_257, D_259))) | ~v1_funct_1(F_258) | ~m1_subset_1(E_256, k1_zfmisc_1(k2_zfmisc_1(A_255, B_260))) | ~v1_funct_1(E_256))), inference(cnfTransformation, [status(thm)], [f_130])).
% 15.85/8.32  tff(c_2223, plain, (![A_255, B_260, A_26, E_256]: (k1_partfun1(A_255, B_260, A_26, A_26, E_256, k6_partfun1(A_26))=k5_relat_1(E_256, k6_partfun1(A_26)) | ~v1_funct_1(k6_partfun1(A_26)) | ~m1_subset_1(E_256, k1_zfmisc_1(k2_zfmisc_1(A_255, B_260))) | ~v1_funct_1(E_256))), inference(resolution, [status(thm)], [c_83, c_2221])).
% 15.85/8.32  tff(c_4074, plain, (![A_387, B_388, A_389, E_390]: (k1_partfun1(A_387, B_388, A_389, A_389, E_390, k6_partfun1(A_389))=k5_relat_1(E_390, k6_partfun1(A_389)) | ~m1_subset_1(E_390, k1_zfmisc_1(k2_zfmisc_1(A_387, B_388))) | ~v1_funct_1(E_390))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_2223])).
% 15.85/8.32  tff(c_4092, plain, (![A_389]: (k1_partfun1('#skF_1', '#skF_2', A_389, A_389, '#skF_3', k6_partfun1(A_389))=k5_relat_1('#skF_3', k6_partfun1(A_389)) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_78, c_4074])).
% 15.85/8.32  tff(c_4600, plain, (![A_419]: (k1_partfun1('#skF_1', '#skF_2', A_419, A_419, '#skF_3', k6_partfun1(A_419))=k5_relat_1('#skF_3', k6_partfun1(A_419)))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_4092])).
% 15.85/8.32  tff(c_38, plain, (![C_29, D_30, B_28, F_32, A_27, E_31]: (m1_subset_1(k1_partfun1(A_27, B_28, C_29, D_30, E_31, F_32), k1_zfmisc_1(k2_zfmisc_1(A_27, D_30))) | ~m1_subset_1(F_32, k1_zfmisc_1(k2_zfmisc_1(C_29, D_30))) | ~v1_funct_1(F_32) | ~m1_subset_1(E_31, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))) | ~v1_funct_1(E_31))), inference(cnfTransformation, [status(thm)], [f_120])).
% 15.85/8.32  tff(c_4612, plain, (![A_419]: (m1_subset_1(k5_relat_1('#skF_3', k6_partfun1(A_419)), k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_419))) | ~m1_subset_1(k6_partfun1(A_419), k1_zfmisc_1(k2_zfmisc_1(A_419, A_419))) | ~v1_funct_1(k6_partfun1(A_419)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4600, c_38])).
% 15.85/8.32  tff(c_4639, plain, (![A_421]: (m1_subset_1(k5_relat_1('#skF_3', k6_partfun1(A_421)), k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_421))))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_88, c_83, c_4612])).
% 15.85/8.32  tff(c_8, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 15.85/8.32  tff(c_4673, plain, (![A_421]: (v1_relat_1(k5_relat_1('#skF_3', k6_partfun1(A_421))) | ~v1_relat_1(k2_zfmisc_1('#skF_1', A_421)))), inference(resolution, [status(thm)], [c_4639, c_8])).
% 15.85/8.32  tff(c_4721, plain, (![A_421]: (v1_relat_1(k5_relat_1('#skF_3', k6_partfun1(A_421))))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_4673])).
% 15.85/8.32  tff(c_4117, plain, (![A_389]: (k1_partfun1('#skF_1', '#skF_2', A_389, A_389, '#skF_3', k6_partfun1(A_389))=k5_relat_1('#skF_3', k6_partfun1(A_389)))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_4092])).
% 15.85/8.32  tff(c_2164, plain, (![E_244, A_246, B_245, D_243, C_242, F_241]: (v1_funct_1(k1_partfun1(A_246, B_245, C_242, D_243, E_244, F_241)) | ~m1_subset_1(F_241, k1_zfmisc_1(k2_zfmisc_1(C_242, D_243))) | ~v1_funct_1(F_241) | ~m1_subset_1(E_244, k1_zfmisc_1(k2_zfmisc_1(A_246, B_245))) | ~v1_funct_1(E_244))), inference(cnfTransformation, [status(thm)], [f_120])).
% 15.85/8.32  tff(c_2166, plain, (![A_246, B_245, A_26, E_244]: (v1_funct_1(k1_partfun1(A_246, B_245, A_26, A_26, E_244, k6_partfun1(A_26))) | ~v1_funct_1(k6_partfun1(A_26)) | ~m1_subset_1(E_244, k1_zfmisc_1(k2_zfmisc_1(A_246, B_245))) | ~v1_funct_1(E_244))), inference(resolution, [status(thm)], [c_83, c_2164])).
% 15.85/8.32  tff(c_2238, plain, (![A_262, B_263, A_264, E_265]: (v1_funct_1(k1_partfun1(A_262, B_263, A_264, A_264, E_265, k6_partfun1(A_264))) | ~m1_subset_1(E_265, k1_zfmisc_1(k2_zfmisc_1(A_262, B_263))) | ~v1_funct_1(E_265))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_2166])).
% 15.85/8.32  tff(c_2244, plain, (![A_264]: (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', A_264, A_264, '#skF_3', k6_partfun1(A_264))) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_78, c_2238])).
% 15.85/8.32  tff(c_2253, plain, (![A_264]: (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', A_264, A_264, '#skF_3', k6_partfun1(A_264))))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2244])).
% 15.85/8.32  tff(c_4599, plain, (![A_264]: (v1_funct_1(k5_relat_1('#skF_3', k6_partfun1(A_264))))), inference(demodulation, [status(thm), theory('equality')], [c_4117, c_2253])).
% 15.85/8.32  tff(c_2124, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_955])).
% 15.85/8.32  tff(c_2125, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2124, c_190])).
% 15.85/8.32  tff(c_2328, plain, (![B_275, C_276, A_277]: (k6_partfun1(B_275)=k5_relat_1(k2_funct_1(C_276), C_276) | k1_xboole_0=B_275 | ~v2_funct_1(C_276) | k2_relset_1(A_277, B_275, C_276)!=B_275 | ~m1_subset_1(C_276, k1_zfmisc_1(k2_zfmisc_1(A_277, B_275))) | ~v1_funct_2(C_276, A_277, B_275) | ~v1_funct_1(C_276))), inference(cnfTransformation, [status(thm)], [f_191])).
% 15.85/8.32  tff(c_2332, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_2328])).
% 15.85/8.32  tff(c_2340, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_2125, c_2332])).
% 15.85/8.32  tff(c_2341, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_4') | k1_relat_1('#skF_3')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_64, c_2340])).
% 15.85/8.32  tff(c_2365, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2341])).
% 15.85/8.32  tff(c_2401, plain, (![A_283, C_284, B_285]: (k6_partfun1(A_283)=k5_relat_1(C_284, k2_funct_1(C_284)) | k1_xboole_0=B_285 | ~v2_funct_1(C_284) | k2_relset_1(A_283, B_285, C_284)!=B_285 | ~m1_subset_1(C_284, k1_zfmisc_1(k2_zfmisc_1(A_283, B_285))) | ~v1_funct_2(C_284, A_283, B_285) | ~v1_funct_1(C_284))), inference(cnfTransformation, [status(thm)], [f_191])).
% 15.85/8.32  tff(c_2407, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_2401])).
% 15.85/8.32  tff(c_2417, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_70, c_66, c_2407])).
% 15.85/8.32  tff(c_2418, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_62, c_2417])).
% 15.85/8.32  tff(c_2424, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2418, c_85])).
% 15.85/8.32  tff(c_2433, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_148, c_82, c_66, c_2424])).
% 15.85/8.32  tff(c_2504, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2433, c_92])).
% 15.85/8.32  tff(c_2530, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_2504])).
% 15.85/8.32  tff(c_2532, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2365, c_2530])).
% 15.85/8.32  tff(c_2533, plain, (~v2_funct_1('#skF_4') | k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2341])).
% 15.85/8.32  tff(c_2555, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_2533])).
% 15.85/8.32  tff(c_18, plain, (![A_11]: (v1_relat_1(k6_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 15.85/8.32  tff(c_89, plain, (![A_11]: (v1_relat_1(k6_partfun1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_18])).
% 15.85/8.32  tff(c_14, plain, (![A_8]: (k2_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_44])).
% 15.85/8.32  tff(c_91, plain, (![A_8]: (k2_relat_1(k6_partfun1(A_8))=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_14])).
% 15.85/8.32  tff(c_227, plain, (![A_8]: (k5_relat_1(k6_partfun1(A_8), k6_partfun1(A_8))=k6_partfun1(A_8) | ~v1_relat_1(k6_partfun1(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_91, c_215])).
% 15.85/8.32  tff(c_233, plain, (![A_8]: (k5_relat_1(k6_partfun1(A_8), k6_partfun1(A_8))=k6_partfun1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_227])).
% 15.85/8.32  tff(c_22, plain, (![A_12, B_14]: (v2_funct_1(A_12) | k6_relat_1(k1_relat_1(A_12))!=k5_relat_1(A_12, B_14) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_67])).
% 15.85/8.32  tff(c_360, plain, (![A_89, B_90]: (v2_funct_1(A_89) | k6_partfun1(k1_relat_1(A_89))!=k5_relat_1(A_89, B_90) | ~v1_funct_1(B_90) | ~v1_relat_1(B_90) | ~v1_funct_1(A_89) | ~v1_relat_1(A_89))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_22])).
% 15.85/8.32  tff(c_368, plain, (![A_8]: (v2_funct_1(k6_partfun1(A_8)) | k6_partfun1(k1_relat_1(k6_partfun1(A_8)))!=k6_partfun1(A_8) | ~v1_funct_1(k6_partfun1(A_8)) | ~v1_relat_1(k6_partfun1(A_8)) | ~v1_funct_1(k6_partfun1(A_8)) | ~v1_relat_1(k6_partfun1(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_233, c_360])).
% 15.85/8.32  tff(c_382, plain, (![A_8]: (v2_funct_1(k6_partfun1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_88, c_89, c_88, c_92, c_368])).
% 15.85/8.32  tff(c_3219, plain, (![C_338, B_334, D_337, E_336, A_335]: (k1_xboole_0=C_338 | v2_funct_1(E_336) | k2_relset_1(A_335, B_334, D_337)!=B_334 | ~v2_funct_1(k1_partfun1(A_335, B_334, B_334, C_338, D_337, E_336)) | ~m1_subset_1(E_336, k1_zfmisc_1(k2_zfmisc_1(B_334, C_338))) | ~v1_funct_2(E_336, B_334, C_338) | ~v1_funct_1(E_336) | ~m1_subset_1(D_337, k1_zfmisc_1(k2_zfmisc_1(A_335, B_334))) | ~v1_funct_2(D_337, A_335, B_334) | ~v1_funct_1(D_337))), inference(cnfTransformation, [status(thm)], [f_175])).
% 15.85/8.32  tff(c_3229, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_926, c_3219])).
% 15.85/8.32  tff(c_3240, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_76, c_74, c_72, c_382, c_70, c_3229])).
% 15.85/8.32  tff(c_3242, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2555, c_64, c_3240])).
% 15.85/8.32  tff(c_3244, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_2533])).
% 15.85/8.32  tff(c_2534, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_2341])).
% 15.85/8.32  tff(c_2539, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2534, c_2125])).
% 15.85/8.32  tff(c_3363, plain, (![A_343, C_344, B_345]: (k6_partfun1(A_343)=k5_relat_1(C_344, k2_funct_1(C_344)) | k1_xboole_0=B_345 | ~v2_funct_1(C_344) | k2_relset_1(A_343, B_345, C_344)!=B_345 | ~m1_subset_1(C_344, k1_zfmisc_1(k2_zfmisc_1(A_343, B_345))) | ~v1_funct_2(C_344, A_343, B_345) | ~v1_funct_1(C_344))), inference(cnfTransformation, [status(thm)], [f_191])).
% 15.85/8.32  tff(c_3367, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_3363])).
% 15.85/8.32  tff(c_3375, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_2539, c_3244, c_3367])).
% 15.85/8.32  tff(c_3376, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_64, c_3375])).
% 15.85/8.32  tff(c_3404, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3376, c_85])).
% 15.85/8.32  tff(c_3413, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_76, c_3244, c_3404])).
% 15.85/8.32  tff(c_3482, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3413, c_92])).
% 15.85/8.32  tff(c_3505, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_3482])).
% 15.85/8.32  tff(c_2540, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2534, c_2124])).
% 15.85/8.32  tff(c_4624, plain, (![A_419]: (m1_subset_1(k5_relat_1('#skF_3', k6_partfun1(A_419)), k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_419))))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_88, c_83, c_4612])).
% 15.85/8.32  tff(c_3531, plain, (![B_350, D_348, A_351, F_346, E_349, C_347]: (m1_subset_1(k1_partfun1(A_351, B_350, C_347, D_348, E_349, F_346), k1_zfmisc_1(k2_zfmisc_1(A_351, D_348))) | ~m1_subset_1(F_346, k1_zfmisc_1(k2_zfmisc_1(C_347, D_348))) | ~v1_funct_1(F_346) | ~m1_subset_1(E_349, k1_zfmisc_1(k2_zfmisc_1(A_351, B_350))) | ~v1_funct_1(E_349))), inference(cnfTransformation, [status(thm)], [f_120])).
% 15.85/8.32  tff(c_2225, plain, (![A_255, B_260, E_256]: (k1_partfun1(A_255, B_260, '#skF_2', '#skF_1', E_256, '#skF_4')=k5_relat_1(E_256, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_256, k1_zfmisc_1(k2_zfmisc_1(A_255, B_260))) | ~v1_funct_1(E_256))), inference(resolution, [status(thm)], [c_72, c_2221])).
% 15.85/8.32  tff(c_2233, plain, (![A_255, B_260, E_256]: (k1_partfun1(A_255, B_260, '#skF_2', '#skF_1', E_256, '#skF_4')=k5_relat_1(E_256, '#skF_4') | ~m1_subset_1(E_256, k1_zfmisc_1(k2_zfmisc_1(A_255, B_260))) | ~v1_funct_1(E_256))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2225])).
% 15.85/8.32  tff(c_8105, plain, (![C_674, E_673, D_672, F_675, B_676, A_677]: (k1_partfun1(A_677, D_672, '#skF_2', '#skF_1', k1_partfun1(A_677, B_676, C_674, D_672, E_673, F_675), '#skF_4')=k5_relat_1(k1_partfun1(A_677, B_676, C_674, D_672, E_673, F_675), '#skF_4') | ~v1_funct_1(k1_partfun1(A_677, B_676, C_674, D_672, E_673, F_675)) | ~m1_subset_1(F_675, k1_zfmisc_1(k2_zfmisc_1(C_674, D_672))) | ~v1_funct_1(F_675) | ~m1_subset_1(E_673, k1_zfmisc_1(k2_zfmisc_1(A_677, B_676))) | ~v1_funct_1(E_673))), inference(resolution, [status(thm)], [c_3531, c_2233])).
% 15.85/8.32  tff(c_8183, plain, (![A_389]: (k1_partfun1('#skF_1', A_389, '#skF_2', '#skF_1', k1_partfun1('#skF_1', '#skF_2', A_389, A_389, '#skF_3', k6_partfun1(A_389)), '#skF_4')=k5_relat_1(k1_partfun1('#skF_1', '#skF_2', A_389, A_389, '#skF_3', k6_partfun1(A_389)), '#skF_4') | ~v1_funct_1(k5_relat_1('#skF_3', k6_partfun1(A_389))) | ~m1_subset_1(k6_partfun1(A_389), k1_zfmisc_1(k2_zfmisc_1(A_389, A_389))) | ~v1_funct_1(k6_partfun1(A_389)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4117, c_8105])).
% 15.85/8.32  tff(c_12199, plain, (![A_784]: (k1_partfun1('#skF_1', A_784, '#skF_2', '#skF_1', k5_relat_1('#skF_3', k6_partfun1(A_784)), '#skF_4')=k5_relat_1(k5_relat_1('#skF_3', k6_partfun1(A_784)), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_88, c_83, c_4599, c_4117, c_4117, c_8183])).
% 15.85/8.32  tff(c_12259, plain, (![A_784]: (m1_subset_1(k5_relat_1(k5_relat_1('#skF_3', k6_partfun1(A_784)), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1(k5_relat_1('#skF_3', k6_partfun1(A_784)), k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_784))) | ~v1_funct_1(k5_relat_1('#skF_3', k6_partfun1(A_784))))), inference(superposition, [status(thm), theory('equality')], [c_12199, c_38])).
% 15.85/8.32  tff(c_12325, plain, (![A_784]: (m1_subset_1(k5_relat_1(k5_relat_1('#skF_3', k6_partfun1(A_784)), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_4599, c_4624, c_76, c_72, c_12259])).
% 15.85/8.32  tff(c_2300, plain, (![A_272, B_273, E_274]: (k1_partfun1(A_272, B_273, '#skF_2', '#skF_1', E_274, '#skF_4')=k5_relat_1(E_274, '#skF_4') | ~m1_subset_1(E_274, k1_zfmisc_1(k2_zfmisc_1(A_272, B_273))) | ~v1_funct_1(E_274))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2225])).
% 15.85/8.32  tff(c_2309, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_2300])).
% 15.85/8.32  tff(c_2318, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_926, c_2309])).
% 15.85/8.32  tff(c_90, plain, (![B_10, A_9]: (k5_relat_1(B_10, k6_partfun1(A_9))=B_10 | ~r1_tarski(k2_relat_1(B_10), A_9) | ~v1_relat_1(B_10))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_16])).
% 15.85/8.32  tff(c_196, plain, (![A_9]: (k5_relat_1('#skF_3', k6_partfun1(A_9))='#skF_3' | ~r1_tarski('#skF_2', A_9) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_192, c_90])).
% 15.85/8.32  tff(c_200, plain, (![A_9]: (k5_relat_1('#skF_3', k6_partfun1(A_9))='#skF_3' | ~r1_tarski('#skF_2', A_9))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_196])).
% 15.85/8.32  tff(c_8340, plain, (![A_389]: (k1_partfun1('#skF_1', A_389, '#skF_2', '#skF_1', k5_relat_1('#skF_3', k6_partfun1(A_389)), '#skF_4')=k5_relat_1(k5_relat_1('#skF_3', k6_partfun1(A_389)), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_88, c_83, c_4599, c_4117, c_4117, c_8183])).
% 15.85/8.32  tff(c_32, plain, (![A_22, B_23, D_25]: (r2_relset_1(A_22, B_23, D_25, D_25) | ~m1_subset_1(D_25, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 15.85/8.32  tff(c_3581, plain, (![B_350, D_348, A_351, F_346, E_349, C_347]: (r2_relset_1(A_351, D_348, k1_partfun1(A_351, B_350, C_347, D_348, E_349, F_346), k1_partfun1(A_351, B_350, C_347, D_348, E_349, F_346)) | ~m1_subset_1(F_346, k1_zfmisc_1(k2_zfmisc_1(C_347, D_348))) | ~v1_funct_1(F_346) | ~m1_subset_1(E_349, k1_zfmisc_1(k2_zfmisc_1(A_351, B_350))) | ~v1_funct_1(E_349))), inference(resolution, [status(thm)], [c_3531, c_32])).
% 15.85/8.32  tff(c_12243, plain, (![A_784]: (r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k5_relat_1('#skF_3', k6_partfun1(A_784)), '#skF_4'), k1_partfun1('#skF_1', A_784, '#skF_2', '#skF_1', k5_relat_1('#skF_3', k6_partfun1(A_784)), '#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1(k5_relat_1('#skF_3', k6_partfun1(A_784)), k1_zfmisc_1(k2_zfmisc_1('#skF_1', A_784))) | ~v1_funct_1(k5_relat_1('#skF_3', k6_partfun1(A_784))))), inference(superposition, [status(thm), theory('equality')], [c_12199, c_3581])).
% 15.85/8.32  tff(c_18308, plain, (![A_923]: (r2_relset_1('#skF_1', '#skF_1', k5_relat_1(k5_relat_1('#skF_3', k6_partfun1(A_923)), '#skF_4'), k5_relat_1(k5_relat_1('#skF_3', k6_partfun1(A_923)), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_4599, c_4624, c_76, c_72, c_8340, c_12243])).
% 15.85/8.32  tff(c_18313, plain, (![A_9]: (r2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_4'), k5_relat_1(k5_relat_1('#skF_3', k6_partfun1(A_9)), '#skF_4')) | ~r1_tarski('#skF_2', A_9))), inference(superposition, [status(thm), theory('equality')], [c_200, c_18308])).
% 15.85/8.32  tff(c_18515, plain, (![A_928]: (r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k5_relat_1(k5_relat_1('#skF_3', k6_partfun1(A_928)), '#skF_4')) | ~r1_tarski('#skF_2', A_928))), inference(demodulation, [status(thm), theory('equality')], [c_2318, c_18313])).
% 15.85/8.32  tff(c_34, plain, (![D_25, C_24, A_22, B_23]: (D_25=C_24 | ~r2_relset_1(A_22, B_23, C_24, D_25) | ~m1_subset_1(D_25, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 15.85/8.32  tff(c_18517, plain, (![A_928]: (k5_relat_1(k5_relat_1('#skF_3', k6_partfun1(A_928)), '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k5_relat_1(k5_relat_1('#skF_3', k6_partfun1(A_928)), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~r1_tarski('#skF_2', A_928))), inference(resolution, [status(thm)], [c_18515, c_34])).
% 15.85/8.32  tff(c_18536, plain, (![A_929]: (k5_relat_1(k5_relat_1('#skF_3', k6_partfun1(A_929)), '#skF_4')=k6_partfun1('#skF_1') | ~r1_tarski('#skF_2', A_929))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_12325, c_18517])).
% 15.85/8.32  tff(c_84, plain, (![A_16, B_18]: (k2_funct_1(A_16)=B_18 | k6_partfun1(k2_relat_1(A_16))!=k5_relat_1(B_18, A_16) | k2_relat_1(B_18)!=k1_relat_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_28])).
% 15.85/8.32  tff(c_18574, plain, (![A_929]: (k5_relat_1('#skF_3', k6_partfun1(A_929))=k2_funct_1('#skF_4') | k6_partfun1(k2_relat_1('#skF_4'))!=k6_partfun1('#skF_1') | k2_relat_1(k5_relat_1('#skF_3', k6_partfun1(A_929)))!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(k5_relat_1('#skF_3', k6_partfun1(A_929))) | ~v1_relat_1(k5_relat_1('#skF_3', k6_partfun1(A_929))) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_2', A_929))), inference(superposition, [status(thm), theory('equality')], [c_18536, c_84])).
% 15.85/8.32  tff(c_22465, plain, (![A_1062]: (k5_relat_1('#skF_3', k6_partfun1(A_1062))=k2_funct_1('#skF_4') | k2_relat_1(k5_relat_1('#skF_3', k6_partfun1(A_1062)))!='#skF_2' | ~r1_tarski('#skF_2', A_1062))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_76, c_4721, c_4599, c_3244, c_3505, c_2540, c_18574])).
% 15.85/8.32  tff(c_22474, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))=k2_funct_1('#skF_4') | k2_relat_1('#skF_3')!='#skF_2' | ~r1_tarski('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_231, c_22465])).
% 15.85/8.32  tff(c_22482, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_192, c_231, c_22474])).
% 15.85/8.32  tff(c_22486, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22482, c_3376])).
% 15.85/8.32  tff(c_22489, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2123, c_22486])).
% 15.85/8.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.85/8.32  
% 15.85/8.32  Inference rules
% 15.85/8.32  ----------------------
% 15.85/8.32  #Ref     : 0
% 15.85/8.32  #Sup     : 4608
% 15.85/8.32  #Fact    : 0
% 15.85/8.32  #Define  : 0
% 15.85/8.32  #Split   : 32
% 15.85/8.32  #Chain   : 0
% 15.85/8.32  #Close   : 0
% 15.85/8.32  
% 15.85/8.32  Ordering : KBO
% 15.85/8.32  
% 15.85/8.32  Simplification rules
% 15.85/8.32  ----------------------
% 15.85/8.32  #Subsume      : 188
% 15.85/8.32  #Demod        : 12205
% 15.85/8.32  #Tautology    : 1334
% 15.85/8.32  #SimpNegUnit  : 404
% 15.85/8.32  #BackRed      : 84
% 15.85/8.32  
% 15.85/8.32  #Partial instantiations: 0
% 15.85/8.32  #Strategies tried      : 1
% 15.85/8.32  
% 15.85/8.32  Timing (in seconds)
% 15.85/8.32  ----------------------
% 16.12/8.32  Preprocessing        : 0.41
% 16.12/8.32  Parsing              : 0.22
% 16.12/8.32  CNF conversion       : 0.03
% 16.12/8.32  Main loop            : 7.03
% 16.12/8.32  Inferencing          : 1.40
% 16.12/8.32  Reduction            : 4.07
% 16.12/8.32  Demodulation         : 3.56
% 16.12/8.32  BG Simplification    : 0.13
% 16.12/8.32  Subsumption          : 1.15
% 16.12/8.32  Abstraction          : 0.21
% 16.12/8.32  MUC search           : 0.00
% 16.12/8.32  Cooper               : 0.00
% 16.12/8.32  Total                : 7.51
% 16.12/8.32  Index Insertion      : 0.00
% 16.12/8.32  Index Deletion       : 0.00
% 16.12/8.32  Index Matching       : 0.00
% 16.12/8.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
