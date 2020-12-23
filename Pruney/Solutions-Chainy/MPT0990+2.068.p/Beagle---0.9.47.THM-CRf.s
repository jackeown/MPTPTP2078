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
% DateTime   : Thu Dec  3 10:13:05 EST 2020

% Result     : Theorem 6.94s
% Output     : CNFRefutation 7.09s
% Verified   : 
% Statistics : Number of formulae       :  170 (1298 expanded)
%              Number of leaves         :   45 ( 483 expanded)
%              Depth                    :   22
%              Number of atoms          :  371 (5682 expanded)
%              Number of equality atoms :  138 (2002 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_210,negated_conjecture,(
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

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_123,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_113,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_109,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_184,axiom,(
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

tff(f_142,axiom,(
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

tff(f_125,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_71,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_168,axiom,(
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

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

tff(c_62,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_74,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_144,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_156,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_144])).

tff(c_84,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_80,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_78,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_874,plain,(
    ! [C_132,A_130,D_134,E_131,B_135,F_133] :
      ( k1_partfun1(A_130,B_135,C_132,D_134,E_131,F_133) = k5_relat_1(E_131,F_133)
      | ~ m1_subset_1(F_133,k1_zfmisc_1(k2_zfmisc_1(C_132,D_134)))
      | ~ v1_funct_1(F_133)
      | ~ m1_subset_1(E_131,k1_zfmisc_1(k2_zfmisc_1(A_130,B_135)))
      | ~ v1_funct_1(E_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_880,plain,(
    ! [A_130,B_135,E_131] :
      ( k1_partfun1(A_130,B_135,'#skF_2','#skF_1',E_131,'#skF_4') = k5_relat_1(E_131,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_131,k1_zfmisc_1(k2_zfmisc_1(A_130,B_135)))
      | ~ v1_funct_1(E_131) ) ),
    inference(resolution,[status(thm)],[c_74,c_874])).

tff(c_918,plain,(
    ! [A_143,B_144,E_145] :
      ( k1_partfun1(A_143,B_144,'#skF_2','#skF_1',E_145,'#skF_4') = k5_relat_1(E_145,'#skF_4')
      | ~ m1_subset_1(E_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144)))
      | ~ v1_funct_1(E_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_880])).

tff(c_924,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_918])).

tff(c_931,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_924])).

tff(c_42,plain,(
    ! [A_32] : m1_subset_1(k6_partfun1(A_32),k1_zfmisc_1(k2_zfmisc_1(A_32,A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_70,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_550,plain,(
    ! [D_94,C_95,A_96,B_97] :
      ( D_94 = C_95
      | ~ r2_relset_1(A_96,B_97,C_95,D_94)
      | ~ m1_subset_1(D_94,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97)))
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_558,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_70,c_550])).

tff(c_573,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_558])).

tff(c_584,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_573])).

tff(c_1099,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_931,c_584])).

tff(c_1110,plain,(
    ! [A_154,F_155,E_157,C_156,B_153,D_152] :
      ( m1_subset_1(k1_partfun1(A_154,B_153,C_156,D_152,E_157,F_155),k1_zfmisc_1(k2_zfmisc_1(A_154,D_152)))
      | ~ m1_subset_1(F_155,k1_zfmisc_1(k2_zfmisc_1(C_156,D_152)))
      | ~ v1_funct_1(F_155)
      | ~ m1_subset_1(E_157,k1_zfmisc_1(k2_zfmisc_1(A_154,B_153)))
      | ~ v1_funct_1(E_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1143,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_931,c_1110])).

tff(c_1166,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_78,c_74,c_1143])).

tff(c_1168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1099,c_1166])).

tff(c_1169,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_573])).

tff(c_1433,plain,(
    ! [B_180,F_178,D_179,C_177,A_175,E_176] :
      ( k1_partfun1(A_175,B_180,C_177,D_179,E_176,F_178) = k5_relat_1(E_176,F_178)
      | ~ m1_subset_1(F_178,k1_zfmisc_1(k2_zfmisc_1(C_177,D_179)))
      | ~ v1_funct_1(F_178)
      | ~ m1_subset_1(E_176,k1_zfmisc_1(k2_zfmisc_1(A_175,B_180)))
      | ~ v1_funct_1(E_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1439,plain,(
    ! [A_175,B_180,E_176] :
      ( k1_partfun1(A_175,B_180,'#skF_2','#skF_1',E_176,'#skF_4') = k5_relat_1(E_176,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_176,k1_zfmisc_1(k2_zfmisc_1(A_175,B_180)))
      | ~ v1_funct_1(E_176) ) ),
    inference(resolution,[status(thm)],[c_74,c_1433])).

tff(c_1480,plain,(
    ! [A_181,B_182,E_183] :
      ( k1_partfun1(A_181,B_182,'#skF_2','#skF_1',E_183,'#skF_4') = k5_relat_1(E_183,'#skF_4')
      | ~ m1_subset_1(E_183,k1_zfmisc_1(k2_zfmisc_1(A_181,B_182)))
      | ~ v1_funct_1(E_183) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1439])).

tff(c_1486,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_1480])).

tff(c_1493,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1169,c_1486])).

tff(c_155,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_144])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_76,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_234,plain,(
    ! [A_77,B_78,C_79] :
      ( k2_relset_1(A_77,B_78,C_79) = k2_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_248,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_234])).

tff(c_1564,plain,(
    ! [B_184,C_185,A_186] :
      ( k6_partfun1(B_184) = k5_relat_1(k2_funct_1(C_185),C_185)
      | k1_xboole_0 = B_184
      | ~ v2_funct_1(C_185)
      | k2_relset_1(A_186,B_184,C_185) != B_184
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k2_zfmisc_1(A_186,B_184)))
      | ~ v1_funct_2(C_185,A_186,B_184)
      | ~ v1_funct_1(C_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_1570,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_1564])).

tff(c_1580,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_248,c_1570])).

tff(c_1581,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1580])).

tff(c_1601,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1581])).

tff(c_82,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_223,plain,(
    ! [A_73,B_74,D_75] :
      ( r2_relset_1(A_73,B_74,D_75,D_75)
      | ~ m1_subset_1(D_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_230,plain,(
    ! [A_32] : r2_relset_1(A_32,A_32,k6_partfun1(A_32),k6_partfun1(A_32)) ),
    inference(resolution,[status(thm)],[c_42,c_223])).

tff(c_2401,plain,(
    ! [A_219,B_220,C_221,D_222] :
      ( k2_relset_1(A_219,B_220,C_221) = B_220
      | ~ r2_relset_1(B_220,B_220,k1_partfun1(B_220,A_219,A_219,B_220,D_222,C_221),k6_partfun1(B_220))
      | ~ m1_subset_1(D_222,k1_zfmisc_1(k2_zfmisc_1(B_220,A_219)))
      | ~ v1_funct_2(D_222,B_220,A_219)
      | ~ v1_funct_1(D_222)
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(A_219,B_220)))
      | ~ v1_funct_2(C_221,A_219,B_220)
      | ~ v1_funct_1(C_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_2407,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1169,c_2401])).

tff(c_2411,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_84,c_82,c_80,c_230,c_248,c_2407])).

tff(c_2413,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1601,c_2411])).

tff(c_2414,plain,
    ( ~ v2_funct_1('#skF_4')
    | k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1581])).

tff(c_2435,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2414])).

tff(c_46,plain,(
    ! [A_39] : k6_relat_1(A_39) = k6_partfun1(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_22,plain,(
    ! [A_14] : v2_funct_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_85,plain,(
    ! [A_14] : v2_funct_1(k6_partfun1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_22])).

tff(c_72,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_3113,plain,(
    ! [E_255,D_256,A_254,C_257,B_253] :
      ( k1_xboole_0 = C_257
      | v2_funct_1(E_255)
      | k2_relset_1(A_254,B_253,D_256) != B_253
      | ~ v2_funct_1(k1_partfun1(A_254,B_253,B_253,C_257,D_256,E_255))
      | ~ m1_subset_1(E_255,k1_zfmisc_1(k2_zfmisc_1(B_253,C_257)))
      | ~ v1_funct_2(E_255,B_253,C_257)
      | ~ v1_funct_1(E_255)
      | ~ m1_subset_1(D_256,k1_zfmisc_1(k2_zfmisc_1(A_254,B_253)))
      | ~ v1_funct_2(D_256,A_254,B_253)
      | ~ v1_funct_1(D_256) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_3117,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_1169,c_3113])).

tff(c_3122,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_76,c_74,c_85,c_72,c_3117])).

tff(c_3124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2435,c_66,c_3122])).

tff(c_3126,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2414])).

tff(c_16,plain,(
    ! [A_12] :
      ( k4_relat_1(A_12) = k2_funct_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_3129,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3126,c_16])).

tff(c_3132,plain,(
    k4_relat_1('#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_78,c_3129])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_relat_1(k4_relat_1(A_1))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3151,plain,
    ( v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3132,c_2])).

tff(c_3165,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_3151])).

tff(c_2415,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1581])).

tff(c_2416,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2415,c_248])).

tff(c_3252,plain,(
    ! [A_261,C_262,B_263] :
      ( k6_partfun1(A_261) = k5_relat_1(C_262,k2_funct_1(C_262))
      | k1_xboole_0 = B_263
      | ~ v2_funct_1(C_262)
      | k2_relset_1(A_261,B_263,C_262) != B_263
      | ~ m1_subset_1(C_262,k1_zfmisc_1(k2_zfmisc_1(A_261,B_263)))
      | ~ v1_funct_2(C_262,A_261,B_263)
      | ~ v1_funct_1(C_262) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_3258,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_3252])).

tff(c_3268,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_2416,c_3126,c_3258])).

tff(c_3269,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_3268])).

tff(c_6,plain,(
    ! [A_2] :
      ( k1_relat_1(k4_relat_1(A_2)) = k2_relat_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3148,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3132,c_6])).

tff(c_3163,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_2415,c_3148])).

tff(c_14,plain,(
    ! [A_11] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_11)),A_11) = A_11
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_86,plain,(
    ! [A_11] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_11)),A_11) = A_11
      | ~ v1_relat_1(A_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_14])).

tff(c_3193,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3163,c_86])).

tff(c_3201,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3165,c_3193])).

tff(c_8,plain,(
    ! [A_3,B_7,C_9] :
      ( k5_relat_1(k5_relat_1(A_3,B_7),C_9) = k5_relat_1(A_3,k5_relat_1(B_7,C_9))
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1503,plain,(
    ! [C_9] :
      ( k5_relat_1(k6_partfun1('#skF_1'),C_9) = k5_relat_1('#skF_3',k5_relat_1('#skF_4',C_9))
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1493,c_8])).

tff(c_3741,plain,(
    ! [C_283] :
      ( k5_relat_1(k6_partfun1('#skF_1'),C_283) = k5_relat_1('#skF_3',k5_relat_1('#skF_4',C_283))
      | ~ v1_relat_1(C_283) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_156,c_1503])).

tff(c_3797,plain,
    ( k5_relat_1('#skF_3',k5_relat_1('#skF_4',k2_funct_1('#skF_4'))) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3201,c_3741])).

tff(c_3840,plain,(
    k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3165,c_3269,c_3797])).

tff(c_68,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_10,plain,(
    ! [A_10] : k1_relat_1(k6_relat_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_88,plain,(
    ! [A_10] : k1_relat_1(k6_partfun1(A_10)) = A_10 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_10])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_3256,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_3252])).

tff(c_3264,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_72,c_68,c_3256])).

tff(c_3265,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3264])).

tff(c_26,plain,(
    ! [A_15] :
      ( k1_relat_1(k5_relat_1(A_15,k2_funct_1(A_15))) = k1_relat_1(A_15)
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3279,plain,
    ( k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3265,c_26])).

tff(c_3290,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_84,c_68,c_88,c_3279])).

tff(c_3308,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3290,c_86])).

tff(c_3316,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_3308])).

tff(c_1568,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_1564])).

tff(c_1576,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_72,c_68,c_1568])).

tff(c_1577,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_1576])).

tff(c_173,plain,(
    ! [A_71] :
      ( k4_relat_1(A_71) = k2_funct_1(A_71)
      | ~ v2_funct_1(A_71)
      | ~ v1_funct_1(A_71)
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_179,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_173])).

tff(c_185,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_84,c_179])).

tff(c_195,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_2])).

tff(c_203,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_195])).

tff(c_3276,plain,(
    ! [C_9] :
      ( k5_relat_1('#skF_3',k5_relat_1(k2_funct_1('#skF_3'),C_9)) = k5_relat_1(k6_partfun1('#skF_1'),C_9)
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3265,c_8])).

tff(c_4066,plain,(
    ! [C_297] :
      ( k5_relat_1('#skF_3',k5_relat_1(k2_funct_1('#skF_3'),C_297)) = k5_relat_1(k6_partfun1('#skF_1'),C_297)
      | ~ v1_relat_1(C_297) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_203,c_3276])).

tff(c_4084,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = k5_relat_1('#skF_3',k6_partfun1('#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1577,c_4066])).

tff(c_4092,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_3840,c_3316,c_4084])).

tff(c_4095,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4092,c_3269])).

tff(c_4207,plain,(
    ! [C_9] :
      ( k5_relat_1(k6_partfun1('#skF_2'),C_9) = k5_relat_1('#skF_4',k5_relat_1('#skF_3',C_9))
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4095,c_8])).

tff(c_4375,plain,(
    ! [C_303] :
      ( k5_relat_1(k6_partfun1('#skF_2'),C_303) = k5_relat_1('#skF_4',k5_relat_1('#skF_3',C_303))
      | ~ v1_relat_1(C_303) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_155,c_4207])).

tff(c_3328,plain,
    ( k1_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3269,c_26])).

tff(c_3339,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_78,c_3126,c_88,c_3328])).

tff(c_3353,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3339,c_86])).

tff(c_3361,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_3353])).

tff(c_4387,plain,
    ( k5_relat_1('#skF_4',k5_relat_1('#skF_3','#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4375,c_3361])).

tff(c_4463,plain,(
    k5_relat_1('#skF_4',k6_partfun1('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_1493,c_4387])).

tff(c_240,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_234])).

tff(c_247,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_240])).

tff(c_192,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_6])).

tff(c_201,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_192])).

tff(c_212,plain,
    ( k5_relat_1(k6_partfun1(k2_relat_1('#skF_3')),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_86])).

tff(c_216,plain,(
    k5_relat_1(k6_partfun1(k2_relat_1('#skF_3')),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_212])).

tff(c_249,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_216])).

tff(c_4425,plain,
    ( k5_relat_1('#skF_4',k5_relat_1('#skF_3',k2_funct_1('#skF_3'))) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4375,c_249])).

tff(c_4479,plain,(
    k5_relat_1('#skF_4',k6_partfun1('#skF_1')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_3265,c_4425])).

tff(c_4516,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4463,c_4479])).

tff(c_4517,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_4516])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 13:33:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.94/2.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.94/2.49  
% 6.94/2.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.94/2.49  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.94/2.49  
% 6.94/2.49  %Foreground sorts:
% 6.94/2.49  
% 6.94/2.49  
% 6.94/2.49  %Background operators:
% 6.94/2.49  
% 6.94/2.49  
% 6.94/2.49  %Foreground operators:
% 6.94/2.49  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.94/2.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.94/2.49  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.94/2.49  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.94/2.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.94/2.49  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.94/2.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.94/2.49  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.94/2.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.94/2.49  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.94/2.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.94/2.49  tff('#skF_2', type, '#skF_2': $i).
% 6.94/2.49  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.94/2.49  tff('#skF_3', type, '#skF_3': $i).
% 6.94/2.49  tff('#skF_1', type, '#skF_1': $i).
% 6.94/2.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.94/2.49  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.94/2.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.94/2.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.94/2.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.94/2.49  tff('#skF_4', type, '#skF_4': $i).
% 6.94/2.49  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.94/2.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.94/2.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.94/2.49  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 6.94/2.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.94/2.49  
% 7.09/2.51  tff(f_210, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 7.09/2.51  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.09/2.51  tff(f_123, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.09/2.51  tff(f_113, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.09/2.51  tff(f_97, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.09/2.51  tff(f_109, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.09/2.51  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.09/2.51  tff(f_184, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 7.09/2.51  tff(f_142, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 7.09/2.51  tff(f_125, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.09/2.51  tff(f_71, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 7.09/2.51  tff(f_168, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 7.09/2.51  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 7.09/2.51  tff(f_29, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 7.09/2.51  tff(f_35, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 7.09/2.51  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 7.09/2.51  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 7.09/2.51  tff(f_49, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 7.09/2.51  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_funct_1)).
% 7.09/2.51  tff(c_62, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_210])).
% 7.09/2.51  tff(c_74, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_210])).
% 7.09/2.51  tff(c_144, plain, (![C_66, A_67, B_68]: (v1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.09/2.51  tff(c_156, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_144])).
% 7.09/2.51  tff(c_84, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_210])).
% 7.09/2.51  tff(c_80, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_210])).
% 7.09/2.51  tff(c_78, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_210])).
% 7.09/2.51  tff(c_874, plain, (![C_132, A_130, D_134, E_131, B_135, F_133]: (k1_partfun1(A_130, B_135, C_132, D_134, E_131, F_133)=k5_relat_1(E_131, F_133) | ~m1_subset_1(F_133, k1_zfmisc_1(k2_zfmisc_1(C_132, D_134))) | ~v1_funct_1(F_133) | ~m1_subset_1(E_131, k1_zfmisc_1(k2_zfmisc_1(A_130, B_135))) | ~v1_funct_1(E_131))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.09/2.51  tff(c_880, plain, (![A_130, B_135, E_131]: (k1_partfun1(A_130, B_135, '#skF_2', '#skF_1', E_131, '#skF_4')=k5_relat_1(E_131, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_131, k1_zfmisc_1(k2_zfmisc_1(A_130, B_135))) | ~v1_funct_1(E_131))), inference(resolution, [status(thm)], [c_74, c_874])).
% 7.09/2.51  tff(c_918, plain, (![A_143, B_144, E_145]: (k1_partfun1(A_143, B_144, '#skF_2', '#skF_1', E_145, '#skF_4')=k5_relat_1(E_145, '#skF_4') | ~m1_subset_1(E_145, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))) | ~v1_funct_1(E_145))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_880])).
% 7.09/2.51  tff(c_924, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_918])).
% 7.09/2.51  tff(c_931, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_924])).
% 7.09/2.51  tff(c_42, plain, (![A_32]: (m1_subset_1(k6_partfun1(A_32), k1_zfmisc_1(k2_zfmisc_1(A_32, A_32))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.09/2.51  tff(c_70, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_210])).
% 7.09/2.51  tff(c_550, plain, (![D_94, C_95, A_96, B_97]: (D_94=C_95 | ~r2_relset_1(A_96, B_97, C_95, D_94) | ~m1_subset_1(D_94, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.09/2.51  tff(c_558, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_70, c_550])).
% 7.09/2.51  tff(c_573, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_558])).
% 7.09/2.51  tff(c_584, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_573])).
% 7.09/2.51  tff(c_1099, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_931, c_584])).
% 7.09/2.51  tff(c_1110, plain, (![A_154, F_155, E_157, C_156, B_153, D_152]: (m1_subset_1(k1_partfun1(A_154, B_153, C_156, D_152, E_157, F_155), k1_zfmisc_1(k2_zfmisc_1(A_154, D_152))) | ~m1_subset_1(F_155, k1_zfmisc_1(k2_zfmisc_1(C_156, D_152))) | ~v1_funct_1(F_155) | ~m1_subset_1(E_157, k1_zfmisc_1(k2_zfmisc_1(A_154, B_153))) | ~v1_funct_1(E_157))), inference(cnfTransformation, [status(thm)], [f_109])).
% 7.09/2.51  tff(c_1143, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_931, c_1110])).
% 7.09/2.51  tff(c_1166, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_78, c_74, c_1143])).
% 7.09/2.51  tff(c_1168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1099, c_1166])).
% 7.09/2.51  tff(c_1169, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_573])).
% 7.09/2.51  tff(c_1433, plain, (![B_180, F_178, D_179, C_177, A_175, E_176]: (k1_partfun1(A_175, B_180, C_177, D_179, E_176, F_178)=k5_relat_1(E_176, F_178) | ~m1_subset_1(F_178, k1_zfmisc_1(k2_zfmisc_1(C_177, D_179))) | ~v1_funct_1(F_178) | ~m1_subset_1(E_176, k1_zfmisc_1(k2_zfmisc_1(A_175, B_180))) | ~v1_funct_1(E_176))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.09/2.51  tff(c_1439, plain, (![A_175, B_180, E_176]: (k1_partfun1(A_175, B_180, '#skF_2', '#skF_1', E_176, '#skF_4')=k5_relat_1(E_176, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_176, k1_zfmisc_1(k2_zfmisc_1(A_175, B_180))) | ~v1_funct_1(E_176))), inference(resolution, [status(thm)], [c_74, c_1433])).
% 7.09/2.51  tff(c_1480, plain, (![A_181, B_182, E_183]: (k1_partfun1(A_181, B_182, '#skF_2', '#skF_1', E_183, '#skF_4')=k5_relat_1(E_183, '#skF_4') | ~m1_subset_1(E_183, k1_zfmisc_1(k2_zfmisc_1(A_181, B_182))) | ~v1_funct_1(E_183))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1439])).
% 7.09/2.51  tff(c_1486, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_1480])).
% 7.09/2.51  tff(c_1493, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_1169, c_1486])).
% 7.09/2.51  tff(c_155, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_144])).
% 7.09/2.51  tff(c_66, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_210])).
% 7.09/2.51  tff(c_76, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_210])).
% 7.09/2.51  tff(c_234, plain, (![A_77, B_78, C_79]: (k2_relset_1(A_77, B_78, C_79)=k2_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.09/2.51  tff(c_248, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_234])).
% 7.09/2.51  tff(c_1564, plain, (![B_184, C_185, A_186]: (k6_partfun1(B_184)=k5_relat_1(k2_funct_1(C_185), C_185) | k1_xboole_0=B_184 | ~v2_funct_1(C_185) | k2_relset_1(A_186, B_184, C_185)!=B_184 | ~m1_subset_1(C_185, k1_zfmisc_1(k2_zfmisc_1(A_186, B_184))) | ~v1_funct_2(C_185, A_186, B_184) | ~v1_funct_1(C_185))), inference(cnfTransformation, [status(thm)], [f_184])).
% 7.09/2.51  tff(c_1570, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_1564])).
% 7.09/2.51  tff(c_1580, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_248, c_1570])).
% 7.09/2.51  tff(c_1581, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_66, c_1580])).
% 7.09/2.51  tff(c_1601, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_1581])).
% 7.09/2.51  tff(c_82, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_210])).
% 7.09/2.51  tff(c_223, plain, (![A_73, B_74, D_75]: (r2_relset_1(A_73, B_74, D_75, D_75) | ~m1_subset_1(D_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.09/2.51  tff(c_230, plain, (![A_32]: (r2_relset_1(A_32, A_32, k6_partfun1(A_32), k6_partfun1(A_32)))), inference(resolution, [status(thm)], [c_42, c_223])).
% 7.09/2.51  tff(c_2401, plain, (![A_219, B_220, C_221, D_222]: (k2_relset_1(A_219, B_220, C_221)=B_220 | ~r2_relset_1(B_220, B_220, k1_partfun1(B_220, A_219, A_219, B_220, D_222, C_221), k6_partfun1(B_220)) | ~m1_subset_1(D_222, k1_zfmisc_1(k2_zfmisc_1(B_220, A_219))) | ~v1_funct_2(D_222, B_220, A_219) | ~v1_funct_1(D_222) | ~m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(A_219, B_220))) | ~v1_funct_2(C_221, A_219, B_220) | ~v1_funct_1(C_221))), inference(cnfTransformation, [status(thm)], [f_142])).
% 7.09/2.51  tff(c_2407, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1169, c_2401])).
% 7.09/2.51  tff(c_2411, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_84, c_82, c_80, c_230, c_248, c_2407])).
% 7.09/2.51  tff(c_2413, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1601, c_2411])).
% 7.09/2.51  tff(c_2414, plain, (~v2_funct_1('#skF_4') | k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1581])).
% 7.09/2.51  tff(c_2435, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_2414])).
% 7.09/2.51  tff(c_46, plain, (![A_39]: (k6_relat_1(A_39)=k6_partfun1(A_39))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.09/2.51  tff(c_22, plain, (![A_14]: (v2_funct_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 7.09/2.51  tff(c_85, plain, (![A_14]: (v2_funct_1(k6_partfun1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_22])).
% 7.09/2.51  tff(c_72, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_210])).
% 7.09/2.51  tff(c_3113, plain, (![E_255, D_256, A_254, C_257, B_253]: (k1_xboole_0=C_257 | v2_funct_1(E_255) | k2_relset_1(A_254, B_253, D_256)!=B_253 | ~v2_funct_1(k1_partfun1(A_254, B_253, B_253, C_257, D_256, E_255)) | ~m1_subset_1(E_255, k1_zfmisc_1(k2_zfmisc_1(B_253, C_257))) | ~v1_funct_2(E_255, B_253, C_257) | ~v1_funct_1(E_255) | ~m1_subset_1(D_256, k1_zfmisc_1(k2_zfmisc_1(A_254, B_253))) | ~v1_funct_2(D_256, A_254, B_253) | ~v1_funct_1(D_256))), inference(cnfTransformation, [status(thm)], [f_168])).
% 7.09/2.51  tff(c_3117, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1169, c_3113])).
% 7.09/2.51  tff(c_3122, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_78, c_76, c_74, c_85, c_72, c_3117])).
% 7.09/2.51  tff(c_3124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2435, c_66, c_3122])).
% 7.09/2.51  tff(c_3126, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_2414])).
% 7.09/2.51  tff(c_16, plain, (![A_12]: (k4_relat_1(A_12)=k2_funct_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.09/2.51  tff(c_3129, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_3126, c_16])).
% 7.09/2.51  tff(c_3132, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_78, c_3129])).
% 7.09/2.51  tff(c_2, plain, (![A_1]: (v1_relat_1(k4_relat_1(A_1)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.09/2.51  tff(c_3151, plain, (v1_relat_1(k2_funct_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3132, c_2])).
% 7.09/2.51  tff(c_3165, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_3151])).
% 7.09/2.51  tff(c_2415, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_1581])).
% 7.09/2.51  tff(c_2416, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2415, c_248])).
% 7.09/2.51  tff(c_3252, plain, (![A_261, C_262, B_263]: (k6_partfun1(A_261)=k5_relat_1(C_262, k2_funct_1(C_262)) | k1_xboole_0=B_263 | ~v2_funct_1(C_262) | k2_relset_1(A_261, B_263, C_262)!=B_263 | ~m1_subset_1(C_262, k1_zfmisc_1(k2_zfmisc_1(A_261, B_263))) | ~v1_funct_2(C_262, A_261, B_263) | ~v1_funct_1(C_262))), inference(cnfTransformation, [status(thm)], [f_184])).
% 7.09/2.51  tff(c_3258, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_3252])).
% 7.09/2.51  tff(c_3268, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_2416, c_3126, c_3258])).
% 7.09/2.51  tff(c_3269, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_66, c_3268])).
% 7.09/2.51  tff(c_6, plain, (![A_2]: (k1_relat_1(k4_relat_1(A_2))=k2_relat_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.09/2.51  tff(c_3148, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3132, c_6])).
% 7.09/2.51  tff(c_3163, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_156, c_2415, c_3148])).
% 7.09/2.51  tff(c_14, plain, (![A_11]: (k5_relat_1(k6_relat_1(k1_relat_1(A_11)), A_11)=A_11 | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.09/2.51  tff(c_86, plain, (![A_11]: (k5_relat_1(k6_partfun1(k1_relat_1(A_11)), A_11)=A_11 | ~v1_relat_1(A_11))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_14])).
% 7.09/2.51  tff(c_3193, plain, (k5_relat_1(k6_partfun1('#skF_1'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3163, c_86])).
% 7.09/2.51  tff(c_3201, plain, (k5_relat_1(k6_partfun1('#skF_1'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3165, c_3193])).
% 7.09/2.51  tff(c_8, plain, (![A_3, B_7, C_9]: (k5_relat_1(k5_relat_1(A_3, B_7), C_9)=k5_relat_1(A_3, k5_relat_1(B_7, C_9)) | ~v1_relat_1(C_9) | ~v1_relat_1(B_7) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.09/2.51  tff(c_1503, plain, (![C_9]: (k5_relat_1(k6_partfun1('#skF_1'), C_9)=k5_relat_1('#skF_3', k5_relat_1('#skF_4', C_9)) | ~v1_relat_1(C_9) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1493, c_8])).
% 7.09/2.51  tff(c_3741, plain, (![C_283]: (k5_relat_1(k6_partfun1('#skF_1'), C_283)=k5_relat_1('#skF_3', k5_relat_1('#skF_4', C_283)) | ~v1_relat_1(C_283))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_156, c_1503])).
% 7.09/2.51  tff(c_3797, plain, (k5_relat_1('#skF_3', k5_relat_1('#skF_4', k2_funct_1('#skF_4')))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3201, c_3741])).
% 7.09/2.51  tff(c_3840, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3165, c_3269, c_3797])).
% 7.09/2.51  tff(c_68, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_210])).
% 7.09/2.51  tff(c_10, plain, (![A_10]: (k1_relat_1(k6_relat_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.09/2.51  tff(c_88, plain, (![A_10]: (k1_relat_1(k6_partfun1(A_10))=A_10)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_10])).
% 7.09/2.51  tff(c_64, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_210])).
% 7.09/2.51  tff(c_3256, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_3252])).
% 7.09/2.51  tff(c_3264, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_72, c_68, c_3256])).
% 7.09/2.52  tff(c_3265, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_3264])).
% 7.09/2.52  tff(c_26, plain, (![A_15]: (k1_relat_1(k5_relat_1(A_15, k2_funct_1(A_15)))=k1_relat_1(A_15) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.09/2.52  tff(c_3279, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3265, c_26])).
% 7.09/2.52  tff(c_3290, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_155, c_84, c_68, c_88, c_3279])).
% 7.09/2.52  tff(c_3308, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3290, c_86])).
% 7.09/2.52  tff(c_3316, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_155, c_3308])).
% 7.09/2.52  tff(c_1568, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_1564])).
% 7.09/2.52  tff(c_1576, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_72, c_68, c_1568])).
% 7.09/2.52  tff(c_1577, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_64, c_1576])).
% 7.09/2.52  tff(c_173, plain, (![A_71]: (k4_relat_1(A_71)=k2_funct_1(A_71) | ~v2_funct_1(A_71) | ~v1_funct_1(A_71) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.09/2.52  tff(c_179, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_173])).
% 7.09/2.52  tff(c_185, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_84, c_179])).
% 7.09/2.52  tff(c_195, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_185, c_2])).
% 7.09/2.52  tff(c_203, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_195])).
% 7.09/2.52  tff(c_3276, plain, (![C_9]: (k5_relat_1('#skF_3', k5_relat_1(k2_funct_1('#skF_3'), C_9))=k5_relat_1(k6_partfun1('#skF_1'), C_9) | ~v1_relat_1(C_9) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3265, c_8])).
% 7.09/2.52  tff(c_4066, plain, (![C_297]: (k5_relat_1('#skF_3', k5_relat_1(k2_funct_1('#skF_3'), C_297))=k5_relat_1(k6_partfun1('#skF_1'), C_297) | ~v1_relat_1(C_297))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_203, c_3276])).
% 7.09/2.52  tff(c_4084, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')=k5_relat_1('#skF_3', k6_partfun1('#skF_2')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1577, c_4066])).
% 7.09/2.52  tff(c_4092, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_155, c_3840, c_3316, c_4084])).
% 7.09/2.52  tff(c_4095, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4092, c_3269])).
% 7.09/2.52  tff(c_4207, plain, (![C_9]: (k5_relat_1(k6_partfun1('#skF_2'), C_9)=k5_relat_1('#skF_4', k5_relat_1('#skF_3', C_9)) | ~v1_relat_1(C_9) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4095, c_8])).
% 7.09/2.52  tff(c_4375, plain, (![C_303]: (k5_relat_1(k6_partfun1('#skF_2'), C_303)=k5_relat_1('#skF_4', k5_relat_1('#skF_3', C_303)) | ~v1_relat_1(C_303))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_155, c_4207])).
% 7.09/2.52  tff(c_3328, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3269, c_26])).
% 7.09/2.52  tff(c_3339, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_156, c_78, c_3126, c_88, c_3328])).
% 7.09/2.52  tff(c_3353, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3339, c_86])).
% 7.09/2.52  tff(c_3361, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_156, c_3353])).
% 7.09/2.52  tff(c_4387, plain, (k5_relat_1('#skF_4', k5_relat_1('#skF_3', '#skF_4'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4375, c_3361])).
% 7.09/2.52  tff(c_4463, plain, (k5_relat_1('#skF_4', k6_partfun1('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_156, c_1493, c_4387])).
% 7.09/2.52  tff(c_240, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_234])).
% 7.09/2.52  tff(c_247, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_240])).
% 7.09/2.52  tff(c_192, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_185, c_6])).
% 7.09/2.52  tff(c_201, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_192])).
% 7.09/2.52  tff(c_212, plain, (k5_relat_1(k6_partfun1(k2_relat_1('#skF_3')), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_201, c_86])).
% 7.09/2.52  tff(c_216, plain, (k5_relat_1(k6_partfun1(k2_relat_1('#skF_3')), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_203, c_212])).
% 7.09/2.52  tff(c_249, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_247, c_216])).
% 7.09/2.52  tff(c_4425, plain, (k5_relat_1('#skF_4', k5_relat_1('#skF_3', k2_funct_1('#skF_3')))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_4375, c_249])).
% 7.09/2.52  tff(c_4479, plain, (k5_relat_1('#skF_4', k6_partfun1('#skF_1'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_203, c_3265, c_4425])).
% 7.09/2.52  tff(c_4516, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4463, c_4479])).
% 7.09/2.52  tff(c_4517, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_4516])).
% 7.09/2.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.09/2.52  
% 7.09/2.52  Inference rules
% 7.09/2.52  ----------------------
% 7.09/2.52  #Ref     : 0
% 7.09/2.52  #Sup     : 1005
% 7.09/2.52  #Fact    : 0
% 7.09/2.52  #Define  : 0
% 7.09/2.52  #Split   : 17
% 7.09/2.52  #Chain   : 0
% 7.09/2.52  #Close   : 0
% 7.09/2.52  
% 7.09/2.52  Ordering : KBO
% 7.09/2.52  
% 7.09/2.52  Simplification rules
% 7.09/2.52  ----------------------
% 7.09/2.52  #Subsume      : 26
% 7.09/2.52  #Demod        : 1480
% 7.09/2.52  #Tautology    : 509
% 7.09/2.52  #SimpNegUnit  : 47
% 7.09/2.52  #BackRed      : 58
% 7.09/2.52  
% 7.09/2.52  #Partial instantiations: 0
% 7.09/2.52  #Strategies tried      : 1
% 7.09/2.52  
% 7.09/2.52  Timing (in seconds)
% 7.09/2.52  ----------------------
% 7.09/2.52  Preprocessing        : 0.43
% 7.09/2.52  Parsing              : 0.22
% 7.09/2.52  CNF conversion       : 0.03
% 7.09/2.52  Main loop            : 1.22
% 7.09/2.52  Inferencing          : 0.42
% 7.09/2.52  Reduction            : 0.47
% 7.09/2.52  Demodulation         : 0.36
% 7.09/2.52  BG Simplification    : 0.05
% 7.09/2.52  Subsumption          : 0.20
% 7.09/2.52  Abstraction          : 0.06
% 7.09/2.52  MUC search           : 0.00
% 7.09/2.52  Cooper               : 0.00
% 7.09/2.52  Total                : 1.70
% 7.09/2.52  Index Insertion      : 0.00
% 7.09/2.52  Index Deletion       : 0.00
% 7.09/2.52  Index Matching       : 0.00
% 7.09/2.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
