%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:07 EST 2020

% Result     : Theorem 8.03s
% Output     : CNFRefutation 8.03s
% Verified   : 
% Statistics : Number of formulae       :  188 (1012 expanded)
%              Number of leaves         :   42 ( 383 expanded)
%              Depth                    :   16
%              Number of atoms          :  561 (4681 expanded)
%              Number of equality atoms :  194 (1477 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_261,negated_conjecture,(
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

tff(f_124,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_219,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_45,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_148,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_158,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_132,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_144,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_160,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_108,axiom,(
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

tff(f_235,axiom,(
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

tff(f_81,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A)
        & v1_relat_1(B)
        & v1_funct_1(B)
        & v2_funct_1(B) )
     => ( v1_relat_1(k5_relat_1(A,B))
        & v2_funct_1(k5_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_funct_1)).

tff(f_203,axiom,(
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

tff(f_177,axiom,(
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

tff(f_91,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
          & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

tff(c_72,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_88,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_86,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_84,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_189,plain,(
    ! [A_71,B_72,C_73] :
      ( k2_relset_1(A_71,B_72,C_73) = k2_relat_1(C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_71,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_200,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_189])).

tff(c_931,plain,(
    ! [C_158,A_159,B_160] :
      ( v1_funct_1(k2_funct_1(C_158))
      | k2_relset_1(A_159,B_160,C_158) != B_160
      | ~ v2_funct_1(C_158)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_159,B_160)))
      | ~ v1_funct_2(C_158,A_159,B_160)
      | ~ v1_funct_1(C_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_937,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_931])).

tff(c_945,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_200,c_937])).

tff(c_949,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_945])).

tff(c_76,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_94,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_92,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_90,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_113,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_125,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_113])).

tff(c_78,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_6,plain,(
    ! [A_2] :
      ( v2_funct_1(k2_funct_1(A_2))
      | ~ v2_funct_1(A_2)
      | ~ v1_funct_1(A_2)
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_46,plain,(
    ! [A_28] : m1_subset_1(k6_partfun1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_123,plain,(
    ! [A_28] : v1_relat_1(k6_partfun1(A_28)) ),
    inference(resolution,[status(thm)],[c_46,c_113])).

tff(c_625,plain,(
    ! [D_137,A_139,B_138,E_141,F_140,C_142] :
      ( k1_partfun1(A_139,B_138,C_142,D_137,E_141,F_140) = k5_relat_1(E_141,F_140)
      | ~ m1_subset_1(F_140,k1_zfmisc_1(k2_zfmisc_1(C_142,D_137)))
      | ~ v1_funct_1(F_140)
      | ~ m1_subset_1(E_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_138)))
      | ~ v1_funct_1(E_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_631,plain,(
    ! [A_139,B_138,E_141] :
      ( k1_partfun1(A_139,B_138,'#skF_2','#skF_1',E_141,'#skF_4') = k5_relat_1(E_141,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_138)))
      | ~ v1_funct_1(E_141) ) ),
    inference(resolution,[status(thm)],[c_84,c_625])).

tff(c_642,plain,(
    ! [A_143,B_144,E_145] :
      ( k1_partfun1(A_143,B_144,'#skF_2','#skF_1',E_145,'#skF_4') = k5_relat_1(E_145,'#skF_4')
      | ~ m1_subset_1(E_145,k1_zfmisc_1(k2_zfmisc_1(A_143,B_144)))
      | ~ v1_funct_1(E_145) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_631])).

tff(c_654,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_642])).

tff(c_662,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_654])).

tff(c_80,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_270,plain,(
    ! [D_83,C_84,A_85,B_86] :
      ( D_83 = C_84
      | ~ r2_relset_1(A_85,B_86,C_84,D_83)
      | ~ m1_subset_1(D_83,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86)))
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_278,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_80,c_270])).

tff(c_293,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_278])).

tff(c_294,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_293])).

tff(c_815,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_662,c_294])).

tff(c_856,plain,(
    ! [A_152,D_156,F_155,B_157,C_153,E_154] :
      ( m1_subset_1(k1_partfun1(A_152,B_157,C_153,D_156,E_154,F_155),k1_zfmisc_1(k2_zfmisc_1(A_152,D_156)))
      | ~ m1_subset_1(F_155,k1_zfmisc_1(k2_zfmisc_1(C_153,D_156)))
      | ~ v1_funct_1(F_155)
      | ~ m1_subset_1(E_154,k1_zfmisc_1(k2_zfmisc_1(A_152,B_157)))
      | ~ v1_funct_1(E_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_898,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_662,c_856])).

tff(c_918,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_90,c_88,c_84,c_898])).

tff(c_921,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_815,c_918])).

tff(c_922,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_293])).

tff(c_1030,plain,(
    ! [D_173,C_170,B_174,A_169,F_172,E_171] :
      ( v1_funct_1(k1_partfun1(A_169,B_174,C_170,D_173,E_171,F_172))
      | ~ m1_subset_1(F_172,k1_zfmisc_1(k2_zfmisc_1(C_170,D_173)))
      | ~ v1_funct_1(F_172)
      | ~ m1_subset_1(E_171,k1_zfmisc_1(k2_zfmisc_1(A_169,B_174)))
      | ~ v1_funct_1(E_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_1034,plain,(
    ! [A_169,B_174,E_171] :
      ( v1_funct_1(k1_partfun1(A_169,B_174,'#skF_2','#skF_1',E_171,'#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_171,k1_zfmisc_1(k2_zfmisc_1(A_169,B_174)))
      | ~ v1_funct_1(E_171) ) ),
    inference(resolution,[status(thm)],[c_84,c_1030])).

tff(c_1044,plain,(
    ! [A_175,B_176,E_177] :
      ( v1_funct_1(k1_partfun1(A_175,B_176,'#skF_2','#skF_1',E_177,'#skF_4'))
      | ~ m1_subset_1(E_177,k1_zfmisc_1(k2_zfmisc_1(A_175,B_176)))
      | ~ v1_funct_1(E_177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1034])).

tff(c_1053,plain,
    ( v1_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_1044])).

tff(c_1060,plain,(
    v1_funct_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_922,c_1053])).

tff(c_82,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_198,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_189])).

tff(c_202,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_198])).

tff(c_50,plain,(
    ! [A_35] : k6_relat_1(A_35) = k6_partfun1(A_35) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_28,plain,(
    ! [A_8,B_10] :
      ( k2_funct_1(A_8) = B_10
      | k6_relat_1(k2_relat_1(A_8)) != k5_relat_1(B_10,A_8)
      | k2_relat_1(B_10) != k1_relat_1(A_8)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(B_10)
      | ~ v1_relat_1(B_10)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_951,plain,(
    ! [A_162,B_163] :
      ( k2_funct_1(A_162) = B_163
      | k6_partfun1(k2_relat_1(A_162)) != k5_relat_1(B_163,A_162)
      | k2_relat_1(B_163) != k1_relat_1(A_162)
      | ~ v2_funct_1(A_162)
      | ~ v1_funct_1(B_163)
      | ~ v1_relat_1(B_163)
      | ~ v1_funct_1(A_162)
      | ~ v1_relat_1(A_162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_28])).

tff(c_957,plain,(
    ! [B_163] :
      ( k2_funct_1('#skF_3') = B_163
      | k5_relat_1(B_163,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_163) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_163)
      | ~ v1_relat_1(B_163)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_951])).

tff(c_962,plain,(
    ! [B_164] :
      ( k2_funct_1('#skF_3') = B_164
      | k5_relat_1(B_164,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_164) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_164)
      | ~ v1_relat_1(B_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_94,c_78,c_957])).

tff(c_979,plain,(
    ! [A_28] :
      ( k6_partfun1(A_28) = k2_funct_1('#skF_3')
      | k5_relat_1(k6_partfun1(A_28),'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(k6_partfun1(A_28)) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(k6_partfun1(A_28)) ) ),
    inference(resolution,[status(thm)],[c_123,c_962])).

tff(c_1064,plain,
    ( k6_partfun1('#skF_1') = k2_funct_1('#skF_3')
    | k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1(k6_partfun1('#skF_1')) != k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1060,c_979])).

tff(c_1084,plain,(
    k2_relat_1(k6_partfun1('#skF_1')) != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1064])).

tff(c_74,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_261])).

tff(c_1340,plain,(
    ! [A_218,C_219,B_220] :
      ( k6_partfun1(A_218) = k5_relat_1(C_219,k2_funct_1(C_219))
      | k1_xboole_0 = B_220
      | ~ v2_funct_1(C_219)
      | k2_relset_1(A_218,B_220,C_219) != B_220
      | ~ m1_subset_1(C_219,k1_zfmisc_1(k2_zfmisc_1(A_218,B_220)))
      | ~ v1_funct_2(C_219,A_218,B_220)
      | ~ v1_funct_1(C_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_1348,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_1340])).

tff(c_1358,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_82,c_78,c_1348])).

tff(c_1359,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1358])).

tff(c_20,plain,(
    ! [A_6] :
      ( k2_relat_1(k5_relat_1(A_6,k2_funct_1(A_6))) = k1_relat_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1378,plain,
    ( k2_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1359,c_20])).

tff(c_1392,plain,(
    k2_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_94,c_78,c_1378])).

tff(c_1394,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1084,c_1392])).

tff(c_1396,plain,(
    k2_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1064])).

tff(c_95,plain,(
    ! [A_8,B_10] :
      ( k2_funct_1(A_8) = B_10
      | k6_partfun1(k2_relat_1(A_8)) != k5_relat_1(B_10,A_8)
      | k2_relat_1(B_10) != k1_relat_1(A_8)
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(B_10)
      | ~ v1_relat_1(B_10)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_28])).

tff(c_1399,plain,(
    ! [B_10] :
      ( k2_funct_1(k6_partfun1('#skF_1')) = B_10
      | k5_relat_1(B_10,k6_partfun1('#skF_1')) != k6_partfun1(k1_relat_1('#skF_3'))
      | k2_relat_1(B_10) != k1_relat_1(k6_partfun1('#skF_1'))
      | ~ v2_funct_1(k6_partfun1('#skF_1'))
      | ~ v1_funct_1(B_10)
      | ~ v1_relat_1(B_10)
      | ~ v1_funct_1(k6_partfun1('#skF_1'))
      | ~ v1_relat_1(k6_partfun1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1396,c_95])).

tff(c_1403,plain,(
    ! [B_10] :
      ( k2_funct_1(k6_partfun1('#skF_1')) = B_10
      | k5_relat_1(B_10,k6_partfun1('#skF_1')) != k6_partfun1(k1_relat_1('#skF_3'))
      | k2_relat_1(B_10) != k1_relat_1(k6_partfun1('#skF_1'))
      | ~ v2_funct_1(k6_partfun1('#skF_1'))
      | ~ v1_funct_1(B_10)
      | ~ v1_relat_1(B_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_1060,c_1399])).

tff(c_1499,plain,(
    ~ v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1403])).

tff(c_1500,plain,(
    ! [C_238,B_239,A_240] :
      ( m1_subset_1(k2_funct_1(C_238),k1_zfmisc_1(k2_zfmisc_1(B_239,A_240)))
      | k2_relset_1(A_240,B_239,C_238) != B_239
      | ~ v2_funct_1(C_238)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_240,B_239)))
      | ~ v1_funct_2(C_238,A_240,B_239)
      | ~ v1_funct_1(C_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_32,plain,(
    ! [C_14,A_12,B_13] :
      ( v1_relat_1(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1537,plain,(
    ! [C_241,A_242,B_243] :
      ( v1_relat_1(k2_funct_1(C_241))
      | k2_relset_1(A_242,B_243,C_241) != B_243
      | ~ v2_funct_1(C_241)
      | ~ m1_subset_1(C_241,k1_zfmisc_1(k2_zfmisc_1(A_242,B_243)))
      | ~ v1_funct_2(C_241,A_242,B_243)
      | ~ v1_funct_1(C_241) ) ),
    inference(resolution,[status(thm)],[c_1500,c_32])).

tff(c_1549,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_1537])).

tff(c_1558,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_78,c_82,c_1549])).

tff(c_940,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_931])).

tff(c_948,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_78,c_82,c_940])).

tff(c_1675,plain,(
    ! [A_257,C_258,B_259] :
      ( k6_partfun1(A_257) = k5_relat_1(C_258,k2_funct_1(C_258))
      | k1_xboole_0 = B_259
      | ~ v2_funct_1(C_258)
      | k2_relset_1(A_257,B_259,C_258) != B_259
      | ~ m1_subset_1(C_258,k1_zfmisc_1(k2_zfmisc_1(A_257,B_259)))
      | ~ v1_funct_2(C_258,A_257,B_259)
      | ~ v1_funct_1(C_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_1683,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_1675])).

tff(c_1693,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_82,c_78,c_1683])).

tff(c_1694,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1693])).

tff(c_12,plain,(
    ! [A_3,B_4] :
      ( v2_funct_1(k5_relat_1(A_3,B_4))
      | ~ v2_funct_1(B_4)
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4)
      | ~ v2_funct_1(A_3)
      | ~ v1_funct_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1710,plain,
    ( v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1694,c_12])).

tff(c_1728,plain,
    ( v2_funct_1(k6_partfun1('#skF_1'))
    | ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_94,c_78,c_1558,c_948,c_1710])).

tff(c_1729,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_1499,c_1728])).

tff(c_1737,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_1729])).

tff(c_1741,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_94,c_78,c_1737])).

tff(c_1743,plain,(
    v2_funct_1(k6_partfun1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1403])).

tff(c_2726,plain,(
    ! [B_312,E_308,C_310,D_311,A_309] :
      ( k1_xboole_0 = C_310
      | v2_funct_1(E_308)
      | k2_relset_1(A_309,B_312,D_311) != B_312
      | ~ v2_funct_1(k1_partfun1(A_309,B_312,B_312,C_310,D_311,E_308))
      | ~ m1_subset_1(E_308,k1_zfmisc_1(k2_zfmisc_1(B_312,C_310)))
      | ~ v1_funct_2(E_308,B_312,C_310)
      | ~ v1_funct_1(E_308)
      | ~ m1_subset_1(D_311,k1_zfmisc_1(k2_zfmisc_1(A_309,B_312)))
      | ~ v1_funct_2(D_311,A_309,B_312)
      | ~ v1_funct_1(D_311) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_2732,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_922,c_2726])).

tff(c_2740,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_90,c_88,c_86,c_84,c_1743,c_82,c_2732])).

tff(c_2742,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_949,c_76,c_2740])).

tff(c_2743,plain,
    ( k2_relat_1('#skF_4') != '#skF_1'
    | v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_945])).

tff(c_2745,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_2743])).

tff(c_166,plain,(
    ! [A_66,B_67,D_68] :
      ( r2_relset_1(A_66,B_67,D_68,D_68)
      | ~ m1_subset_1(D_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_173,plain,(
    ! [A_28] : r2_relset_1(A_28,A_28,k6_partfun1(A_28),k6_partfun1(A_28)) ),
    inference(resolution,[status(thm)],[c_46,c_166])).

tff(c_3789,plain,(
    ! [A_384,B_385,C_386,D_387] :
      ( k2_relset_1(A_384,B_385,C_386) = B_385
      | ~ r2_relset_1(B_385,B_385,k1_partfun1(B_385,A_384,A_384,B_385,D_387,C_386),k6_partfun1(B_385))
      | ~ m1_subset_1(D_387,k1_zfmisc_1(k2_zfmisc_1(B_385,A_384)))
      | ~ v1_funct_2(D_387,B_385,A_384)
      | ~ v1_funct_1(D_387)
      | ~ m1_subset_1(C_386,k1_zfmisc_1(k2_zfmisc_1(A_384,B_385)))
      | ~ v1_funct_2(C_386,A_384,B_385)
      | ~ v1_funct_1(C_386) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_3795,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_922,c_3789])).

tff(c_3799,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_84,c_94,c_92,c_90,c_173,c_200,c_3795])).

tff(c_3801,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2745,c_3799])).

tff(c_3803,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2743])).

tff(c_124,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_113])).

tff(c_3833,plain,(
    ! [A_393,B_394] :
      ( k2_funct_1(A_393) = B_394
      | k6_partfun1(k2_relat_1(A_393)) != k5_relat_1(B_394,A_393)
      | k2_relat_1(B_394) != k1_relat_1(A_393)
      | ~ v2_funct_1(A_393)
      | ~ v1_funct_1(B_394)
      | ~ v1_relat_1(B_394)
      | ~ v1_funct_1(A_393)
      | ~ v1_relat_1(A_393) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_28])).

tff(c_3841,plain,(
    ! [B_394] :
      ( k2_funct_1('#skF_3') = B_394
      | k5_relat_1(B_394,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_394) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_394)
      | ~ v1_relat_1(B_394)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_3833])).

tff(c_3898,plain,(
    ! [B_409] :
      ( k2_funct_1('#skF_3') = B_409
      | k5_relat_1(B_409,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_409) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_409)
      | ~ v1_relat_1(B_409) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_94,c_78,c_3841])).

tff(c_3910,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_124,c_3898])).

tff(c_3921,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_3803,c_3910])).

tff(c_3922,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_3921])).

tff(c_3938,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3922])).

tff(c_2744,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_945])).

tff(c_4065,plain,(
    ! [A_427,C_428,B_429] :
      ( k6_partfun1(A_427) = k5_relat_1(C_428,k2_funct_1(C_428))
      | k1_xboole_0 = B_429
      | ~ v2_funct_1(C_428)
      | k2_relset_1(A_427,B_429,C_428) != B_429
      | ~ m1_subset_1(C_428,k1_zfmisc_1(k2_zfmisc_1(A_427,B_429)))
      | ~ v1_funct_2(C_428,A_427,B_429)
      | ~ v1_funct_1(C_428) ) ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_4073,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_4065])).

tff(c_4083,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_82,c_78,c_4073])).

tff(c_4084,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4083])).

tff(c_4133,plain,
    ( k2_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4084,c_20])).

tff(c_4143,plain,(
    k2_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_94,c_78,c_4133])).

tff(c_3804,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3803,c_200])).

tff(c_4173,plain,(
    ! [B_430,C_431,A_432] :
      ( k6_partfun1(B_430) = k5_relat_1(k2_funct_1(C_431),C_431)
      | k1_xboole_0 = B_430
      | ~ v2_funct_1(C_431)
      | k2_relset_1(A_432,B_430,C_431) != B_430
      | ~ m1_subset_1(C_431,k1_zfmisc_1(k2_zfmisc_1(A_432,B_430)))
      | ~ v1_funct_2(C_431,A_432,B_430)
      | ~ v1_funct_1(C_431) ) ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_4179,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_4173])).

tff(c_4187,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_3804,c_2744,c_4179])).

tff(c_4188,plain,(
    k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_4187])).

tff(c_24,plain,(
    ! [A_7] :
      ( k2_relat_1(k5_relat_1(k2_funct_1(A_7),A_7)) = k2_relat_1(A_7)
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4204,plain,
    ( k2_relat_1(k6_partfun1('#skF_1')) = k2_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4188,c_24])).

tff(c_4218,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_88,c_2744,c_3803,c_4143,c_4204])).

tff(c_4220,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3938,c_4218])).

tff(c_4221,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3922])).

tff(c_3924,plain,(
    ! [E_414,F_413,D_410,B_411,C_415,A_412] :
      ( k1_partfun1(A_412,B_411,C_415,D_410,E_414,F_413) = k5_relat_1(E_414,F_413)
      | ~ m1_subset_1(F_413,k1_zfmisc_1(k2_zfmisc_1(C_415,D_410)))
      | ~ v1_funct_1(F_413)
      | ~ m1_subset_1(E_414,k1_zfmisc_1(k2_zfmisc_1(A_412,B_411)))
      | ~ v1_funct_1(E_414) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_3928,plain,(
    ! [A_412,B_411,E_414] :
      ( k1_partfun1(A_412,B_411,'#skF_2','#skF_1',E_414,'#skF_4') = k5_relat_1(E_414,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_414,k1_zfmisc_1(k2_zfmisc_1(A_412,B_411)))
      | ~ v1_funct_1(E_414) ) ),
    inference(resolution,[status(thm)],[c_84,c_3924])).

tff(c_4228,plain,(
    ! [A_433,B_434,E_435] :
      ( k1_partfun1(A_433,B_434,'#skF_2','#skF_1',E_435,'#skF_4') = k5_relat_1(E_435,'#skF_4')
      | ~ m1_subset_1(E_435,k1_zfmisc_1(k2_zfmisc_1(A_433,B_434)))
      | ~ v1_funct_1(E_435) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_3928])).

tff(c_4237,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_4228])).

tff(c_4244,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_922,c_4237])).

tff(c_4351,plain,(
    ! [A_443,C_444,B_445] :
      ( k6_partfun1(A_443) = k5_relat_1(C_444,k2_funct_1(C_444))
      | k1_xboole_0 = B_445
      | ~ v2_funct_1(C_444)
      | k2_relset_1(A_443,B_445,C_444) != B_445
      | ~ m1_subset_1(C_444,k1_zfmisc_1(k2_zfmisc_1(A_443,B_445)))
      | ~ v1_funct_2(C_444,A_443,B_445)
      | ~ v1_funct_1(C_444) ) ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_4357,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_84,c_4351])).

tff(c_4365,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_86,c_3804,c_2744,c_4357])).

tff(c_4366,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_4365])).

tff(c_4383,plain,
    ( k2_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4366,c_20])).

tff(c_4393,plain,(
    k2_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_88,c_2744,c_4383])).

tff(c_4453,plain,(
    ! [B_446,C_447,A_448] :
      ( k6_partfun1(B_446) = k5_relat_1(k2_funct_1(C_447),C_447)
      | k1_xboole_0 = B_446
      | ~ v2_funct_1(C_447)
      | k2_relset_1(A_448,B_446,C_447) != B_446
      | ~ m1_subset_1(C_447,k1_zfmisc_1(k2_zfmisc_1(A_448,B_446)))
      | ~ v1_funct_2(C_447,A_448,B_446)
      | ~ v1_funct_1(C_447) ) ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_4461,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_90,c_4453])).

tff(c_4471,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_92,c_82,c_78,c_4461])).

tff(c_4472,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_4471])).

tff(c_4513,plain,
    ( k2_relat_1(k6_partfun1('#skF_2')) = k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4472,c_24])).

tff(c_4527,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_94,c_78,c_202,c_4393,c_4513])).

tff(c_3835,plain,(
    ! [B_394] :
      ( k2_funct_1('#skF_4') = B_394
      | k5_relat_1(B_394,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_394) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_394)
      | ~ v1_relat_1(B_394)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3803,c_3833])).

tff(c_3845,plain,(
    ! [B_394] :
      ( k2_funct_1('#skF_4') = B_394
      | k5_relat_1(B_394,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_394) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_394)
      | ~ v1_relat_1(B_394) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_88,c_2744,c_3835])).

tff(c_6545,plain,(
    ! [B_520] :
      ( k2_funct_1('#skF_4') = B_520
      | k5_relat_1(B_520,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_520) != '#skF_2'
      | ~ v1_funct_1(B_520)
      | ~ v1_relat_1(B_520) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4527,c_3845])).

tff(c_6647,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_125,c_6545])).

tff(c_6748,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_202,c_4244,c_6647])).

tff(c_6759,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6748,c_4366])).

tff(c_6768,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4221,c_6759])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:02:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.03/2.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.03/2.79  
% 8.03/2.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.03/2.79  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.03/2.79  
% 8.03/2.79  %Foreground sorts:
% 8.03/2.79  
% 8.03/2.79  
% 8.03/2.79  %Background operators:
% 8.03/2.79  
% 8.03/2.79  
% 8.03/2.79  %Foreground operators:
% 8.03/2.79  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.03/2.79  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.03/2.79  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.03/2.79  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.03/2.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.03/2.79  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 8.03/2.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.03/2.79  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.03/2.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.03/2.79  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.03/2.79  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.03/2.79  tff('#skF_2', type, '#skF_2': $i).
% 8.03/2.79  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.03/2.79  tff('#skF_3', type, '#skF_3': $i).
% 8.03/2.79  tff('#skF_1', type, '#skF_1': $i).
% 8.03/2.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.03/2.79  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 8.03/2.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.03/2.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.03/2.79  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.03/2.79  tff('#skF_4', type, '#skF_4': $i).
% 8.03/2.79  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.03/2.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.03/2.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.03/2.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.03/2.79  
% 8.03/2.82  tff(f_261, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 8.03/2.82  tff(f_124, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.03/2.82  tff(f_219, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 8.03/2.82  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.03/2.82  tff(f_45, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_funct_1)).
% 8.03/2.82  tff(f_148, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 8.03/2.82  tff(f_158, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 8.03/2.82  tff(f_132, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 8.03/2.82  tff(f_144, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 8.03/2.82  tff(f_160, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 8.03/2.82  tff(f_108, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_1)).
% 8.03/2.82  tff(f_235, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 8.03/2.82  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_funct_1)).
% 8.03/2.82  tff(f_61, axiom, (![A, B]: ((((((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) & v1_relat_1(B)) & v1_funct_1(B)) & v2_funct_1(B)) => (v1_relat_1(k5_relat_1(A, B)) & v2_funct_1(k5_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_funct_1)).
% 8.03/2.82  tff(f_203, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 8.03/2.82  tff(f_177, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 8.03/2.82  tff(f_91, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_funct_1)).
% 8.03/2.82  tff(c_72, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_261])).
% 8.03/2.82  tff(c_88, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_261])).
% 8.03/2.82  tff(c_86, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_261])).
% 8.03/2.82  tff(c_84, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_261])).
% 8.03/2.82  tff(c_189, plain, (![A_71, B_72, C_73]: (k2_relset_1(A_71, B_72, C_73)=k2_relat_1(C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_71, B_72))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 8.03/2.82  tff(c_200, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_189])).
% 8.03/2.82  tff(c_931, plain, (![C_158, A_159, B_160]: (v1_funct_1(k2_funct_1(C_158)) | k2_relset_1(A_159, B_160, C_158)!=B_160 | ~v2_funct_1(C_158) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_159, B_160))) | ~v1_funct_2(C_158, A_159, B_160) | ~v1_funct_1(C_158))), inference(cnfTransformation, [status(thm)], [f_219])).
% 8.03/2.82  tff(c_937, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_931])).
% 8.03/2.82  tff(c_945, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relat_1('#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_200, c_937])).
% 8.03/2.82  tff(c_949, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_945])).
% 8.03/2.82  tff(c_76, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_261])).
% 8.03/2.82  tff(c_94, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_261])).
% 8.03/2.82  tff(c_92, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_261])).
% 8.03/2.82  tff(c_90, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_261])).
% 8.03/2.82  tff(c_113, plain, (![C_59, A_60, B_61]: (v1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.03/2.82  tff(c_125, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_90, c_113])).
% 8.03/2.82  tff(c_78, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_261])).
% 8.03/2.82  tff(c_6, plain, (![A_2]: (v2_funct_1(k2_funct_1(A_2)) | ~v2_funct_1(A_2) | ~v1_funct_1(A_2) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.03/2.82  tff(c_46, plain, (![A_28]: (m1_subset_1(k6_partfun1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 8.03/2.82  tff(c_123, plain, (![A_28]: (v1_relat_1(k6_partfun1(A_28)))), inference(resolution, [status(thm)], [c_46, c_113])).
% 8.03/2.82  tff(c_625, plain, (![D_137, A_139, B_138, E_141, F_140, C_142]: (k1_partfun1(A_139, B_138, C_142, D_137, E_141, F_140)=k5_relat_1(E_141, F_140) | ~m1_subset_1(F_140, k1_zfmisc_1(k2_zfmisc_1(C_142, D_137))) | ~v1_funct_1(F_140) | ~m1_subset_1(E_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_138))) | ~v1_funct_1(E_141))), inference(cnfTransformation, [status(thm)], [f_158])).
% 8.03/2.82  tff(c_631, plain, (![A_139, B_138, E_141]: (k1_partfun1(A_139, B_138, '#skF_2', '#skF_1', E_141, '#skF_4')=k5_relat_1(E_141, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_138))) | ~v1_funct_1(E_141))), inference(resolution, [status(thm)], [c_84, c_625])).
% 8.03/2.82  tff(c_642, plain, (![A_143, B_144, E_145]: (k1_partfun1(A_143, B_144, '#skF_2', '#skF_1', E_145, '#skF_4')=k5_relat_1(E_145, '#skF_4') | ~m1_subset_1(E_145, k1_zfmisc_1(k2_zfmisc_1(A_143, B_144))) | ~v1_funct_1(E_145))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_631])).
% 8.03/2.82  tff(c_654, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_90, c_642])).
% 8.03/2.82  tff(c_662, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_654])).
% 8.03/2.82  tff(c_80, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_261])).
% 8.03/2.82  tff(c_270, plain, (![D_83, C_84, A_85, B_86]: (D_83=C_84 | ~r2_relset_1(A_85, B_86, C_84, D_83) | ~m1_subset_1(D_83, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.03/2.82  tff(c_278, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_80, c_270])).
% 8.03/2.82  tff(c_293, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_278])).
% 8.03/2.82  tff(c_294, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_293])).
% 8.03/2.82  tff(c_815, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_662, c_294])).
% 8.03/2.82  tff(c_856, plain, (![A_152, D_156, F_155, B_157, C_153, E_154]: (m1_subset_1(k1_partfun1(A_152, B_157, C_153, D_156, E_154, F_155), k1_zfmisc_1(k2_zfmisc_1(A_152, D_156))) | ~m1_subset_1(F_155, k1_zfmisc_1(k2_zfmisc_1(C_153, D_156))) | ~v1_funct_1(F_155) | ~m1_subset_1(E_154, k1_zfmisc_1(k2_zfmisc_1(A_152, B_157))) | ~v1_funct_1(E_154))), inference(cnfTransformation, [status(thm)], [f_144])).
% 8.03/2.82  tff(c_898, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_662, c_856])).
% 8.03/2.82  tff(c_918, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_90, c_88, c_84, c_898])).
% 8.03/2.82  tff(c_921, plain, $false, inference(negUnitSimplification, [status(thm)], [c_815, c_918])).
% 8.03/2.82  tff(c_922, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_293])).
% 8.03/2.82  tff(c_1030, plain, (![D_173, C_170, B_174, A_169, F_172, E_171]: (v1_funct_1(k1_partfun1(A_169, B_174, C_170, D_173, E_171, F_172)) | ~m1_subset_1(F_172, k1_zfmisc_1(k2_zfmisc_1(C_170, D_173))) | ~v1_funct_1(F_172) | ~m1_subset_1(E_171, k1_zfmisc_1(k2_zfmisc_1(A_169, B_174))) | ~v1_funct_1(E_171))), inference(cnfTransformation, [status(thm)], [f_144])).
% 8.03/2.82  tff(c_1034, plain, (![A_169, B_174, E_171]: (v1_funct_1(k1_partfun1(A_169, B_174, '#skF_2', '#skF_1', E_171, '#skF_4')) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_171, k1_zfmisc_1(k2_zfmisc_1(A_169, B_174))) | ~v1_funct_1(E_171))), inference(resolution, [status(thm)], [c_84, c_1030])).
% 8.03/2.82  tff(c_1044, plain, (![A_175, B_176, E_177]: (v1_funct_1(k1_partfun1(A_175, B_176, '#skF_2', '#skF_1', E_177, '#skF_4')) | ~m1_subset_1(E_177, k1_zfmisc_1(k2_zfmisc_1(A_175, B_176))) | ~v1_funct_1(E_177))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1034])).
% 8.03/2.82  tff(c_1053, plain, (v1_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_90, c_1044])).
% 8.03/2.82  tff(c_1060, plain, (v1_funct_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_922, c_1053])).
% 8.03/2.82  tff(c_82, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_261])).
% 8.03/2.82  tff(c_198, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_90, c_189])).
% 8.03/2.82  tff(c_202, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_198])).
% 8.03/2.82  tff(c_50, plain, (![A_35]: (k6_relat_1(A_35)=k6_partfun1(A_35))), inference(cnfTransformation, [status(thm)], [f_160])).
% 8.03/2.82  tff(c_28, plain, (![A_8, B_10]: (k2_funct_1(A_8)=B_10 | k6_relat_1(k2_relat_1(A_8))!=k5_relat_1(B_10, A_8) | k2_relat_1(B_10)!=k1_relat_1(A_8) | ~v2_funct_1(A_8) | ~v1_funct_1(B_10) | ~v1_relat_1(B_10) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_108])).
% 8.03/2.82  tff(c_951, plain, (![A_162, B_163]: (k2_funct_1(A_162)=B_163 | k6_partfun1(k2_relat_1(A_162))!=k5_relat_1(B_163, A_162) | k2_relat_1(B_163)!=k1_relat_1(A_162) | ~v2_funct_1(A_162) | ~v1_funct_1(B_163) | ~v1_relat_1(B_163) | ~v1_funct_1(A_162) | ~v1_relat_1(A_162))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_28])).
% 8.03/2.82  tff(c_957, plain, (![B_163]: (k2_funct_1('#skF_3')=B_163 | k5_relat_1(B_163, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_163)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_163) | ~v1_relat_1(B_163) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_202, c_951])).
% 8.03/2.82  tff(c_962, plain, (![B_164]: (k2_funct_1('#skF_3')=B_164 | k5_relat_1(B_164, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_164)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_164) | ~v1_relat_1(B_164))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_94, c_78, c_957])).
% 8.03/2.82  tff(c_979, plain, (![A_28]: (k6_partfun1(A_28)=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1(A_28), '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(k6_partfun1(A_28))!=k1_relat_1('#skF_3') | ~v1_funct_1(k6_partfun1(A_28)))), inference(resolution, [status(thm)], [c_123, c_962])).
% 8.03/2.82  tff(c_1064, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3') | k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(k6_partfun1('#skF_1'))!=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1060, c_979])).
% 8.03/2.82  tff(c_1084, plain, (k2_relat_1(k6_partfun1('#skF_1'))!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_1064])).
% 8.03/2.82  tff(c_74, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_261])).
% 8.03/2.82  tff(c_1340, plain, (![A_218, C_219, B_220]: (k6_partfun1(A_218)=k5_relat_1(C_219, k2_funct_1(C_219)) | k1_xboole_0=B_220 | ~v2_funct_1(C_219) | k2_relset_1(A_218, B_220, C_219)!=B_220 | ~m1_subset_1(C_219, k1_zfmisc_1(k2_zfmisc_1(A_218, B_220))) | ~v1_funct_2(C_219, A_218, B_220) | ~v1_funct_1(C_219))), inference(cnfTransformation, [status(thm)], [f_235])).
% 8.03/2.82  tff(c_1348, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_90, c_1340])).
% 8.03/2.82  tff(c_1358, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_82, c_78, c_1348])).
% 8.03/2.82  tff(c_1359, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_74, c_1358])).
% 8.03/2.82  tff(c_20, plain, (![A_6]: (k2_relat_1(k5_relat_1(A_6, k2_funct_1(A_6)))=k1_relat_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.03/2.82  tff(c_1378, plain, (k2_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1359, c_20])).
% 8.03/2.82  tff(c_1392, plain, (k2_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_125, c_94, c_78, c_1378])).
% 8.03/2.82  tff(c_1394, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1084, c_1392])).
% 8.03/2.82  tff(c_1396, plain, (k2_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_1064])).
% 8.03/2.82  tff(c_95, plain, (![A_8, B_10]: (k2_funct_1(A_8)=B_10 | k6_partfun1(k2_relat_1(A_8))!=k5_relat_1(B_10, A_8) | k2_relat_1(B_10)!=k1_relat_1(A_8) | ~v2_funct_1(A_8) | ~v1_funct_1(B_10) | ~v1_relat_1(B_10) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_28])).
% 8.03/2.82  tff(c_1399, plain, (![B_10]: (k2_funct_1(k6_partfun1('#skF_1'))=B_10 | k5_relat_1(B_10, k6_partfun1('#skF_1'))!=k6_partfun1(k1_relat_1('#skF_3')) | k2_relat_1(B_10)!=k1_relat_1(k6_partfun1('#skF_1')) | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1(B_10) | ~v1_relat_1(B_10) | ~v1_funct_1(k6_partfun1('#skF_1')) | ~v1_relat_1(k6_partfun1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1396, c_95])).
% 8.03/2.82  tff(c_1403, plain, (![B_10]: (k2_funct_1(k6_partfun1('#skF_1'))=B_10 | k5_relat_1(B_10, k6_partfun1('#skF_1'))!=k6_partfun1(k1_relat_1('#skF_3')) | k2_relat_1(B_10)!=k1_relat_1(k6_partfun1('#skF_1')) | ~v2_funct_1(k6_partfun1('#skF_1')) | ~v1_funct_1(B_10) | ~v1_relat_1(B_10))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_1060, c_1399])).
% 8.03/2.82  tff(c_1499, plain, (~v2_funct_1(k6_partfun1('#skF_1'))), inference(splitLeft, [status(thm)], [c_1403])).
% 8.03/2.82  tff(c_1500, plain, (![C_238, B_239, A_240]: (m1_subset_1(k2_funct_1(C_238), k1_zfmisc_1(k2_zfmisc_1(B_239, A_240))) | k2_relset_1(A_240, B_239, C_238)!=B_239 | ~v2_funct_1(C_238) | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_240, B_239))) | ~v1_funct_2(C_238, A_240, B_239) | ~v1_funct_1(C_238))), inference(cnfTransformation, [status(thm)], [f_219])).
% 8.03/2.82  tff(c_32, plain, (![C_14, A_12, B_13]: (v1_relat_1(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.03/2.82  tff(c_1537, plain, (![C_241, A_242, B_243]: (v1_relat_1(k2_funct_1(C_241)) | k2_relset_1(A_242, B_243, C_241)!=B_243 | ~v2_funct_1(C_241) | ~m1_subset_1(C_241, k1_zfmisc_1(k2_zfmisc_1(A_242, B_243))) | ~v1_funct_2(C_241, A_242, B_243) | ~v1_funct_1(C_241))), inference(resolution, [status(thm)], [c_1500, c_32])).
% 8.03/2.82  tff(c_1549, plain, (v1_relat_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_90, c_1537])).
% 8.03/2.82  tff(c_1558, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_78, c_82, c_1549])).
% 8.03/2.82  tff(c_940, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_90, c_931])).
% 8.03/2.82  tff(c_948, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_78, c_82, c_940])).
% 8.03/2.82  tff(c_1675, plain, (![A_257, C_258, B_259]: (k6_partfun1(A_257)=k5_relat_1(C_258, k2_funct_1(C_258)) | k1_xboole_0=B_259 | ~v2_funct_1(C_258) | k2_relset_1(A_257, B_259, C_258)!=B_259 | ~m1_subset_1(C_258, k1_zfmisc_1(k2_zfmisc_1(A_257, B_259))) | ~v1_funct_2(C_258, A_257, B_259) | ~v1_funct_1(C_258))), inference(cnfTransformation, [status(thm)], [f_235])).
% 8.03/2.82  tff(c_1683, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_90, c_1675])).
% 8.03/2.82  tff(c_1693, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_82, c_78, c_1683])).
% 8.03/2.82  tff(c_1694, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_74, c_1693])).
% 8.03/2.82  tff(c_12, plain, (![A_3, B_4]: (v2_funct_1(k5_relat_1(A_3, B_4)) | ~v2_funct_1(B_4) | ~v1_funct_1(B_4) | ~v1_relat_1(B_4) | ~v2_funct_1(A_3) | ~v1_funct_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.03/2.82  tff(c_1710, plain, (v2_funct_1(k6_partfun1('#skF_1')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1694, c_12])).
% 8.03/2.82  tff(c_1728, plain, (v2_funct_1(k6_partfun1('#skF_1')) | ~v2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_94, c_78, c_1558, c_948, c_1710])).
% 8.03/2.82  tff(c_1729, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_1499, c_1728])).
% 8.03/2.82  tff(c_1737, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_1729])).
% 8.03/2.82  tff(c_1741, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_94, c_78, c_1737])).
% 8.03/2.82  tff(c_1743, plain, (v2_funct_1(k6_partfun1('#skF_1'))), inference(splitRight, [status(thm)], [c_1403])).
% 8.03/2.82  tff(c_2726, plain, (![B_312, E_308, C_310, D_311, A_309]: (k1_xboole_0=C_310 | v2_funct_1(E_308) | k2_relset_1(A_309, B_312, D_311)!=B_312 | ~v2_funct_1(k1_partfun1(A_309, B_312, B_312, C_310, D_311, E_308)) | ~m1_subset_1(E_308, k1_zfmisc_1(k2_zfmisc_1(B_312, C_310))) | ~v1_funct_2(E_308, B_312, C_310) | ~v1_funct_1(E_308) | ~m1_subset_1(D_311, k1_zfmisc_1(k2_zfmisc_1(A_309, B_312))) | ~v1_funct_2(D_311, A_309, B_312) | ~v1_funct_1(D_311))), inference(cnfTransformation, [status(thm)], [f_203])).
% 8.03/2.82  tff(c_2732, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_922, c_2726])).
% 8.03/2.82  tff(c_2740, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_90, c_88, c_86, c_84, c_1743, c_82, c_2732])).
% 8.03/2.82  tff(c_2742, plain, $false, inference(negUnitSimplification, [status(thm)], [c_949, c_76, c_2740])).
% 8.03/2.82  tff(c_2743, plain, (k2_relat_1('#skF_4')!='#skF_1' | v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_945])).
% 8.03/2.82  tff(c_2745, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_2743])).
% 8.03/2.82  tff(c_166, plain, (![A_66, B_67, D_68]: (r2_relset_1(A_66, B_67, D_68, D_68) | ~m1_subset_1(D_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.03/2.82  tff(c_173, plain, (![A_28]: (r2_relset_1(A_28, A_28, k6_partfun1(A_28), k6_partfun1(A_28)))), inference(resolution, [status(thm)], [c_46, c_166])).
% 8.03/2.82  tff(c_3789, plain, (![A_384, B_385, C_386, D_387]: (k2_relset_1(A_384, B_385, C_386)=B_385 | ~r2_relset_1(B_385, B_385, k1_partfun1(B_385, A_384, A_384, B_385, D_387, C_386), k6_partfun1(B_385)) | ~m1_subset_1(D_387, k1_zfmisc_1(k2_zfmisc_1(B_385, A_384))) | ~v1_funct_2(D_387, B_385, A_384) | ~v1_funct_1(D_387) | ~m1_subset_1(C_386, k1_zfmisc_1(k2_zfmisc_1(A_384, B_385))) | ~v1_funct_2(C_386, A_384, B_385) | ~v1_funct_1(C_386))), inference(cnfTransformation, [status(thm)], [f_177])).
% 8.03/2.82  tff(c_3795, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_922, c_3789])).
% 8.03/2.82  tff(c_3799, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_84, c_94, c_92, c_90, c_173, c_200, c_3795])).
% 8.03/2.82  tff(c_3801, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2745, c_3799])).
% 8.03/2.82  tff(c_3803, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_2743])).
% 8.03/2.82  tff(c_124, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_113])).
% 8.03/2.82  tff(c_3833, plain, (![A_393, B_394]: (k2_funct_1(A_393)=B_394 | k6_partfun1(k2_relat_1(A_393))!=k5_relat_1(B_394, A_393) | k2_relat_1(B_394)!=k1_relat_1(A_393) | ~v2_funct_1(A_393) | ~v1_funct_1(B_394) | ~v1_relat_1(B_394) | ~v1_funct_1(A_393) | ~v1_relat_1(A_393))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_28])).
% 8.03/2.82  tff(c_3841, plain, (![B_394]: (k2_funct_1('#skF_3')=B_394 | k5_relat_1(B_394, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_394)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_394) | ~v1_relat_1(B_394) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_202, c_3833])).
% 8.03/2.82  tff(c_3898, plain, (![B_409]: (k2_funct_1('#skF_3')=B_409 | k5_relat_1(B_409, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_409)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_409) | ~v1_relat_1(B_409))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_94, c_78, c_3841])).
% 8.03/2.82  tff(c_3910, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_124, c_3898])).
% 8.03/2.82  tff(c_3921, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_3803, c_3910])).
% 8.03/2.82  tff(c_3922, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k1_relat_1('#skF_3')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_72, c_3921])).
% 8.03/2.82  tff(c_3938, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_3922])).
% 8.03/2.82  tff(c_2744, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_945])).
% 8.03/2.82  tff(c_4065, plain, (![A_427, C_428, B_429]: (k6_partfun1(A_427)=k5_relat_1(C_428, k2_funct_1(C_428)) | k1_xboole_0=B_429 | ~v2_funct_1(C_428) | k2_relset_1(A_427, B_429, C_428)!=B_429 | ~m1_subset_1(C_428, k1_zfmisc_1(k2_zfmisc_1(A_427, B_429))) | ~v1_funct_2(C_428, A_427, B_429) | ~v1_funct_1(C_428))), inference(cnfTransformation, [status(thm)], [f_235])).
% 8.03/2.82  tff(c_4073, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_90, c_4065])).
% 8.03/2.82  tff(c_4083, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_82, c_78, c_4073])).
% 8.03/2.82  tff(c_4084, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_74, c_4083])).
% 8.03/2.82  tff(c_4133, plain, (k2_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4084, c_20])).
% 8.03/2.82  tff(c_4143, plain, (k2_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_125, c_94, c_78, c_4133])).
% 8.03/2.82  tff(c_3804, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3803, c_200])).
% 8.03/2.82  tff(c_4173, plain, (![B_430, C_431, A_432]: (k6_partfun1(B_430)=k5_relat_1(k2_funct_1(C_431), C_431) | k1_xboole_0=B_430 | ~v2_funct_1(C_431) | k2_relset_1(A_432, B_430, C_431)!=B_430 | ~m1_subset_1(C_431, k1_zfmisc_1(k2_zfmisc_1(A_432, B_430))) | ~v1_funct_2(C_431, A_432, B_430) | ~v1_funct_1(C_431))), inference(cnfTransformation, [status(thm)], [f_235])).
% 8.03/2.82  tff(c_4179, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_4173])).
% 8.03/2.82  tff(c_4187, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_3804, c_2744, c_4179])).
% 8.03/2.82  tff(c_4188, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_76, c_4187])).
% 8.03/2.82  tff(c_24, plain, (![A_7]: (k2_relat_1(k5_relat_1(k2_funct_1(A_7), A_7))=k2_relat_1(A_7) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.03/2.82  tff(c_4204, plain, (k2_relat_1(k6_partfun1('#skF_1'))=k2_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4188, c_24])).
% 8.03/2.82  tff(c_4218, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_88, c_2744, c_3803, c_4143, c_4204])).
% 8.03/2.82  tff(c_4220, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3938, c_4218])).
% 8.03/2.82  tff(c_4221, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_3922])).
% 8.03/2.82  tff(c_3924, plain, (![E_414, F_413, D_410, B_411, C_415, A_412]: (k1_partfun1(A_412, B_411, C_415, D_410, E_414, F_413)=k5_relat_1(E_414, F_413) | ~m1_subset_1(F_413, k1_zfmisc_1(k2_zfmisc_1(C_415, D_410))) | ~v1_funct_1(F_413) | ~m1_subset_1(E_414, k1_zfmisc_1(k2_zfmisc_1(A_412, B_411))) | ~v1_funct_1(E_414))), inference(cnfTransformation, [status(thm)], [f_158])).
% 8.03/2.82  tff(c_3928, plain, (![A_412, B_411, E_414]: (k1_partfun1(A_412, B_411, '#skF_2', '#skF_1', E_414, '#skF_4')=k5_relat_1(E_414, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_414, k1_zfmisc_1(k2_zfmisc_1(A_412, B_411))) | ~v1_funct_1(E_414))), inference(resolution, [status(thm)], [c_84, c_3924])).
% 8.03/2.82  tff(c_4228, plain, (![A_433, B_434, E_435]: (k1_partfun1(A_433, B_434, '#skF_2', '#skF_1', E_435, '#skF_4')=k5_relat_1(E_435, '#skF_4') | ~m1_subset_1(E_435, k1_zfmisc_1(k2_zfmisc_1(A_433, B_434))) | ~v1_funct_1(E_435))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_3928])).
% 8.03/2.82  tff(c_4237, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_90, c_4228])).
% 8.03/2.82  tff(c_4244, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_922, c_4237])).
% 8.03/2.82  tff(c_4351, plain, (![A_443, C_444, B_445]: (k6_partfun1(A_443)=k5_relat_1(C_444, k2_funct_1(C_444)) | k1_xboole_0=B_445 | ~v2_funct_1(C_444) | k2_relset_1(A_443, B_445, C_444)!=B_445 | ~m1_subset_1(C_444, k1_zfmisc_1(k2_zfmisc_1(A_443, B_445))) | ~v1_funct_2(C_444, A_443, B_445) | ~v1_funct_1(C_444))), inference(cnfTransformation, [status(thm)], [f_235])).
% 8.03/2.82  tff(c_4357, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_84, c_4351])).
% 8.03/2.82  tff(c_4365, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_86, c_3804, c_2744, c_4357])).
% 8.03/2.82  tff(c_4366, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_76, c_4365])).
% 8.03/2.82  tff(c_4383, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4366, c_20])).
% 8.03/2.82  tff(c_4393, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_124, c_88, c_2744, c_4383])).
% 8.03/2.82  tff(c_4453, plain, (![B_446, C_447, A_448]: (k6_partfun1(B_446)=k5_relat_1(k2_funct_1(C_447), C_447) | k1_xboole_0=B_446 | ~v2_funct_1(C_447) | k2_relset_1(A_448, B_446, C_447)!=B_446 | ~m1_subset_1(C_447, k1_zfmisc_1(k2_zfmisc_1(A_448, B_446))) | ~v1_funct_2(C_447, A_448, B_446) | ~v1_funct_1(C_447))), inference(cnfTransformation, [status(thm)], [f_235])).
% 8.03/2.82  tff(c_4461, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_90, c_4453])).
% 8.03/2.82  tff(c_4471, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_92, c_82, c_78, c_4461])).
% 8.03/2.82  tff(c_4472, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_74, c_4471])).
% 8.03/2.82  tff(c_4513, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4472, c_24])).
% 8.03/2.82  tff(c_4527, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_125, c_94, c_78, c_202, c_4393, c_4513])).
% 8.03/2.82  tff(c_3835, plain, (![B_394]: (k2_funct_1('#skF_4')=B_394 | k5_relat_1(B_394, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_394)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_394) | ~v1_relat_1(B_394) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3803, c_3833])).
% 8.03/2.82  tff(c_3845, plain, (![B_394]: (k2_funct_1('#skF_4')=B_394 | k5_relat_1(B_394, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_394)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_394) | ~v1_relat_1(B_394))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_88, c_2744, c_3835])).
% 8.03/2.82  tff(c_6545, plain, (![B_520]: (k2_funct_1('#skF_4')=B_520 | k5_relat_1(B_520, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_520)!='#skF_2' | ~v1_funct_1(B_520) | ~v1_relat_1(B_520))), inference(demodulation, [status(thm), theory('equality')], [c_4527, c_3845])).
% 8.03/2.82  tff(c_6647, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_125, c_6545])).
% 8.03/2.82  tff(c_6748, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_202, c_4244, c_6647])).
% 8.03/2.82  tff(c_6759, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6748, c_4366])).
% 8.03/2.82  tff(c_6768, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4221, c_6759])).
% 8.03/2.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.03/2.82  
% 8.03/2.82  Inference rules
% 8.03/2.82  ----------------------
% 8.03/2.82  #Ref     : 0
% 8.03/2.82  #Sup     : 1442
% 8.03/2.82  #Fact    : 0
% 8.03/2.82  #Define  : 0
% 8.03/2.82  #Split   : 46
% 8.03/2.82  #Chain   : 0
% 8.03/2.82  #Close   : 0
% 8.03/2.82  
% 8.03/2.82  Ordering : KBO
% 8.03/2.82  
% 8.03/2.82  Simplification rules
% 8.03/2.82  ----------------------
% 8.03/2.82  #Subsume      : 99
% 8.03/2.82  #Demod        : 1892
% 8.03/2.82  #Tautology    : 405
% 8.03/2.82  #SimpNegUnit  : 106
% 8.03/2.82  #BackRed      : 42
% 8.03/2.82  
% 8.03/2.82  #Partial instantiations: 0
% 8.03/2.82  #Strategies tried      : 1
% 8.03/2.82  
% 8.03/2.82  Timing (in seconds)
% 8.03/2.82  ----------------------
% 8.03/2.82  Preprocessing        : 0.39
% 8.03/2.82  Parsing              : 0.21
% 8.03/2.82  CNF conversion       : 0.03
% 8.03/2.82  Main loop            : 1.63
% 8.03/2.82  Inferencing          : 0.54
% 8.03/2.82  Reduction            : 0.63
% 8.03/2.82  Demodulation         : 0.47
% 8.03/2.82  BG Simplification    : 0.06
% 8.03/2.82  Subsumption          : 0.29
% 8.03/2.82  Abstraction          : 0.07
% 8.03/2.82  MUC search           : 0.00
% 8.03/2.82  Cooper               : 0.00
% 8.03/2.82  Total                : 2.08
% 8.03/2.82  Index Insertion      : 0.00
% 8.03/2.82  Index Deletion       : 0.00
% 8.03/2.82  Index Matching       : 0.00
% 8.03/2.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
