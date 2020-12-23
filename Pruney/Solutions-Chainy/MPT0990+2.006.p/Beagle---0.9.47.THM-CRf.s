%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:56 EST 2020

% Result     : Theorem 18.17s
% Output     : CNFRefutation 18.38s
% Verified   : 
% Statistics : Number of formulae       :  186 (3331 expanded)
%              Number of leaves         :   49 (1152 expanded)
%              Depth                    :   23
%              Number of atoms          :  407 (8470 expanded)
%              Number of equality atoms :  101 (2664 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_181,negated_conjecture,(
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

tff(f_111,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_155,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_87,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A)
        & v1_relat_1(C) )
     => ( v1_relat_1(k5_relat_1(B,C))
        & v4_relat_1(k5_relat_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc26_relat_1)).

tff(f_117,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_107,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_143,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_131,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_129,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_153,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_97,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(c_66,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_84,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_143,plain,(
    ! [C_64,A_65,B_66] :
      ( v1_relat_1(C_64)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_155,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_143])).

tff(c_78,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_156,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_78,c_143])).

tff(c_64,plain,(
    ! [A_51] : k6_relat_1(A_51) = k6_partfun1(A_51) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_22,plain,(
    ! [A_16,B_17] :
      ( k5_relat_1(k6_relat_1(A_16),B_17) = k7_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_94,plain,(
    ! [A_16,B_17] :
      ( k5_relat_1(k6_partfun1(A_16),B_17) = k7_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_22])).

tff(c_32,plain,(
    ! [A_22] : v1_relat_1(k6_relat_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_93,plain,(
    ! [A_22] : v1_relat_1(k6_partfun1(A_22)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_32])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_244,plain,(
    ! [B_80,A_81] :
      ( v4_relat_1(B_80,A_81)
      | ~ r1_tarski(k1_relat_1(B_80),A_81)
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_254,plain,(
    ! [B_80] :
      ( v4_relat_1(B_80,k1_relat_1(B_80))
      | ~ v1_relat_1(B_80) ) ),
    inference(resolution,[status(thm)],[c_6,c_244])).

tff(c_384,plain,(
    ! [B_94,C_95,A_96] :
      ( v1_relat_1(k5_relat_1(B_94,C_95))
      | ~ v1_relat_1(C_95)
      | ~ v4_relat_1(B_94,A_96)
      | ~ v1_relat_1(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_437,plain,(
    ! [B_101,C_102] :
      ( v1_relat_1(k5_relat_1(B_101,C_102))
      | ~ v1_relat_1(C_102)
      | ~ v1_relat_1(B_101) ) ),
    inference(resolution,[status(thm)],[c_254,c_384])).

tff(c_440,plain,(
    ! [B_17,A_16] :
      ( v1_relat_1(k7_relat_1(B_17,A_16))
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1(k6_partfun1(A_16))
      | ~ v1_relat_1(B_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_437])).

tff(c_448,plain,(
    ! [B_17,A_16] :
      ( v1_relat_1(k7_relat_1(B_17,A_16))
      | ~ v1_relat_1(B_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_440])).

tff(c_194,plain,(
    ! [C_73,A_74,B_75] :
      ( v4_relat_1(C_73,A_74)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1(A_74,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_206,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_78,c_194])).

tff(c_208,plain,(
    ! [B_77,A_78] :
      ( k7_relat_1(B_77,A_78) = B_77
      | ~ v4_relat_1(B_77,A_78)
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_214,plain,
    ( k7_relat_1('#skF_4','#skF_2') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_206,c_208])).

tff(c_223,plain,(
    k7_relat_1('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_214])).

tff(c_20,plain,(
    ! [A_15] :
      ( k5_relat_1(A_15,k6_relat_1(k2_relat_1(A_15))) = A_15
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_95,plain,(
    ! [A_15] :
      ( k5_relat_1(A_15,k6_partfun1(k2_relat_1(A_15))) = A_15
      | ~ v1_relat_1(A_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_20])).

tff(c_766,plain,(
    ! [A_138,B_139,C_140] :
      ( k5_relat_1(k5_relat_1(A_138,B_139),C_140) = k5_relat_1(A_138,k5_relat_1(B_139,C_140))
      | ~ v1_relat_1(C_140)
      | ~ v1_relat_1(B_139)
      | ~ v1_relat_1(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_797,plain,(
    ! [A_16,B_17,C_140] :
      ( k5_relat_1(k6_partfun1(A_16),k5_relat_1(B_17,C_140)) = k5_relat_1(k7_relat_1(B_17,A_16),C_140)
      | ~ v1_relat_1(C_140)
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1(k6_partfun1(A_16))
      | ~ v1_relat_1(B_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_766])).

tff(c_2603,plain,(
    ! [A_258,B_259,C_260] :
      ( k5_relat_1(k6_partfun1(A_258),k5_relat_1(B_259,C_260)) = k5_relat_1(k7_relat_1(B_259,A_258),C_260)
      | ~ v1_relat_1(C_260)
      | ~ v1_relat_1(B_259) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_797])).

tff(c_2696,plain,(
    ! [A_15,A_258] :
      ( k5_relat_1(k7_relat_1(A_15,A_258),k6_partfun1(k2_relat_1(A_15))) = k5_relat_1(k6_partfun1(A_258),A_15)
      | ~ v1_relat_1(k6_partfun1(k2_relat_1(A_15)))
      | ~ v1_relat_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_2603])).

tff(c_10488,plain,(
    ! [A_469,A_470] :
      ( k5_relat_1(k7_relat_1(A_469,A_470),k6_partfun1(k2_relat_1(A_469))) = k5_relat_1(k6_partfun1(A_470),A_469)
      | ~ v1_relat_1(A_469) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_2696])).

tff(c_10580,plain,
    ( k5_relat_1('#skF_4',k6_partfun1(k2_relat_1('#skF_4'))) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_10488])).

tff(c_10637,plain,(
    k5_relat_1('#skF_4',k6_partfun1(k2_relat_1('#skF_4'))) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_10580])).

tff(c_10678,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_10637,c_95])).

tff(c_10707,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_10678])).

tff(c_815,plain,(
    ! [A_16,B_17,C_140] :
      ( k5_relat_1(k6_partfun1(A_16),k5_relat_1(B_17,C_140)) = k5_relat_1(k7_relat_1(B_17,A_16),C_140)
      | ~ v1_relat_1(C_140)
      | ~ v1_relat_1(B_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_797])).

tff(c_10792,plain,(
    ! [A_16] :
      ( k5_relat_1(k7_relat_1(k6_partfun1('#skF_2'),A_16),'#skF_4') = k5_relat_1(k6_partfun1(A_16),'#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(k6_partfun1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10707,c_815])).

tff(c_11438,plain,(
    ! [A_485] : k5_relat_1(k7_relat_1(k6_partfun1('#skF_2'),A_485),'#skF_4') = k5_relat_1(k6_partfun1(A_485),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_156,c_10792])).

tff(c_398,plain,(
    ! [B_80,C_95] :
      ( v1_relat_1(k5_relat_1(B_80,C_95))
      | ~ v1_relat_1(C_95)
      | ~ v1_relat_1(B_80) ) ),
    inference(resolution,[status(thm)],[c_254,c_384])).

tff(c_11473,plain,(
    ! [A_485] :
      ( v1_relat_1(k5_relat_1(k6_partfun1(A_485),'#skF_4'))
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(k7_relat_1(k6_partfun1('#skF_2'),A_485)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11438,c_398])).

tff(c_11678,plain,(
    ! [A_487] :
      ( v1_relat_1(k5_relat_1(k6_partfun1(A_487),'#skF_4'))
      | ~ v1_relat_1(k7_relat_1(k6_partfun1('#skF_2'),A_487)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_11473])).

tff(c_11682,plain,(
    ! [A_16] :
      ( v1_relat_1(k5_relat_1(k6_partfun1(A_16),'#skF_4'))
      | ~ v1_relat_1(k6_partfun1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_448,c_11678])).

tff(c_11931,plain,(
    ! [A_490] : v1_relat_1(k5_relat_1(k6_partfun1(A_490),'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_11682])).

tff(c_11957,plain,(
    ! [A_16] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_16))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_11931])).

tff(c_11972,plain,(
    ! [A_16] : v1_relat_1(k7_relat_1('#skF_4',A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_11957])).

tff(c_10770,plain,(
    k5_relat_1('#skF_4',k6_partfun1(k2_relat_1('#skF_4'))) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10707,c_10637])).

tff(c_10874,plain,(
    ! [A_16] :
      ( k5_relat_1(k7_relat_1('#skF_4',A_16),k6_partfun1(k2_relat_1('#skF_4'))) = k5_relat_1(k6_partfun1(A_16),'#skF_4')
      | ~ v1_relat_1(k6_partfun1(k2_relat_1('#skF_4')))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10770,c_815])).

tff(c_10909,plain,(
    ! [A_16] : k5_relat_1(k7_relat_1('#skF_4',A_16),k6_partfun1(k2_relat_1('#skF_4'))) = k5_relat_1(k6_partfun1(A_16),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_93,c_10874])).

tff(c_15919,plain,(
    ! [B_577,C_578,A_579] :
      ( k7_relat_1(k5_relat_1(B_577,C_578),A_579) = k5_relat_1(k7_relat_1(B_577,A_579),C_578)
      | ~ v1_relat_1(k5_relat_1(B_577,C_578))
      | ~ v1_relat_1(C_578)
      | ~ v1_relat_1(B_577) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2603,c_94])).

tff(c_15961,plain,(
    ! [A_579] :
      ( k7_relat_1(k5_relat_1('#skF_4',k6_partfun1(k2_relat_1('#skF_4'))),A_579) = k5_relat_1(k7_relat_1('#skF_4',A_579),k6_partfun1(k2_relat_1('#skF_4')))
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(k6_partfun1(k2_relat_1('#skF_4')))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10770,c_15919])).

tff(c_16120,plain,(
    ! [A_579] : k5_relat_1(k6_partfun1(A_579),'#skF_4') = k7_relat_1('#skF_4',A_579) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_93,c_156,c_10909,c_10770,c_15961])).

tff(c_16414,plain,(
    ! [A_581] : k5_relat_1(k6_partfun1(A_581),'#skF_4') = k7_relat_1('#skF_4',A_581) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_93,c_156,c_10909,c_10770,c_15961])).

tff(c_18,plain,(
    ! [A_14] : k2_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_96,plain,(
    ! [A_14] : k2_relat_1(k6_partfun1(A_14)) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_18])).

tff(c_803,plain,(
    ! [A_15,C_140] :
      ( k5_relat_1(A_15,k5_relat_1(k6_partfun1(k2_relat_1(A_15)),C_140)) = k5_relat_1(A_15,C_140)
      | ~ v1_relat_1(C_140)
      | ~ v1_relat_1(k6_partfun1(k2_relat_1(A_15)))
      | ~ v1_relat_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_766])).

tff(c_2331,plain,(
    ! [A_254,C_255] :
      ( k5_relat_1(A_254,k5_relat_1(k6_partfun1(k2_relat_1(A_254)),C_255)) = k5_relat_1(A_254,C_255)
      | ~ v1_relat_1(C_255)
      | ~ v1_relat_1(A_254) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_803])).

tff(c_2412,plain,(
    ! [A_16,C_255] :
      ( k7_relat_1(k5_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(A_16))),C_255),A_16) = k5_relat_1(k6_partfun1(A_16),C_255)
      | ~ v1_relat_1(C_255)
      | ~ v1_relat_1(k6_partfun1(A_16))
      | ~ v1_relat_1(k5_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(A_16))),C_255)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_2331])).

tff(c_2450,plain,(
    ! [A_16,C_255] :
      ( k7_relat_1(k5_relat_1(k6_partfun1(A_16),C_255),A_16) = k5_relat_1(k6_partfun1(A_16),C_255)
      | ~ v1_relat_1(C_255)
      | ~ v1_relat_1(k5_relat_1(k6_partfun1(A_16),C_255)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_93,c_96,c_2412])).

tff(c_16421,plain,(
    ! [A_581] :
      ( k7_relat_1(k5_relat_1(k6_partfun1(A_581),'#skF_4'),A_581) = k5_relat_1(k6_partfun1(A_581),'#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_581)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16414,c_2450])).

tff(c_16515,plain,(
    ! [A_581] : k7_relat_1(k7_relat_1('#skF_4',A_581),A_581) = k7_relat_1('#skF_4',A_581) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11972,c_156,c_16120,c_16120,c_16421])).

tff(c_76,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_521,plain,(
    ! [A_111,B_112,C_113] :
      ( k2_relset_1(A_111,B_112,C_113) = k2_relat_1(C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_527,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_521])).

tff(c_534,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_527])).

tff(c_88,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_72,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_26,plain,(
    ! [A_18] :
      ( v1_relat_1(k2_funct_1(A_18))
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_42,plain,(
    ! [A_24] :
      ( k5_relat_1(A_24,k2_funct_1(A_24)) = k6_relat_1(k1_relat_1(A_24))
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_90,plain,(
    ! [A_24] :
      ( k5_relat_1(A_24,k2_funct_1(A_24)) = k6_partfun1(k1_relat_1(A_24))
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_42])).

tff(c_539,plain,
    ( k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_534,c_95])).

tff(c_543,plain,(
    k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_539])).

tff(c_794,plain,(
    ! [C_140] :
      ( k5_relat_1('#skF_3',k5_relat_1(k6_partfun1('#skF_2'),C_140)) = k5_relat_1('#skF_3',C_140)
      | ~ v1_relat_1(C_140)
      | ~ v1_relat_1(k6_partfun1('#skF_2'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_543,c_766])).

tff(c_822,plain,(
    ! [C_141] :
      ( k5_relat_1('#skF_3',k5_relat_1(k6_partfun1('#skF_2'),C_141)) = k5_relat_1('#skF_3',C_141)
      | ~ v1_relat_1(C_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_93,c_794])).

tff(c_28,plain,(
    ! [B_20,C_21,A_19] :
      ( v4_relat_1(k5_relat_1(B_20,C_21),A_19)
      | ~ v1_relat_1(C_21)
      | ~ v4_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_831,plain,(
    ! [C_141,A_19] :
      ( v4_relat_1(k5_relat_1('#skF_3',C_141),A_19)
      | ~ v1_relat_1(k5_relat_1(k6_partfun1('#skF_2'),C_141))
      | ~ v4_relat_1('#skF_3',A_19)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(C_141) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_822,c_28])).

tff(c_1593,plain,(
    ! [C_197,A_198] :
      ( v4_relat_1(k5_relat_1('#skF_3',C_197),A_198)
      | ~ v1_relat_1(k5_relat_1(k6_partfun1('#skF_2'),C_197))
      | ~ v4_relat_1('#skF_3',A_198)
      | ~ v1_relat_1(C_197) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_831])).

tff(c_1602,plain,(
    ! [C_95,A_198] :
      ( v4_relat_1(k5_relat_1('#skF_3',C_95),A_198)
      | ~ v4_relat_1('#skF_3',A_198)
      | ~ v1_relat_1(C_95)
      | ~ v1_relat_1(k6_partfun1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_398,c_1593])).

tff(c_1625,plain,(
    ! [C_199,A_200] :
      ( v4_relat_1(k5_relat_1('#skF_3',C_199),A_200)
      | ~ v4_relat_1('#skF_3',A_200)
      | ~ v1_relat_1(C_199) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_1602])).

tff(c_1632,plain,(
    ! [A_200] :
      ( v4_relat_1(k6_partfun1(k1_relat_1('#skF_3')),A_200)
      | ~ v4_relat_1('#skF_3',A_200)
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_1625])).

tff(c_1648,plain,(
    ! [A_200] :
      ( v4_relat_1(k6_partfun1(k1_relat_1('#skF_3')),A_200)
      | ~ v4_relat_1('#skF_3',A_200)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_88,c_72,c_1632])).

tff(c_1653,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1648])).

tff(c_1656,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_1653])).

tff(c_1660,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_88,c_1656])).

tff(c_1662,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1648])).

tff(c_205,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_84,c_194])).

tff(c_82,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_1518,plain,(
    ! [D_192,B_190,E_194,C_191,F_193,A_189] :
      ( m1_subset_1(k1_partfun1(A_189,B_190,C_191,D_192,E_194,F_193),k1_zfmisc_1(k2_zfmisc_1(A_189,D_192)))
      | ~ m1_subset_1(F_193,k1_zfmisc_1(k2_zfmisc_1(C_191,D_192)))
      | ~ v1_funct_1(F_193)
      | ~ m1_subset_1(E_194,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190)))
      | ~ v1_funct_1(E_194) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_56,plain,(
    ! [A_38] : m1_subset_1(k6_relat_1(A_38),k1_zfmisc_1(k2_zfmisc_1(A_38,A_38))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_89,plain,(
    ! [A_38] : m1_subset_1(k6_partfun1(A_38),k1_zfmisc_1(k2_zfmisc_1(A_38,A_38))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_56])).

tff(c_74,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_1067,plain,(
    ! [D_148,C_149,A_150,B_151] :
      ( D_148 = C_149
      | ~ r2_relset_1(A_150,B_151,C_149,D_148)
      | ~ m1_subset_1(D_148,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151)))
      | ~ m1_subset_1(C_149,k1_zfmisc_1(k2_zfmisc_1(A_150,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1075,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_74,c_1067])).

tff(c_1090,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_1075])).

tff(c_1099,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1090])).

tff(c_1531,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1518,c_1099])).

tff(c_1553,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_84,c_82,c_78,c_1531])).

tff(c_1554,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1090])).

tff(c_1791,plain,(
    ! [D_217,F_220,E_219,B_215,A_216,C_218] :
      ( k1_partfun1(A_216,B_215,C_218,D_217,E_219,F_220) = k5_relat_1(E_219,F_220)
      | ~ m1_subset_1(F_220,k1_zfmisc_1(k2_zfmisc_1(C_218,D_217)))
      | ~ v1_funct_1(F_220)
      | ~ m1_subset_1(E_219,k1_zfmisc_1(k2_zfmisc_1(A_216,B_215)))
      | ~ v1_funct_1(E_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_1797,plain,(
    ! [A_216,B_215,E_219] :
      ( k1_partfun1(A_216,B_215,'#skF_2','#skF_1',E_219,'#skF_4') = k5_relat_1(E_219,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_219,k1_zfmisc_1(k2_zfmisc_1(A_216,B_215)))
      | ~ v1_funct_1(E_219) ) ),
    inference(resolution,[status(thm)],[c_78,c_1791])).

tff(c_1997,plain,(
    ! [A_244,B_245,E_246] :
      ( k1_partfun1(A_244,B_245,'#skF_2','#skF_1',E_246,'#skF_4') = k5_relat_1(E_246,'#skF_4')
      | ~ m1_subset_1(E_246,k1_zfmisc_1(k2_zfmisc_1(A_244,B_245)))
      | ~ v1_funct_1(E_246) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_1797])).

tff(c_2006,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_1997])).

tff(c_2014,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_1554,c_2006])).

tff(c_2027,plain,(
    ! [A_19] :
      ( v4_relat_1(k6_partfun1('#skF_1'),A_19)
      | ~ v1_relat_1('#skF_4')
      | ~ v4_relat_1('#skF_3',A_19)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2014,c_28])).

tff(c_2047,plain,(
    ! [A_247] :
      ( v4_relat_1(k6_partfun1('#skF_1'),A_247)
      | ~ v4_relat_1('#skF_3',A_247) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_156,c_2027])).

tff(c_16,plain,(
    ! [A_14] : k1_relat_1(k6_relat_1(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_97,plain,(
    ! [A_14] : k1_relat_1(k6_partfun1(A_14)) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_16])).

tff(c_286,plain,(
    ! [B_86,A_87] :
      ( r1_tarski(k1_relat_1(B_86),A_87)
      | ~ v4_relat_1(B_86,A_87)
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_294,plain,(
    ! [A_14,A_87] :
      ( r1_tarski(A_14,A_87)
      | ~ v4_relat_1(k6_partfun1(A_14),A_87)
      | ~ v1_relat_1(k6_partfun1(A_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_286])).

tff(c_298,plain,(
    ! [A_14,A_87] :
      ( r1_tarski(A_14,A_87)
      | ~ v4_relat_1(k6_partfun1(A_14),A_87) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_294])).

tff(c_2074,plain,(
    ! [A_248] :
      ( r1_tarski('#skF_1',A_248)
      | ~ v4_relat_1('#skF_3',A_248) ) ),
    inference(resolution,[status(thm)],[c_2047,c_298])).

tff(c_2081,plain,
    ( r1_tarski('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_254,c_2074])).

tff(c_2088,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_2081])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_296,plain,(
    ! [B_86,A_87] :
      ( k1_relat_1(B_86) = A_87
      | ~ r1_tarski(A_87,k1_relat_1(B_86))
      | ~ v4_relat_1(B_86,A_87)
      | ~ v1_relat_1(B_86) ) ),
    inference(resolution,[status(thm)],[c_286,c_2])).

tff(c_2106,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2088,c_296])).

tff(c_2130,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_205,c_2106])).

tff(c_477,plain,(
    ! [A_105] :
      ( k2_relat_1(k2_funct_1(A_105)) = k1_relat_1(A_105)
      | ~ v2_funct_1(A_105)
      | ~ v1_funct_1(A_105)
      | ~ v1_relat_1(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_2835,plain,(
    ! [A_262] :
      ( k5_relat_1(k2_funct_1(A_262),k6_partfun1(k1_relat_1(A_262))) = k2_funct_1(A_262)
      | ~ v1_relat_1(k2_funct_1(A_262))
      | ~ v2_funct_1(A_262)
      | ~ v1_funct_1(A_262)
      | ~ v1_relat_1(A_262) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_477,c_95])).

tff(c_2856,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2130,c_2835])).

tff(c_2874,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_88,c_72,c_1662,c_2856])).

tff(c_2686,plain,(
    ! [A_16,A_258,B_17] :
      ( k5_relat_1(k7_relat_1(k6_partfun1(A_16),A_258),B_17) = k5_relat_1(k6_partfun1(A_258),k7_relat_1(B_17,A_16))
      | ~ v1_relat_1(B_17)
      | ~ v1_relat_1(k6_partfun1(A_16))
      | ~ v1_relat_1(B_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_2603])).

tff(c_2728,plain,(
    ! [A_16,A_258,B_17] :
      ( k5_relat_1(k7_relat_1(k6_partfun1(A_16),A_258),B_17) = k5_relat_1(k6_partfun1(A_258),k7_relat_1(B_17,A_16))
      | ~ v1_relat_1(B_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_2686])).

tff(c_2643,plain,(
    ! [B_259,C_260,A_258] :
      ( k7_relat_1(k5_relat_1(B_259,C_260),A_258) = k5_relat_1(k7_relat_1(B_259,A_258),C_260)
      | ~ v1_relat_1(k5_relat_1(B_259,C_260))
      | ~ v1_relat_1(C_260)
      | ~ v1_relat_1(B_259) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2603,c_94])).

tff(c_16419,plain,(
    ! [A_581,A_258] :
      ( k7_relat_1(k5_relat_1(k6_partfun1(A_581),'#skF_4'),A_258) = k5_relat_1(k7_relat_1(k6_partfun1(A_581),A_258),'#skF_4')
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_581))
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(k6_partfun1(A_581)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16414,c_2643])).

tff(c_23631,plain,(
    ! [A_720,A_721] : k5_relat_1(k7_relat_1(k6_partfun1(A_720),A_721),'#skF_4') = k7_relat_1(k7_relat_1('#skF_4',A_720),A_721) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_156,c_11972,c_16120,c_16419])).

tff(c_23701,plain,(
    ! [A_258,A_16] :
      ( k5_relat_1(k6_partfun1(A_258),k7_relat_1('#skF_4',A_16)) = k7_relat_1(k7_relat_1('#skF_4',A_16),A_258)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2728,c_23631])).

tff(c_23753,plain,(
    ! [A_258,A_16] : k5_relat_1(k6_partfun1(A_258),k7_relat_1('#skF_4',A_16)) = k7_relat_1(k7_relat_1('#skF_4',A_16),A_258) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_23701])).

tff(c_819,plain,(
    ! [A_15,C_140] :
      ( k5_relat_1(A_15,k5_relat_1(k6_partfun1(k2_relat_1(A_15)),C_140)) = k5_relat_1(A_15,C_140)
      | ~ v1_relat_1(C_140)
      | ~ v1_relat_1(A_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_803])).

tff(c_16463,plain,(
    ! [A_15] :
      ( k5_relat_1(A_15,k7_relat_1('#skF_4',k2_relat_1(A_15))) = k5_relat_1(A_15,'#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(A_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16414,c_819])).

tff(c_16539,plain,(
    ! [A_15] :
      ( k5_relat_1(A_15,k7_relat_1('#skF_4',k2_relat_1(A_15))) = k5_relat_1(A_15,'#skF_4')
      | ~ v1_relat_1(A_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_16463])).

tff(c_40,plain,(
    ! [A_24] :
      ( k5_relat_1(k2_funct_1(A_24),A_24) = k6_relat_1(k2_relat_1(A_24))
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_91,plain,(
    ! [A_24] :
      ( k5_relat_1(k2_funct_1(A_24),A_24) = k6_partfun1(k2_relat_1(A_24))
      | ~ v2_funct_1(A_24)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_40])).

tff(c_5436,plain,(
    ! [A_338,C_339] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_338)),C_339) = k5_relat_1(k2_funct_1(A_338),k5_relat_1(A_338,C_339))
      | ~ v1_relat_1(C_339)
      | ~ v1_relat_1(A_338)
      | ~ v1_relat_1(k2_funct_1(A_338))
      | ~ v2_funct_1(A_338)
      | ~ v1_funct_1(A_338)
      | ~ v1_relat_1(A_338) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_766])).

tff(c_5667,plain,(
    ! [C_339] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_339)) = k5_relat_1(k6_partfun1('#skF_2'),C_339)
      | ~ v1_relat_1(C_339)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_534,c_5436])).

tff(c_38515,plain,(
    ! [C_938] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_938)) = k5_relat_1(k6_partfun1('#skF_2'),C_938)
      | ~ v1_relat_1(C_938) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_88,c_72,c_1662,c_155,c_5667])).

tff(c_38598,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k7_relat_1('#skF_4',k2_relat_1('#skF_3'))) = k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3','#skF_4'))
    | ~ v1_relat_1(k7_relat_1('#skF_4',k2_relat_1('#skF_3')))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16539,c_38515])).

tff(c_38735,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_11972,c_223,c_16515,c_534,c_2874,c_2014,c_23753,c_38598])).

tff(c_38737,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_38735])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:46:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.17/10.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.17/10.02  
% 18.17/10.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.17/10.03  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 18.17/10.03  
% 18.17/10.03  %Foreground sorts:
% 18.17/10.03  
% 18.17/10.03  
% 18.17/10.03  %Background operators:
% 18.17/10.03  
% 18.17/10.03  
% 18.17/10.03  %Foreground operators:
% 18.17/10.03  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 18.17/10.03  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 18.17/10.03  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 18.17/10.03  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 18.17/10.03  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.17/10.03  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 18.17/10.03  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 18.17/10.03  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 18.17/10.03  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 18.17/10.03  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 18.17/10.03  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 18.17/10.03  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 18.17/10.03  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 18.17/10.03  tff('#skF_2', type, '#skF_2': $i).
% 18.17/10.03  tff('#skF_3', type, '#skF_3': $i).
% 18.17/10.03  tff('#skF_1', type, '#skF_1': $i).
% 18.17/10.03  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 18.17/10.03  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 18.17/10.03  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 18.17/10.03  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.17/10.03  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 18.17/10.03  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 18.17/10.03  tff('#skF_4', type, '#skF_4': $i).
% 18.17/10.03  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 18.17/10.03  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.17/10.03  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 18.17/10.03  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 18.17/10.03  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 18.17/10.03  
% 18.38/10.05  tff(f_181, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 18.38/10.05  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 18.38/10.05  tff(f_155, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 18.38/10.05  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 18.38/10.05  tff(f_87, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 18.38/10.05  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 18.38/10.05  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 18.38/10.05  tff(f_83, axiom, (![A, B, C]: (((v1_relat_1(B) & v4_relat_1(B, A)) & v1_relat_1(C)) => (v1_relat_1(k5_relat_1(B, C)) & v4_relat_1(k5_relat_1(B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc26_relat_1)).
% 18.38/10.05  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 18.38/10.05  tff(f_43, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 18.38/10.05  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 18.38/10.05  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 18.38/10.05  tff(f_57, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 18.38/10.05  tff(f_121, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 18.38/10.05  tff(f_73, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 18.38/10.05  tff(f_107, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 18.38/10.05  tff(f_143, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 18.38/10.05  tff(f_131, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 18.38/10.05  tff(f_129, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 18.38/10.05  tff(f_153, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 18.38/10.05  tff(f_97, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 18.38/10.05  tff(c_66, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_181])).
% 18.38/10.05  tff(c_84, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_181])).
% 18.38/10.05  tff(c_143, plain, (![C_64, A_65, B_66]: (v1_relat_1(C_64) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 18.38/10.05  tff(c_155, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_143])).
% 18.38/10.05  tff(c_78, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_181])).
% 18.38/10.05  tff(c_156, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_78, c_143])).
% 18.38/10.05  tff(c_64, plain, (![A_51]: (k6_relat_1(A_51)=k6_partfun1(A_51))), inference(cnfTransformation, [status(thm)], [f_155])).
% 18.38/10.05  tff(c_22, plain, (![A_16, B_17]: (k5_relat_1(k6_relat_1(A_16), B_17)=k7_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 18.38/10.05  tff(c_94, plain, (![A_16, B_17]: (k5_relat_1(k6_partfun1(A_16), B_17)=k7_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_22])).
% 18.38/10.05  tff(c_32, plain, (![A_22]: (v1_relat_1(k6_relat_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 18.38/10.05  tff(c_93, plain, (![A_22]: (v1_relat_1(k6_partfun1(A_22)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_32])).
% 18.38/10.05  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.38/10.05  tff(c_244, plain, (![B_80, A_81]: (v4_relat_1(B_80, A_81) | ~r1_tarski(k1_relat_1(B_80), A_81) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_37])).
% 18.38/10.05  tff(c_254, plain, (![B_80]: (v4_relat_1(B_80, k1_relat_1(B_80)) | ~v1_relat_1(B_80))), inference(resolution, [status(thm)], [c_6, c_244])).
% 18.38/10.05  tff(c_384, plain, (![B_94, C_95, A_96]: (v1_relat_1(k5_relat_1(B_94, C_95)) | ~v1_relat_1(C_95) | ~v4_relat_1(B_94, A_96) | ~v1_relat_1(B_94))), inference(cnfTransformation, [status(thm)], [f_83])).
% 18.38/10.05  tff(c_437, plain, (![B_101, C_102]: (v1_relat_1(k5_relat_1(B_101, C_102)) | ~v1_relat_1(C_102) | ~v1_relat_1(B_101))), inference(resolution, [status(thm)], [c_254, c_384])).
% 18.38/10.05  tff(c_440, plain, (![B_17, A_16]: (v1_relat_1(k7_relat_1(B_17, A_16)) | ~v1_relat_1(B_17) | ~v1_relat_1(k6_partfun1(A_16)) | ~v1_relat_1(B_17))), inference(superposition, [status(thm), theory('equality')], [c_94, c_437])).
% 18.38/10.05  tff(c_448, plain, (![B_17, A_16]: (v1_relat_1(k7_relat_1(B_17, A_16)) | ~v1_relat_1(B_17))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_440])).
% 18.38/10.05  tff(c_194, plain, (![C_73, A_74, B_75]: (v4_relat_1(C_73, A_74) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1(A_74, B_75))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 18.38/10.05  tff(c_206, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_78, c_194])).
% 18.38/10.05  tff(c_208, plain, (![B_77, A_78]: (k7_relat_1(B_77, A_78)=B_77 | ~v4_relat_1(B_77, A_78) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_43])).
% 18.38/10.05  tff(c_214, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_206, c_208])).
% 18.38/10.05  tff(c_223, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_156, c_214])).
% 18.38/10.05  tff(c_20, plain, (![A_15]: (k5_relat_1(A_15, k6_relat_1(k2_relat_1(A_15)))=A_15 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 18.38/10.05  tff(c_95, plain, (![A_15]: (k5_relat_1(A_15, k6_partfun1(k2_relat_1(A_15)))=A_15 | ~v1_relat_1(A_15))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_20])).
% 18.38/10.05  tff(c_766, plain, (![A_138, B_139, C_140]: (k5_relat_1(k5_relat_1(A_138, B_139), C_140)=k5_relat_1(A_138, k5_relat_1(B_139, C_140)) | ~v1_relat_1(C_140) | ~v1_relat_1(B_139) | ~v1_relat_1(A_138))), inference(cnfTransformation, [status(thm)], [f_53])).
% 18.38/10.05  tff(c_797, plain, (![A_16, B_17, C_140]: (k5_relat_1(k6_partfun1(A_16), k5_relat_1(B_17, C_140))=k5_relat_1(k7_relat_1(B_17, A_16), C_140) | ~v1_relat_1(C_140) | ~v1_relat_1(B_17) | ~v1_relat_1(k6_partfun1(A_16)) | ~v1_relat_1(B_17))), inference(superposition, [status(thm), theory('equality')], [c_94, c_766])).
% 18.38/10.05  tff(c_2603, plain, (![A_258, B_259, C_260]: (k5_relat_1(k6_partfun1(A_258), k5_relat_1(B_259, C_260))=k5_relat_1(k7_relat_1(B_259, A_258), C_260) | ~v1_relat_1(C_260) | ~v1_relat_1(B_259))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_797])).
% 18.38/10.05  tff(c_2696, plain, (![A_15, A_258]: (k5_relat_1(k7_relat_1(A_15, A_258), k6_partfun1(k2_relat_1(A_15)))=k5_relat_1(k6_partfun1(A_258), A_15) | ~v1_relat_1(k6_partfun1(k2_relat_1(A_15))) | ~v1_relat_1(A_15) | ~v1_relat_1(A_15))), inference(superposition, [status(thm), theory('equality')], [c_95, c_2603])).
% 18.38/10.05  tff(c_10488, plain, (![A_469, A_470]: (k5_relat_1(k7_relat_1(A_469, A_470), k6_partfun1(k2_relat_1(A_469)))=k5_relat_1(k6_partfun1(A_470), A_469) | ~v1_relat_1(A_469))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_2696])).
% 18.38/10.05  tff(c_10580, plain, (k5_relat_1('#skF_4', k6_partfun1(k2_relat_1('#skF_4')))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_223, c_10488])).
% 18.38/10.05  tff(c_10637, plain, (k5_relat_1('#skF_4', k6_partfun1(k2_relat_1('#skF_4')))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_10580])).
% 18.38/10.05  tff(c_10678, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_10637, c_95])).
% 18.38/10.05  tff(c_10707, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_156, c_10678])).
% 18.38/10.05  tff(c_815, plain, (![A_16, B_17, C_140]: (k5_relat_1(k6_partfun1(A_16), k5_relat_1(B_17, C_140))=k5_relat_1(k7_relat_1(B_17, A_16), C_140) | ~v1_relat_1(C_140) | ~v1_relat_1(B_17))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_797])).
% 18.38/10.05  tff(c_10792, plain, (![A_16]: (k5_relat_1(k7_relat_1(k6_partfun1('#skF_2'), A_16), '#skF_4')=k5_relat_1(k6_partfun1(A_16), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k6_partfun1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_10707, c_815])).
% 18.38/10.05  tff(c_11438, plain, (![A_485]: (k5_relat_1(k7_relat_1(k6_partfun1('#skF_2'), A_485), '#skF_4')=k5_relat_1(k6_partfun1(A_485), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_156, c_10792])).
% 18.38/10.05  tff(c_398, plain, (![B_80, C_95]: (v1_relat_1(k5_relat_1(B_80, C_95)) | ~v1_relat_1(C_95) | ~v1_relat_1(B_80))), inference(resolution, [status(thm)], [c_254, c_384])).
% 18.38/10.05  tff(c_11473, plain, (![A_485]: (v1_relat_1(k5_relat_1(k6_partfun1(A_485), '#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1(k7_relat_1(k6_partfun1('#skF_2'), A_485)))), inference(superposition, [status(thm), theory('equality')], [c_11438, c_398])).
% 18.38/10.05  tff(c_11678, plain, (![A_487]: (v1_relat_1(k5_relat_1(k6_partfun1(A_487), '#skF_4')) | ~v1_relat_1(k7_relat_1(k6_partfun1('#skF_2'), A_487)))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_11473])).
% 18.38/10.05  tff(c_11682, plain, (![A_16]: (v1_relat_1(k5_relat_1(k6_partfun1(A_16), '#skF_4')) | ~v1_relat_1(k6_partfun1('#skF_2')))), inference(resolution, [status(thm)], [c_448, c_11678])).
% 18.38/10.05  tff(c_11931, plain, (![A_490]: (v1_relat_1(k5_relat_1(k6_partfun1(A_490), '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_11682])).
% 18.38/10.05  tff(c_11957, plain, (![A_16]: (v1_relat_1(k7_relat_1('#skF_4', A_16)) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_94, c_11931])).
% 18.38/10.05  tff(c_11972, plain, (![A_16]: (v1_relat_1(k7_relat_1('#skF_4', A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_11957])).
% 18.38/10.05  tff(c_10770, plain, (k5_relat_1('#skF_4', k6_partfun1(k2_relat_1('#skF_4')))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_10707, c_10637])).
% 18.38/10.05  tff(c_10874, plain, (![A_16]: (k5_relat_1(k7_relat_1('#skF_4', A_16), k6_partfun1(k2_relat_1('#skF_4')))=k5_relat_1(k6_partfun1(A_16), '#skF_4') | ~v1_relat_1(k6_partfun1(k2_relat_1('#skF_4'))) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_10770, c_815])).
% 18.38/10.05  tff(c_10909, plain, (![A_16]: (k5_relat_1(k7_relat_1('#skF_4', A_16), k6_partfun1(k2_relat_1('#skF_4')))=k5_relat_1(k6_partfun1(A_16), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_93, c_10874])).
% 18.38/10.05  tff(c_15919, plain, (![B_577, C_578, A_579]: (k7_relat_1(k5_relat_1(B_577, C_578), A_579)=k5_relat_1(k7_relat_1(B_577, A_579), C_578) | ~v1_relat_1(k5_relat_1(B_577, C_578)) | ~v1_relat_1(C_578) | ~v1_relat_1(B_577))), inference(superposition, [status(thm), theory('equality')], [c_2603, c_94])).
% 18.38/10.05  tff(c_15961, plain, (![A_579]: (k7_relat_1(k5_relat_1('#skF_4', k6_partfun1(k2_relat_1('#skF_4'))), A_579)=k5_relat_1(k7_relat_1('#skF_4', A_579), k6_partfun1(k2_relat_1('#skF_4'))) | ~v1_relat_1('#skF_4') | ~v1_relat_1(k6_partfun1(k2_relat_1('#skF_4'))) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_10770, c_15919])).
% 18.38/10.05  tff(c_16120, plain, (![A_579]: (k5_relat_1(k6_partfun1(A_579), '#skF_4')=k7_relat_1('#skF_4', A_579))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_93, c_156, c_10909, c_10770, c_15961])).
% 18.38/10.05  tff(c_16414, plain, (![A_581]: (k5_relat_1(k6_partfun1(A_581), '#skF_4')=k7_relat_1('#skF_4', A_581))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_93, c_156, c_10909, c_10770, c_15961])).
% 18.38/10.05  tff(c_18, plain, (![A_14]: (k2_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_57])).
% 18.38/10.05  tff(c_96, plain, (![A_14]: (k2_relat_1(k6_partfun1(A_14))=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_18])).
% 18.38/10.05  tff(c_803, plain, (![A_15, C_140]: (k5_relat_1(A_15, k5_relat_1(k6_partfun1(k2_relat_1(A_15)), C_140))=k5_relat_1(A_15, C_140) | ~v1_relat_1(C_140) | ~v1_relat_1(k6_partfun1(k2_relat_1(A_15))) | ~v1_relat_1(A_15) | ~v1_relat_1(A_15))), inference(superposition, [status(thm), theory('equality')], [c_95, c_766])).
% 18.38/10.05  tff(c_2331, plain, (![A_254, C_255]: (k5_relat_1(A_254, k5_relat_1(k6_partfun1(k2_relat_1(A_254)), C_255))=k5_relat_1(A_254, C_255) | ~v1_relat_1(C_255) | ~v1_relat_1(A_254))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_803])).
% 18.38/10.05  tff(c_2412, plain, (![A_16, C_255]: (k7_relat_1(k5_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(A_16))), C_255), A_16)=k5_relat_1(k6_partfun1(A_16), C_255) | ~v1_relat_1(C_255) | ~v1_relat_1(k6_partfun1(A_16)) | ~v1_relat_1(k5_relat_1(k6_partfun1(k2_relat_1(k6_partfun1(A_16))), C_255)))), inference(superposition, [status(thm), theory('equality')], [c_94, c_2331])).
% 18.38/10.05  tff(c_2450, plain, (![A_16, C_255]: (k7_relat_1(k5_relat_1(k6_partfun1(A_16), C_255), A_16)=k5_relat_1(k6_partfun1(A_16), C_255) | ~v1_relat_1(C_255) | ~v1_relat_1(k5_relat_1(k6_partfun1(A_16), C_255)))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_93, c_96, c_2412])).
% 18.38/10.05  tff(c_16421, plain, (![A_581]: (k7_relat_1(k5_relat_1(k6_partfun1(A_581), '#skF_4'), A_581)=k5_relat_1(k6_partfun1(A_581), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k7_relat_1('#skF_4', A_581)))), inference(superposition, [status(thm), theory('equality')], [c_16414, c_2450])).
% 18.38/10.05  tff(c_16515, plain, (![A_581]: (k7_relat_1(k7_relat_1('#skF_4', A_581), A_581)=k7_relat_1('#skF_4', A_581))), inference(demodulation, [status(thm), theory('equality')], [c_11972, c_156, c_16120, c_16120, c_16421])).
% 18.38/10.05  tff(c_76, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_181])).
% 18.38/10.05  tff(c_521, plain, (![A_111, B_112, C_113]: (k2_relset_1(A_111, B_112, C_113)=k2_relat_1(C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 18.38/10.05  tff(c_527, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_521])).
% 18.38/10.05  tff(c_534, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_527])).
% 18.38/10.05  tff(c_88, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_181])).
% 18.38/10.05  tff(c_72, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_181])).
% 18.38/10.05  tff(c_26, plain, (![A_18]: (v1_relat_1(k2_funct_1(A_18)) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_73])).
% 18.38/10.05  tff(c_42, plain, (![A_24]: (k5_relat_1(A_24, k2_funct_1(A_24))=k6_relat_1(k1_relat_1(A_24)) | ~v2_funct_1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_107])).
% 18.38/10.05  tff(c_90, plain, (![A_24]: (k5_relat_1(A_24, k2_funct_1(A_24))=k6_partfun1(k1_relat_1(A_24)) | ~v2_funct_1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_42])).
% 18.38/10.05  tff(c_539, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_534, c_95])).
% 18.38/10.05  tff(c_543, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_155, c_539])).
% 18.38/10.05  tff(c_794, plain, (![C_140]: (k5_relat_1('#skF_3', k5_relat_1(k6_partfun1('#skF_2'), C_140))=k5_relat_1('#skF_3', C_140) | ~v1_relat_1(C_140) | ~v1_relat_1(k6_partfun1('#skF_2')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_543, c_766])).
% 18.38/10.05  tff(c_822, plain, (![C_141]: (k5_relat_1('#skF_3', k5_relat_1(k6_partfun1('#skF_2'), C_141))=k5_relat_1('#skF_3', C_141) | ~v1_relat_1(C_141))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_93, c_794])).
% 18.38/10.05  tff(c_28, plain, (![B_20, C_21, A_19]: (v4_relat_1(k5_relat_1(B_20, C_21), A_19) | ~v1_relat_1(C_21) | ~v4_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_83])).
% 18.38/10.05  tff(c_831, plain, (![C_141, A_19]: (v4_relat_1(k5_relat_1('#skF_3', C_141), A_19) | ~v1_relat_1(k5_relat_1(k6_partfun1('#skF_2'), C_141)) | ~v4_relat_1('#skF_3', A_19) | ~v1_relat_1('#skF_3') | ~v1_relat_1(C_141))), inference(superposition, [status(thm), theory('equality')], [c_822, c_28])).
% 18.38/10.05  tff(c_1593, plain, (![C_197, A_198]: (v4_relat_1(k5_relat_1('#skF_3', C_197), A_198) | ~v1_relat_1(k5_relat_1(k6_partfun1('#skF_2'), C_197)) | ~v4_relat_1('#skF_3', A_198) | ~v1_relat_1(C_197))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_831])).
% 18.38/10.05  tff(c_1602, plain, (![C_95, A_198]: (v4_relat_1(k5_relat_1('#skF_3', C_95), A_198) | ~v4_relat_1('#skF_3', A_198) | ~v1_relat_1(C_95) | ~v1_relat_1(k6_partfun1('#skF_2')))), inference(resolution, [status(thm)], [c_398, c_1593])).
% 18.38/10.05  tff(c_1625, plain, (![C_199, A_200]: (v4_relat_1(k5_relat_1('#skF_3', C_199), A_200) | ~v4_relat_1('#skF_3', A_200) | ~v1_relat_1(C_199))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_1602])).
% 18.38/10.05  tff(c_1632, plain, (![A_200]: (v4_relat_1(k6_partfun1(k1_relat_1('#skF_3')), A_200) | ~v4_relat_1('#skF_3', A_200) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_90, c_1625])).
% 18.38/10.05  tff(c_1648, plain, (![A_200]: (v4_relat_1(k6_partfun1(k1_relat_1('#skF_3')), A_200) | ~v4_relat_1('#skF_3', A_200) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_88, c_72, c_1632])).
% 18.38/10.05  tff(c_1653, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1648])).
% 18.38/10.05  tff(c_1656, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_1653])).
% 18.38/10.05  tff(c_1660, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_155, c_88, c_1656])).
% 18.38/10.05  tff(c_1662, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1648])).
% 18.38/10.05  tff(c_205, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_84, c_194])).
% 18.38/10.05  tff(c_82, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_181])).
% 18.38/10.05  tff(c_1518, plain, (![D_192, B_190, E_194, C_191, F_193, A_189]: (m1_subset_1(k1_partfun1(A_189, B_190, C_191, D_192, E_194, F_193), k1_zfmisc_1(k2_zfmisc_1(A_189, D_192))) | ~m1_subset_1(F_193, k1_zfmisc_1(k2_zfmisc_1(C_191, D_192))) | ~v1_funct_1(F_193) | ~m1_subset_1(E_194, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))) | ~v1_funct_1(E_194))), inference(cnfTransformation, [status(thm)], [f_143])).
% 18.38/10.05  tff(c_56, plain, (![A_38]: (m1_subset_1(k6_relat_1(A_38), k1_zfmisc_1(k2_zfmisc_1(A_38, A_38))))), inference(cnfTransformation, [status(thm)], [f_131])).
% 18.38/10.05  tff(c_89, plain, (![A_38]: (m1_subset_1(k6_partfun1(A_38), k1_zfmisc_1(k2_zfmisc_1(A_38, A_38))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_56])).
% 18.38/10.05  tff(c_74, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_181])).
% 18.38/10.05  tff(c_1067, plain, (![D_148, C_149, A_150, B_151]: (D_148=C_149 | ~r2_relset_1(A_150, B_151, C_149, D_148) | ~m1_subset_1(D_148, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))) | ~m1_subset_1(C_149, k1_zfmisc_1(k2_zfmisc_1(A_150, B_151))))), inference(cnfTransformation, [status(thm)], [f_129])).
% 18.38/10.05  tff(c_1075, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_74, c_1067])).
% 18.38/10.05  tff(c_1090, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_1075])).
% 18.38/10.05  tff(c_1099, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1090])).
% 18.38/10.05  tff(c_1531, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1518, c_1099])).
% 18.38/10.05  tff(c_1553, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_88, c_84, c_82, c_78, c_1531])).
% 18.38/10.05  tff(c_1554, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1090])).
% 18.38/10.05  tff(c_1791, plain, (![D_217, F_220, E_219, B_215, A_216, C_218]: (k1_partfun1(A_216, B_215, C_218, D_217, E_219, F_220)=k5_relat_1(E_219, F_220) | ~m1_subset_1(F_220, k1_zfmisc_1(k2_zfmisc_1(C_218, D_217))) | ~v1_funct_1(F_220) | ~m1_subset_1(E_219, k1_zfmisc_1(k2_zfmisc_1(A_216, B_215))) | ~v1_funct_1(E_219))), inference(cnfTransformation, [status(thm)], [f_153])).
% 18.38/10.05  tff(c_1797, plain, (![A_216, B_215, E_219]: (k1_partfun1(A_216, B_215, '#skF_2', '#skF_1', E_219, '#skF_4')=k5_relat_1(E_219, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_219, k1_zfmisc_1(k2_zfmisc_1(A_216, B_215))) | ~v1_funct_1(E_219))), inference(resolution, [status(thm)], [c_78, c_1791])).
% 18.38/10.05  tff(c_1997, plain, (![A_244, B_245, E_246]: (k1_partfun1(A_244, B_245, '#skF_2', '#skF_1', E_246, '#skF_4')=k5_relat_1(E_246, '#skF_4') | ~m1_subset_1(E_246, k1_zfmisc_1(k2_zfmisc_1(A_244, B_245))) | ~v1_funct_1(E_246))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_1797])).
% 18.38/10.05  tff(c_2006, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_84, c_1997])).
% 18.38/10.05  tff(c_2014, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_1554, c_2006])).
% 18.38/10.05  tff(c_2027, plain, (![A_19]: (v4_relat_1(k6_partfun1('#skF_1'), A_19) | ~v1_relat_1('#skF_4') | ~v4_relat_1('#skF_3', A_19) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2014, c_28])).
% 18.38/10.05  tff(c_2047, plain, (![A_247]: (v4_relat_1(k6_partfun1('#skF_1'), A_247) | ~v4_relat_1('#skF_3', A_247))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_156, c_2027])).
% 18.38/10.05  tff(c_16, plain, (![A_14]: (k1_relat_1(k6_relat_1(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_57])).
% 18.38/10.05  tff(c_97, plain, (![A_14]: (k1_relat_1(k6_partfun1(A_14))=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_16])).
% 18.38/10.05  tff(c_286, plain, (![B_86, A_87]: (r1_tarski(k1_relat_1(B_86), A_87) | ~v4_relat_1(B_86, A_87) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_37])).
% 18.38/10.05  tff(c_294, plain, (![A_14, A_87]: (r1_tarski(A_14, A_87) | ~v4_relat_1(k6_partfun1(A_14), A_87) | ~v1_relat_1(k6_partfun1(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_286])).
% 18.38/10.05  tff(c_298, plain, (![A_14, A_87]: (r1_tarski(A_14, A_87) | ~v4_relat_1(k6_partfun1(A_14), A_87))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_294])).
% 18.38/10.05  tff(c_2074, plain, (![A_248]: (r1_tarski('#skF_1', A_248) | ~v4_relat_1('#skF_3', A_248))), inference(resolution, [status(thm)], [c_2047, c_298])).
% 18.38/10.05  tff(c_2081, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_254, c_2074])).
% 18.38/10.05  tff(c_2088, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_2081])).
% 18.38/10.05  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 18.38/10.05  tff(c_296, plain, (![B_86, A_87]: (k1_relat_1(B_86)=A_87 | ~r1_tarski(A_87, k1_relat_1(B_86)) | ~v4_relat_1(B_86, A_87) | ~v1_relat_1(B_86))), inference(resolution, [status(thm)], [c_286, c_2])).
% 18.38/10.05  tff(c_2106, plain, (k1_relat_1('#skF_3')='#skF_1' | ~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2088, c_296])).
% 18.38/10.05  tff(c_2130, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_155, c_205, c_2106])).
% 18.38/10.05  tff(c_477, plain, (![A_105]: (k2_relat_1(k2_funct_1(A_105))=k1_relat_1(A_105) | ~v2_funct_1(A_105) | ~v1_funct_1(A_105) | ~v1_relat_1(A_105))), inference(cnfTransformation, [status(thm)], [f_97])).
% 18.38/10.05  tff(c_2835, plain, (![A_262]: (k5_relat_1(k2_funct_1(A_262), k6_partfun1(k1_relat_1(A_262)))=k2_funct_1(A_262) | ~v1_relat_1(k2_funct_1(A_262)) | ~v2_funct_1(A_262) | ~v1_funct_1(A_262) | ~v1_relat_1(A_262))), inference(superposition, [status(thm), theory('equality')], [c_477, c_95])).
% 18.38/10.05  tff(c_2856, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2130, c_2835])).
% 18.38/10.05  tff(c_2874, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_88, c_72, c_1662, c_2856])).
% 18.38/10.05  tff(c_2686, plain, (![A_16, A_258, B_17]: (k5_relat_1(k7_relat_1(k6_partfun1(A_16), A_258), B_17)=k5_relat_1(k6_partfun1(A_258), k7_relat_1(B_17, A_16)) | ~v1_relat_1(B_17) | ~v1_relat_1(k6_partfun1(A_16)) | ~v1_relat_1(B_17))), inference(superposition, [status(thm), theory('equality')], [c_94, c_2603])).
% 18.38/10.05  tff(c_2728, plain, (![A_16, A_258, B_17]: (k5_relat_1(k7_relat_1(k6_partfun1(A_16), A_258), B_17)=k5_relat_1(k6_partfun1(A_258), k7_relat_1(B_17, A_16)) | ~v1_relat_1(B_17))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_2686])).
% 18.38/10.05  tff(c_2643, plain, (![B_259, C_260, A_258]: (k7_relat_1(k5_relat_1(B_259, C_260), A_258)=k5_relat_1(k7_relat_1(B_259, A_258), C_260) | ~v1_relat_1(k5_relat_1(B_259, C_260)) | ~v1_relat_1(C_260) | ~v1_relat_1(B_259))), inference(superposition, [status(thm), theory('equality')], [c_2603, c_94])).
% 18.38/10.05  tff(c_16419, plain, (![A_581, A_258]: (k7_relat_1(k5_relat_1(k6_partfun1(A_581), '#skF_4'), A_258)=k5_relat_1(k7_relat_1(k6_partfun1(A_581), A_258), '#skF_4') | ~v1_relat_1(k7_relat_1('#skF_4', A_581)) | ~v1_relat_1('#skF_4') | ~v1_relat_1(k6_partfun1(A_581)))), inference(superposition, [status(thm), theory('equality')], [c_16414, c_2643])).
% 18.38/10.05  tff(c_23631, plain, (![A_720, A_721]: (k5_relat_1(k7_relat_1(k6_partfun1(A_720), A_721), '#skF_4')=k7_relat_1(k7_relat_1('#skF_4', A_720), A_721))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_156, c_11972, c_16120, c_16419])).
% 18.38/10.05  tff(c_23701, plain, (![A_258, A_16]: (k5_relat_1(k6_partfun1(A_258), k7_relat_1('#skF_4', A_16))=k7_relat_1(k7_relat_1('#skF_4', A_16), A_258) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2728, c_23631])).
% 18.38/10.05  tff(c_23753, plain, (![A_258, A_16]: (k5_relat_1(k6_partfun1(A_258), k7_relat_1('#skF_4', A_16))=k7_relat_1(k7_relat_1('#skF_4', A_16), A_258))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_23701])).
% 18.38/10.05  tff(c_819, plain, (![A_15, C_140]: (k5_relat_1(A_15, k5_relat_1(k6_partfun1(k2_relat_1(A_15)), C_140))=k5_relat_1(A_15, C_140) | ~v1_relat_1(C_140) | ~v1_relat_1(A_15))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_803])).
% 18.38/10.05  tff(c_16463, plain, (![A_15]: (k5_relat_1(A_15, k7_relat_1('#skF_4', k2_relat_1(A_15)))=k5_relat_1(A_15, '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(A_15))), inference(superposition, [status(thm), theory('equality')], [c_16414, c_819])).
% 18.38/10.05  tff(c_16539, plain, (![A_15]: (k5_relat_1(A_15, k7_relat_1('#skF_4', k2_relat_1(A_15)))=k5_relat_1(A_15, '#skF_4') | ~v1_relat_1(A_15))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_16463])).
% 18.38/10.05  tff(c_40, plain, (![A_24]: (k5_relat_1(k2_funct_1(A_24), A_24)=k6_relat_1(k2_relat_1(A_24)) | ~v2_funct_1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_107])).
% 18.38/10.05  tff(c_91, plain, (![A_24]: (k5_relat_1(k2_funct_1(A_24), A_24)=k6_partfun1(k2_relat_1(A_24)) | ~v2_funct_1(A_24) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_40])).
% 18.38/10.05  tff(c_5436, plain, (![A_338, C_339]: (k5_relat_1(k6_partfun1(k2_relat_1(A_338)), C_339)=k5_relat_1(k2_funct_1(A_338), k5_relat_1(A_338, C_339)) | ~v1_relat_1(C_339) | ~v1_relat_1(A_338) | ~v1_relat_1(k2_funct_1(A_338)) | ~v2_funct_1(A_338) | ~v1_funct_1(A_338) | ~v1_relat_1(A_338))), inference(superposition, [status(thm), theory('equality')], [c_91, c_766])).
% 18.38/10.05  tff(c_5667, plain, (![C_339]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_339))=k5_relat_1(k6_partfun1('#skF_2'), C_339) | ~v1_relat_1(C_339) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_534, c_5436])).
% 18.38/10.05  tff(c_38515, plain, (![C_938]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_938))=k5_relat_1(k6_partfun1('#skF_2'), C_938) | ~v1_relat_1(C_938))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_88, c_72, c_1662, c_155, c_5667])).
% 18.38/10.05  tff(c_38598, plain, (k5_relat_1(k6_partfun1('#skF_2'), k7_relat_1('#skF_4', k2_relat_1('#skF_3')))=k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', '#skF_4')) | ~v1_relat_1(k7_relat_1('#skF_4', k2_relat_1('#skF_3'))) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16539, c_38515])).
% 18.38/10.05  tff(c_38735, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_155, c_11972, c_223, c_16515, c_534, c_2874, c_2014, c_23753, c_38598])).
% 18.38/10.05  tff(c_38737, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_38735])).
% 18.38/10.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.38/10.05  
% 18.38/10.05  Inference rules
% 18.38/10.05  ----------------------
% 18.38/10.05  #Ref     : 0
% 18.38/10.05  #Sup     : 7990
% 18.38/10.05  #Fact    : 0
% 18.38/10.05  #Define  : 0
% 18.38/10.05  #Split   : 14
% 18.38/10.05  #Chain   : 0
% 18.38/10.05  #Close   : 0
% 18.38/10.05  
% 18.38/10.05  Ordering : KBO
% 18.38/10.05  
% 18.38/10.06  Simplification rules
% 18.38/10.06  ----------------------
% 18.38/10.06  #Subsume      : 1029
% 18.38/10.06  #Demod        : 16822
% 18.38/10.06  #Tautology    : 2792
% 18.38/10.06  #SimpNegUnit  : 1
% 18.38/10.06  #BackRed      : 82
% 18.38/10.06  
% 18.38/10.06  #Partial instantiations: 0
% 18.38/10.06  #Strategies tried      : 1
% 18.38/10.06  
% 18.38/10.06  Timing (in seconds)
% 18.38/10.06  ----------------------
% 18.38/10.06  Preprocessing        : 0.36
% 18.38/10.06  Parsing              : 0.19
% 18.38/10.06  CNF conversion       : 0.03
% 18.38/10.06  Main loop            : 8.90
% 18.38/10.06  Inferencing          : 1.65
% 18.38/10.06  Reduction            : 5.02
% 18.38/10.06  Demodulation         : 4.42
% 18.38/10.06  BG Simplification    : 0.16
% 18.38/10.06  Subsumption          : 1.67
% 18.38/10.06  Abstraction          : 0.27
% 18.38/10.06  MUC search           : 0.00
% 18.38/10.06  Cooper               : 0.00
% 18.38/10.06  Total                : 9.31
% 18.38/10.06  Index Insertion      : 0.00
% 18.38/10.06  Index Deletion       : 0.00
% 18.38/10.06  Index Matching       : 0.00
% 18.38/10.06  BG Taut test         : 0.00
%------------------------------------------------------------------------------
