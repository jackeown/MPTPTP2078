%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:59 EST 2020

% Result     : Theorem 14.20s
% Output     : CNFRefutation 14.20s
% Verified   : 
% Statistics : Number of formulae       :  222 (2397 expanded)
%              Number of leaves         :   49 ( 950 expanded)
%              Depth                    :   18
%              Number of atoms          :  508 (8451 expanded)
%              Number of equality atoms :  107 ( 763 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v2_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > k11_relat_1 > #nlpp > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_197,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,k2_funct_2(A,B)),k6_partfun1(A))
          & r2_relset_1(A,A,k1_partfun1(A,A,A,A,k2_funct_2(A,B),B),k6_partfun1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_funct_2)).

tff(f_168,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_144,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(f_158,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_148,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A)))
         => ( ! [D] :
                ( r2_hidden(D,A)
               => k11_relat_1(B,D) = k11_relat_1(C,D) )
           => r2_relset_1(A,A,B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relset_1)).

tff(f_128,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_116,axiom,(
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

tff(f_62,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_74,axiom,(
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

tff(f_32,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_30,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

tff(c_78,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_76,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_74,plain,(
    v3_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_17778,plain,(
    ! [A_988,B_989] :
      ( k2_funct_2(A_988,B_989) = k2_funct_1(B_989)
      | ~ m1_subset_1(B_989,k1_zfmisc_1(k2_zfmisc_1(A_988,A_988)))
      | ~ v3_funct_2(B_989,A_988,A_988)
      | ~ v1_funct_2(B_989,A_988,A_988)
      | ~ v1_funct_1(B_989) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_17784,plain,
    ( k2_funct_2('#skF_3','#skF_4') = k2_funct_1('#skF_4')
    | ~ v3_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_17778])).

tff(c_17796,plain,(
    k2_funct_2('#skF_3','#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_17784])).

tff(c_17730,plain,(
    ! [A_981,B_982] :
      ( v1_funct_1(k2_funct_2(A_981,B_982))
      | ~ m1_subset_1(B_982,k1_zfmisc_1(k2_zfmisc_1(A_981,A_981)))
      | ~ v3_funct_2(B_982,A_981,A_981)
      | ~ v1_funct_2(B_982,A_981,A_981)
      | ~ v1_funct_1(B_982) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_17736,plain,
    ( v1_funct_1(k2_funct_2('#skF_3','#skF_4'))
    | ~ v3_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_17730])).

tff(c_17748,plain,(
    v1_funct_1(k2_funct_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_17736])).

tff(c_17799,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17796,c_17748])).

tff(c_17945,plain,(
    ! [A_1022,B_1023] :
      ( m1_subset_1(k2_funct_2(A_1022,B_1023),k1_zfmisc_1(k2_zfmisc_1(A_1022,A_1022)))
      | ~ m1_subset_1(B_1023,k1_zfmisc_1(k2_zfmisc_1(A_1022,A_1022)))
      | ~ v3_funct_2(B_1023,A_1022,A_1022)
      | ~ v1_funct_2(B_1023,A_1022,A_1022)
      | ~ v1_funct_1(B_1023) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_18009,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v3_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_17796,c_17945])).

tff(c_18033,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_72,c_18009])).

tff(c_18120,plain,(
    ! [F_1029,A_1025,C_1027,E_1028,B_1024,D_1026] :
      ( k1_partfun1(A_1025,B_1024,C_1027,D_1026,E_1028,F_1029) = k5_relat_1(E_1028,F_1029)
      | ~ m1_subset_1(F_1029,k1_zfmisc_1(k2_zfmisc_1(C_1027,D_1026)))
      | ~ v1_funct_1(F_1029)
      | ~ m1_subset_1(E_1028,k1_zfmisc_1(k2_zfmisc_1(A_1025,B_1024)))
      | ~ v1_funct_1(E_1028) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_18128,plain,(
    ! [A_1025,B_1024,E_1028] :
      ( k1_partfun1(A_1025,B_1024,'#skF_3','#skF_3',E_1028,'#skF_4') = k5_relat_1(E_1028,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_1028,k1_zfmisc_1(k2_zfmisc_1(A_1025,B_1024)))
      | ~ v1_funct_1(E_1028) ) ),
    inference(resolution,[status(thm)],[c_72,c_18120])).

tff(c_21194,plain,(
    ! [A_1174,B_1175,E_1176] :
      ( k1_partfun1(A_1174,B_1175,'#skF_3','#skF_3',E_1176,'#skF_4') = k5_relat_1(E_1176,'#skF_4')
      | ~ m1_subset_1(E_1176,k1_zfmisc_1(k2_zfmisc_1(A_1174,B_1175)))
      | ~ v1_funct_1(E_1176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_18128])).

tff(c_21201,plain,
    ( k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3',k2_funct_1('#skF_4'),'#skF_4') = k5_relat_1(k2_funct_1('#skF_4'),'#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_18033,c_21194])).

tff(c_21218,plain,(
    k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3',k2_funct_1('#skF_4'),'#skF_4') = k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17799,c_21201])).

tff(c_533,plain,(
    ! [A_141,B_142] :
      ( k2_funct_2(A_141,B_142) = k2_funct_1(B_142)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(k2_zfmisc_1(A_141,A_141)))
      | ~ v3_funct_2(B_142,A_141,A_141)
      | ~ v1_funct_2(B_142,A_141,A_141)
      | ~ v1_funct_1(B_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_539,plain,
    ( k2_funct_2('#skF_3','#skF_4') = k2_funct_1('#skF_4')
    | ~ v3_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_533])).

tff(c_551,plain,(
    k2_funct_2('#skF_3','#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_539])).

tff(c_635,plain,(
    ! [A_159,B_160] :
      ( m1_subset_1(k2_funct_2(A_159,B_160),k1_zfmisc_1(k2_zfmisc_1(A_159,A_159)))
      | ~ m1_subset_1(B_160,k1_zfmisc_1(k2_zfmisc_1(A_159,A_159)))
      | ~ v3_funct_2(B_160,A_159,A_159)
      | ~ v1_funct_2(B_160,A_159,A_159)
      | ~ v1_funct_1(B_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_694,plain,
    ( m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v3_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_551,c_635])).

tff(c_716,plain,(
    m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_72,c_694])).

tff(c_20,plain,(
    ! [A_17,B_18,C_19] :
      ( k1_relset_1(A_17,B_18,C_19) = k1_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_785,plain,(
    k1_relset_1('#skF_3','#skF_3',k2_funct_1('#skF_4')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_716,c_20])).

tff(c_60,plain,(
    ! [A_44] : m1_subset_1(k6_partfun1(A_44),k1_zfmisc_1(k2_zfmisc_1(A_44,A_44))) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_24,plain,(
    ! [C_28,A_23,B_24] :
      ( k11_relat_1(C_28,'#skF_2'(A_23,B_24,C_28)) != k11_relat_1(B_24,'#skF_2'(A_23,B_24,C_28))
      | r2_relset_1(A_23,A_23,B_24,C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_23,A_23)))
      | ~ m1_subset_1(B_24,k1_zfmisc_1(k2_zfmisc_1(A_23,A_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_7592,plain,(
    ! [A_472,B_473] :
      ( r2_relset_1(A_472,A_472,B_473,B_473)
      | ~ m1_subset_1(B_473,k1_zfmisc_1(k2_zfmisc_1(A_472,A_472)))
      | ~ m1_subset_1(B_473,k1_zfmisc_1(k2_zfmisc_1(A_472,A_472))) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_24])).

tff(c_7605,plain,(
    ! [A_44] :
      ( r2_relset_1(A_44,A_44,k6_partfun1(A_44),k6_partfun1(A_44))
      | ~ m1_subset_1(k6_partfun1(A_44),k1_zfmisc_1(k2_zfmisc_1(A_44,A_44))) ) ),
    inference(resolution,[status(thm)],[c_60,c_7592])).

tff(c_7627,plain,(
    ! [A_44] : r2_relset_1(A_44,A_44,k6_partfun1(A_44),k6_partfun1(A_44)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_7605])).

tff(c_491,plain,(
    ! [A_135,B_136] :
      ( v1_funct_1(k2_funct_2(A_135,B_136))
      | ~ m1_subset_1(B_136,k1_zfmisc_1(k2_zfmisc_1(A_135,A_135)))
      | ~ v3_funct_2(B_136,A_135,A_135)
      | ~ v1_funct_2(B_136,A_135,A_135)
      | ~ v1_funct_1(B_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_497,plain,
    ( v1_funct_1(k2_funct_2('#skF_3','#skF_4'))
    | ~ v3_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_491])).

tff(c_509,plain,(
    v1_funct_1(k2_funct_2('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_497])).

tff(c_554,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_551,c_509])).

tff(c_50,plain,(
    ! [A_42,B_43] :
      ( m1_subset_1(k2_funct_2(A_42,B_43),k1_zfmisc_1(k2_zfmisc_1(A_42,A_42)))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k2_zfmisc_1(A_42,A_42)))
      | ~ v3_funct_2(B_43,A_42,A_42)
      | ~ v1_funct_2(B_43,A_42,A_42)
      | ~ v1_funct_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_859,plain,(
    ! [C_170,D_169,B_167,F_172,E_171,A_168] :
      ( k1_partfun1(A_168,B_167,C_170,D_169,E_171,F_172) = k5_relat_1(E_171,F_172)
      | ~ m1_subset_1(F_172,k1_zfmisc_1(k2_zfmisc_1(C_170,D_169)))
      | ~ v1_funct_1(F_172)
      | ~ m1_subset_1(E_171,k1_zfmisc_1(k2_zfmisc_1(A_168,B_167)))
      | ~ v1_funct_1(E_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_6465,plain,(
    ! [B_440,B_439,A_441,A_442,E_438] :
      ( k1_partfun1(A_442,B_439,A_441,A_441,E_438,k2_funct_2(A_441,B_440)) = k5_relat_1(E_438,k2_funct_2(A_441,B_440))
      | ~ v1_funct_1(k2_funct_2(A_441,B_440))
      | ~ m1_subset_1(E_438,k1_zfmisc_1(k2_zfmisc_1(A_442,B_439)))
      | ~ v1_funct_1(E_438)
      | ~ m1_subset_1(B_440,k1_zfmisc_1(k2_zfmisc_1(A_441,A_441)))
      | ~ v3_funct_2(B_440,A_441,A_441)
      | ~ v1_funct_2(B_440,A_441,A_441)
      | ~ v1_funct_1(B_440) ) ),
    inference(resolution,[status(thm)],[c_50,c_859])).

tff(c_6498,plain,(
    ! [A_441,B_440] :
      ( k1_partfun1('#skF_3','#skF_3',A_441,A_441,'#skF_4',k2_funct_2(A_441,B_440)) = k5_relat_1('#skF_4',k2_funct_2(A_441,B_440))
      | ~ v1_funct_1(k2_funct_2(A_441,B_440))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(B_440,k1_zfmisc_1(k2_zfmisc_1(A_441,A_441)))
      | ~ v3_funct_2(B_440,A_441,A_441)
      | ~ v1_funct_2(B_440,A_441,A_441)
      | ~ v1_funct_1(B_440) ) ),
    inference(resolution,[status(thm)],[c_72,c_6465])).

tff(c_6945,plain,(
    ! [A_453,B_454] :
      ( k1_partfun1('#skF_3','#skF_3',A_453,A_453,'#skF_4',k2_funct_2(A_453,B_454)) = k5_relat_1('#skF_4',k2_funct_2(A_453,B_454))
      | ~ v1_funct_1(k2_funct_2(A_453,B_454))
      | ~ m1_subset_1(B_454,k1_zfmisc_1(k2_zfmisc_1(A_453,A_453)))
      | ~ v3_funct_2(B_454,A_453,A_453)
      | ~ v1_funct_2(B_454,A_453,A_453)
      | ~ v1_funct_1(B_454) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_6498])).

tff(c_6981,plain,
    ( k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_4',k2_funct_2('#skF_3','#skF_4')) = k5_relat_1('#skF_4',k2_funct_2('#skF_3','#skF_4'))
    | ~ v1_funct_1(k2_funct_2('#skF_3','#skF_4'))
    | ~ v3_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_6945])).

tff(c_7027,plain,(
    k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_4',k2_funct_1('#skF_4')) = k5_relat_1('#skF_4',k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_554,c_551,c_551,c_551,c_6981])).

tff(c_70,plain,
    ( ~ r2_relset_1('#skF_3','#skF_3',k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3',k2_funct_2('#skF_3','#skF_4'),'#skF_4'),k6_partfun1('#skF_3'))
    | ~ r2_relset_1('#skF_3','#skF_3',k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_4',k2_funct_2('#skF_3','#skF_4')),k6_partfun1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_86,plain,(
    ~ r2_relset_1('#skF_3','#skF_3',k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_4',k2_funct_2('#skF_3','#skF_4')),k6_partfun1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_555,plain,(
    ~ r2_relset_1('#skF_3','#skF_3',k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_4',k2_funct_1('#skF_4')),k6_partfun1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_551,c_86])).

tff(c_7030,plain,(
    ~ r2_relset_1('#skF_3','#skF_3',k5_relat_1('#skF_4',k2_funct_1('#skF_4')),k6_partfun1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7027,c_555])).

tff(c_46,plain,(
    ! [F_41,D_39,A_36,E_40,C_38,B_37] :
      ( m1_subset_1(k1_partfun1(A_36,B_37,C_38,D_39,E_40,F_41),k1_zfmisc_1(k2_zfmisc_1(A_36,D_39)))
      | ~ m1_subset_1(F_41,k1_zfmisc_1(k2_zfmisc_1(C_38,D_39)))
      | ~ v1_funct_1(F_41)
      | ~ m1_subset_1(E_40,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_funct_1(E_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_7042,plain,
    ( m1_subset_1(k5_relat_1('#skF_4',k2_funct_1('#skF_4')),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7027,c_46])).

tff(c_7054,plain,(
    m1_subset_1(k5_relat_1('#skF_4',k2_funct_1('#skF_4')),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_72,c_554,c_716,c_7042])).

tff(c_600,plain,(
    ! [A_155,B_156,C_157] :
      ( r2_hidden('#skF_2'(A_155,B_156,C_157),A_155)
      | r2_relset_1(A_155,A_155,B_156,C_157)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_155,A_155)))
      | ~ m1_subset_1(B_156,k1_zfmisc_1(k2_zfmisc_1(A_155,A_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1586,plain,(
    ! [A_214,B_215] :
      ( r2_hidden('#skF_2'(A_214,B_215,k6_partfun1(A_214)),A_214)
      | r2_relset_1(A_214,A_214,B_215,k6_partfun1(A_214))
      | ~ m1_subset_1(B_215,k1_zfmisc_1(k2_zfmisc_1(A_214,A_214))) ) ),
    inference(resolution,[status(thm)],[c_60,c_600])).

tff(c_88,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_104,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_88])).

tff(c_272,plain,(
    ! [C_103,A_104,B_105] :
      ( v2_funct_1(C_103)
      | ~ v3_funct_2(C_103,A_104,B_105)
      | ~ v1_funct_1(C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_278,plain,
    ( v2_funct_1('#skF_4')
    | ~ v3_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_272])).

tff(c_290,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_278])).

tff(c_562,plain,(
    ! [A_147,B_148] :
      ( v1_funct_2(k2_funct_2(A_147,B_148),A_147,A_147)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(k2_zfmisc_1(A_147,A_147)))
      | ~ v3_funct_2(B_148,A_147,A_147)
      | ~ v1_funct_2(B_148,A_147,A_147)
      | ~ v1_funct_1(B_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_566,plain,
    ( v1_funct_2(k2_funct_2('#skF_3','#skF_4'),'#skF_3','#skF_3')
    | ~ v3_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_562])).

tff(c_576,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_551,c_566])).

tff(c_44,plain,(
    ! [B_34,A_33,C_35] :
      ( k1_xboole_0 = B_34
      | k1_relset_1(A_33,B_34,C_35) = A_33
      | ~ v1_funct_2(C_35,A_33,B_34)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_737,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_3','#skF_3',k2_funct_1('#skF_4')) = '#skF_3'
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_716,c_44])).

tff(c_778,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_3','#skF_3',k2_funct_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_576,c_737])).

tff(c_829,plain,(
    k1_relset_1('#skF_3','#skF_3',k2_funct_1('#skF_4')) = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_778])).

tff(c_839,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_829,c_785])).

tff(c_16,plain,(
    ! [A_13] :
      ( k1_relat_1(k2_funct_1(A_13)) = k2_relat_1(A_13)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_843,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_839,c_16])).

tff(c_850,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_78,c_290,c_843])).

tff(c_185,plain,(
    ! [A_89,B_90,C_91] :
      ( k2_relset_1(A_89,B_90,C_91) = k2_relat_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_201,plain,(
    k2_relset_1('#skF_3','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_185])).

tff(c_854,plain,(
    k2_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_850,c_201])).

tff(c_974,plain,(
    ! [A_173,C_174,B_175] :
      ( k6_partfun1(A_173) = k5_relat_1(C_174,k2_funct_1(C_174))
      | k1_xboole_0 = B_175
      | ~ v2_funct_1(C_174)
      | k2_relset_1(A_173,B_175,C_174) != B_175
      | ~ m1_subset_1(C_174,k1_zfmisc_1(k2_zfmisc_1(A_173,B_175)))
      | ~ v1_funct_2(C_174,A_173,B_175)
      | ~ v1_funct_1(C_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_984,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_3','#skF_3','#skF_4') != '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_974])).

tff(c_1002,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_854,c_290,c_984])).

tff(c_1007,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1002])).

tff(c_6,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_134,plain,(
    ! [C_71,B_72,A_73] :
      ( ~ v1_xboole_0(C_71)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(C_71))
      | ~ r2_hidden(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_146,plain,(
    ! [A_3,A_73] :
      ( ~ v1_xboole_0(A_3)
      | ~ r2_hidden(A_73,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_134])).

tff(c_147,plain,(
    ! [A_73] : ~ r2_hidden(A_73,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_1031,plain,(
    ! [A_73] : ~ r2_hidden(A_73,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1007,c_147])).

tff(c_1607,plain,(
    ! [B_215] :
      ( r2_relset_1('#skF_3','#skF_3',B_215,k6_partfun1('#skF_3'))
      | ~ m1_subset_1(B_215,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_1586,c_1031])).

tff(c_7125,plain,(
    r2_relset_1('#skF_3','#skF_3',k5_relat_1('#skF_4',k2_funct_1('#skF_4')),k6_partfun1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_7054,c_1607])).

tff(c_7274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7030,c_7125])).

tff(c_7275,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1002])).

tff(c_13722,plain,(
    ! [B_750,A_751,B_749,E_748,A_752] :
      ( k1_partfun1(A_752,B_749,A_751,A_751,E_748,k2_funct_2(A_751,B_750)) = k5_relat_1(E_748,k2_funct_2(A_751,B_750))
      | ~ v1_funct_1(k2_funct_2(A_751,B_750))
      | ~ m1_subset_1(E_748,k1_zfmisc_1(k2_zfmisc_1(A_752,B_749)))
      | ~ v1_funct_1(E_748)
      | ~ m1_subset_1(B_750,k1_zfmisc_1(k2_zfmisc_1(A_751,A_751)))
      | ~ v3_funct_2(B_750,A_751,A_751)
      | ~ v1_funct_2(B_750,A_751,A_751)
      | ~ v1_funct_1(B_750) ) ),
    inference(resolution,[status(thm)],[c_50,c_859])).

tff(c_13758,plain,(
    ! [A_751,B_750] :
      ( k1_partfun1('#skF_3','#skF_3',A_751,A_751,'#skF_4',k2_funct_2(A_751,B_750)) = k5_relat_1('#skF_4',k2_funct_2(A_751,B_750))
      | ~ v1_funct_1(k2_funct_2(A_751,B_750))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(B_750,k1_zfmisc_1(k2_zfmisc_1(A_751,A_751)))
      | ~ v3_funct_2(B_750,A_751,A_751)
      | ~ v1_funct_2(B_750,A_751,A_751)
      | ~ v1_funct_1(B_750) ) ),
    inference(resolution,[status(thm)],[c_72,c_13722])).

tff(c_14342,plain,(
    ! [A_766,B_767] :
      ( k1_partfun1('#skF_3','#skF_3',A_766,A_766,'#skF_4',k2_funct_2(A_766,B_767)) = k5_relat_1('#skF_4',k2_funct_2(A_766,B_767))
      | ~ v1_funct_1(k2_funct_2(A_766,B_767))
      | ~ m1_subset_1(B_767,k1_zfmisc_1(k2_zfmisc_1(A_766,A_766)))
      | ~ v3_funct_2(B_767,A_766,A_766)
      | ~ v1_funct_2(B_767,A_766,A_766)
      | ~ v1_funct_1(B_767) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_13758])).

tff(c_14381,plain,
    ( k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_4',k2_funct_2('#skF_3','#skF_4')) = k5_relat_1('#skF_4',k2_funct_2('#skF_3','#skF_4'))
    | ~ v1_funct_1(k2_funct_2('#skF_3','#skF_4'))
    | ~ v3_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_14342])).

tff(c_14438,plain,(
    k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3','#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_554,c_551,c_7275,c_551,c_551,c_14381])).

tff(c_14443,plain,(
    ~ r2_relset_1('#skF_3','#skF_3',k6_partfun1('#skF_3'),k6_partfun1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14438,c_555])).

tff(c_14448,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7627,c_14443])).

tff(c_14450,plain,(
    k1_relset_1('#skF_3','#skF_3',k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_778])).

tff(c_14693,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_785,c_14450])).

tff(c_14449,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_778])).

tff(c_42,plain,(
    ! [B_34,C_35] :
      ( k1_relset_1(k1_xboole_0,B_34,C_35) = k1_xboole_0
      | ~ v1_funct_2(C_35,k1_xboole_0,B_34)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_705,plain,(
    ! [B_160] :
      ( k1_relset_1(k1_xboole_0,k1_xboole_0,k2_funct_2(k1_xboole_0,B_160)) = k1_xboole_0
      | ~ v1_funct_2(k2_funct_2(k1_xboole_0,B_160),k1_xboole_0,k1_xboole_0)
      | ~ m1_subset_1(B_160,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ v3_funct_2(B_160,k1_xboole_0,k1_xboole_0)
      | ~ v1_funct_2(B_160,k1_xboole_0,k1_xboole_0)
      | ~ v1_funct_1(B_160) ) ),
    inference(resolution,[status(thm)],[c_635,c_42])).

tff(c_17252,plain,(
    ! [B_908] :
      ( k1_relset_1('#skF_3','#skF_3',k2_funct_2('#skF_3',B_908)) = '#skF_3'
      | ~ v1_funct_2(k2_funct_2('#skF_3',B_908),'#skF_3','#skF_3')
      | ~ m1_subset_1(B_908,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
      | ~ v3_funct_2(B_908,'#skF_3','#skF_3')
      | ~ v1_funct_2(B_908,'#skF_3','#skF_3')
      | ~ v1_funct_1(B_908) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14449,c_14449,c_14449,c_14449,c_14449,c_14449,c_14449,c_14449,c_14449,c_14449,c_14449,c_14449,c_14449,c_705])).

tff(c_17295,plain,
    ( k1_relset_1('#skF_3','#skF_3',k2_funct_2('#skF_3','#skF_4')) = '#skF_3'
    | ~ v1_funct_2(k2_funct_2('#skF_3','#skF_4'),'#skF_3','#skF_3')
    | ~ v3_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_17252])).

tff(c_17330,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_576,c_551,c_785,c_551,c_17295])).

tff(c_17332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14693,c_17330])).

tff(c_17333,plain,(
    ! [A_3] : ~ v1_xboole_0(A_3) ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_108,plain,(
    ! [B_66,A_67] :
      ( v1_xboole_0(B_66)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_67))
      | ~ v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_125,plain,(
    ! [A_3] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(A_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_108])).

tff(c_126,plain,(
    ! [A_3] : ~ v1_xboole_0(A_3) ),
    inference(splitLeft,[status(thm)],[c_125])).

tff(c_2,plain,(
    ! [A_1] : v1_xboole_0('#skF_1'(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_2])).

tff(c_130,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_125])).

tff(c_17338,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17333,c_130])).

tff(c_17339,plain,(
    ~ r2_relset_1('#skF_3','#skF_3',k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3',k2_funct_2('#skF_3','#skF_4'),'#skF_4'),k6_partfun1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_17800,plain,(
    ~ r2_relset_1('#skF_3','#skF_3',k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3',k2_funct_1('#skF_4'),'#skF_4'),k6_partfun1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17796,c_17339])).

tff(c_22311,plain,(
    ~ r2_relset_1('#skF_3','#skF_3',k5_relat_1(k2_funct_1('#skF_4'),'#skF_4'),k6_partfun1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21218,c_17800])).

tff(c_22315,plain,
    ( m1_subset_1(k5_relat_1(k2_funct_1('#skF_4'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_21218,c_46])).

tff(c_22319,plain,(
    m1_subset_1(k5_relat_1(k2_funct_1('#skF_4'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17799,c_18033,c_78,c_72,c_22315])).

tff(c_17867,plain,(
    ! [A_1006,B_1007,C_1008] :
      ( r2_hidden('#skF_2'(A_1006,B_1007,C_1008),A_1006)
      | r2_relset_1(A_1006,A_1006,B_1007,C_1008)
      | ~ m1_subset_1(C_1008,k1_zfmisc_1(k2_zfmisc_1(A_1006,A_1006)))
      | ~ m1_subset_1(B_1007,k1_zfmisc_1(k2_zfmisc_1(A_1006,A_1006))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_21723,plain,(
    ! [A_1206,B_1207] :
      ( r2_hidden('#skF_2'(A_1206,B_1207,k6_partfun1(A_1206)),A_1206)
      | r2_relset_1(A_1206,A_1206,B_1207,k6_partfun1(A_1206))
      | ~ m1_subset_1(B_1207,k1_zfmisc_1(k2_zfmisc_1(A_1206,A_1206))) ) ),
    inference(resolution,[status(thm)],[c_60,c_17867])).

tff(c_20450,plain,(
    ! [A_1137,B_1138] :
      ( r2_relset_1(A_1137,A_1137,B_1138,B_1138)
      | ~ m1_subset_1(B_1138,k1_zfmisc_1(k2_zfmisc_1(A_1137,A_1137)))
      | ~ m1_subset_1(B_1138,k1_zfmisc_1(k2_zfmisc_1(A_1137,A_1137))) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_24])).

tff(c_20465,plain,(
    ! [A_44] :
      ( r2_relset_1(A_44,A_44,k6_partfun1(A_44),k6_partfun1(A_44))
      | ~ m1_subset_1(k6_partfun1(A_44),k1_zfmisc_1(k2_zfmisc_1(A_44,A_44))) ) ),
    inference(resolution,[status(thm)],[c_60,c_20450])).

tff(c_20490,plain,(
    ! [A_44] : r2_relset_1(A_44,A_44,k6_partfun1(A_44),k6_partfun1(A_44)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_20465])).

tff(c_18488,plain,(
    ! [A_1051,B_1052,E_1053] :
      ( k1_partfun1(A_1051,B_1052,'#skF_3','#skF_3',E_1053,'#skF_4') = k5_relat_1(E_1053,'#skF_4')
      | ~ m1_subset_1(E_1053,k1_zfmisc_1(k2_zfmisc_1(A_1051,B_1052)))
      | ~ v1_funct_1(E_1053) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_18128])).

tff(c_18498,plain,
    ( k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3',k2_funct_1('#skF_4'),'#skF_4') = k5_relat_1(k2_funct_1('#skF_4'),'#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_18033,c_18488])).

tff(c_18516,plain,(
    k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3',k2_funct_1('#skF_4'),'#skF_4') = k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17799,c_18498])).

tff(c_19650,plain,(
    ~ r2_relset_1('#skF_3','#skF_3',k5_relat_1(k2_funct_1('#skF_4'),'#skF_4'),k6_partfun1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18516,c_17800])).

tff(c_19654,plain,
    ( m1_subset_1(k5_relat_1(k2_funct_1('#skF_4'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1(k2_funct_1('#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3')))
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_18516,c_46])).

tff(c_19658,plain,(
    m1_subset_1(k5_relat_1(k2_funct_1('#skF_4'),'#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17799,c_18033,c_78,c_72,c_19654])).

tff(c_18908,plain,(
    ! [A_1070,B_1071] :
      ( r2_hidden('#skF_2'(A_1070,B_1071,k6_partfun1(A_1070)),A_1070)
      | r2_relset_1(A_1070,A_1070,B_1071,k6_partfun1(A_1070))
      | ~ m1_subset_1(B_1071,k1_zfmisc_1(k2_zfmisc_1(A_1070,A_1070))) ) ),
    inference(resolution,[status(thm)],[c_60,c_17867])).

tff(c_17342,plain,(
    ! [C_910,A_911,B_912] :
      ( v1_relat_1(C_910)
      | ~ m1_subset_1(C_910,k1_zfmisc_1(k2_zfmisc_1(A_911,B_912))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_17358,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_17342])).

tff(c_17566,plain,(
    ! [C_958,A_959,B_960] :
      ( v2_funct_1(C_958)
      | ~ v3_funct_2(C_958,A_959,B_960)
      | ~ v1_funct_1(C_958)
      | ~ m1_subset_1(C_958,k1_zfmisc_1(k2_zfmisc_1(A_959,B_960))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_17572,plain,
    ( v2_funct_1('#skF_4')
    | ~ v3_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_17566])).

tff(c_17584,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_17572])).

tff(c_18114,plain,(
    k1_relset_1('#skF_3','#skF_3',k2_funct_1('#skF_4')) = k1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_18033,c_20])).

tff(c_17849,plain,(
    ! [A_1003,B_1004] :
      ( v1_funct_2(k2_funct_2(A_1003,B_1004),A_1003,A_1003)
      | ~ m1_subset_1(B_1004,k1_zfmisc_1(k2_zfmisc_1(A_1003,A_1003)))
      | ~ v3_funct_2(B_1004,A_1003,A_1003)
      | ~ v1_funct_2(B_1004,A_1003,A_1003)
      | ~ v1_funct_1(B_1004) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_17853,plain,
    ( v1_funct_2(k2_funct_2('#skF_3','#skF_4'),'#skF_3','#skF_3')
    | ~ v3_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_17849])).

tff(c_17863,plain,(
    v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_17796,c_17853])).

tff(c_18056,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_3','#skF_3',k2_funct_1('#skF_4')) = '#skF_3'
    | ~ v1_funct_2(k2_funct_1('#skF_4'),'#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_18033,c_44])).

tff(c_18104,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_3','#skF_3',k2_funct_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17863,c_18056])).

tff(c_18162,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1(k2_funct_1('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18114,c_18104])).

tff(c_18163,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_18162])).

tff(c_18168,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_18163,c_16])).

tff(c_18175,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17358,c_78,c_17584,c_18168])).

tff(c_17475,plain,(
    ! [A_943,B_944,C_945] :
      ( k2_relset_1(A_943,B_944,C_945) = k2_relat_1(C_945)
      | ~ m1_subset_1(C_945,k1_zfmisc_1(k2_zfmisc_1(A_943,B_944))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_17491,plain,(
    k2_relset_1('#skF_3','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_17475])).

tff(c_18179,plain,(
    ! [B_1030,C_1031,A_1032] :
      ( k6_partfun1(B_1030) = k5_relat_1(k2_funct_1(C_1031),C_1031)
      | k1_xboole_0 = B_1030
      | ~ v2_funct_1(C_1031)
      | k2_relset_1(A_1032,B_1030,C_1031) != B_1030
      | ~ m1_subset_1(C_1031,k1_zfmisc_1(k2_zfmisc_1(A_1032,B_1030)))
      | ~ v1_funct_2(C_1031,A_1032,B_1030)
      | ~ v1_funct_1(C_1031) ) ),
    inference(cnfTransformation,[status(thm)],[f_184])).

tff(c_18187,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_3','#skF_3','#skF_4') != '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_18179])).

tff(c_18202,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_3')
    | k1_xboole_0 = '#skF_3'
    | k2_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_17491,c_17584,c_18187])).

tff(c_18218,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18175,c_18202])).

tff(c_18219,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_18218])).

tff(c_17401,plain,(
    ! [C_922,B_923,A_924] :
      ( ~ v1_xboole_0(C_922)
      | ~ m1_subset_1(B_923,k1_zfmisc_1(C_922))
      | ~ r2_hidden(A_924,B_923) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_17413,plain,(
    ! [A_3,A_924] :
      ( ~ v1_xboole_0(A_3)
      | ~ r2_hidden(A_924,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_6,c_17401])).

tff(c_17414,plain,(
    ! [A_924] : ~ r2_hidden(A_924,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_17413])).

tff(c_18243,plain,(
    ! [A_924] : ~ r2_hidden(A_924,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18219,c_17414])).

tff(c_19858,plain,(
    ! [B_1120] :
      ( r2_relset_1('#skF_3','#skF_3',B_1120,k6_partfun1('#skF_3'))
      | ~ m1_subset_1(B_1120,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_18908,c_18243])).

tff(c_19861,plain,(
    r2_relset_1('#skF_3','#skF_3',k5_relat_1(k2_funct_1('#skF_4'),'#skF_4'),k6_partfun1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_19658,c_19858])).

tff(c_19903,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19650,c_19861])).

tff(c_19904,plain,(
    k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_18218])).

tff(c_19906,plain,(
    ! [A_1121,B_1122,E_1123] :
      ( k1_partfun1(A_1121,B_1122,'#skF_3','#skF_3',E_1123,'#skF_4') = k5_relat_1(E_1123,'#skF_4')
      | ~ m1_subset_1(E_1123,k1_zfmisc_1(k2_zfmisc_1(A_1121,B_1122)))
      | ~ v1_funct_1(E_1123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_18128])).

tff(c_19909,plain,
    ( k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3',k2_funct_1('#skF_4'),'#skF_4') = k5_relat_1(k2_funct_1('#skF_4'),'#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_18033,c_19906])).

tff(c_19929,plain,(
    k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3',k2_funct_1('#skF_4'),'#skF_4') = k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17799,c_19909])).

tff(c_20982,plain,(
    k1_partfun1('#skF_3','#skF_3','#skF_3','#skF_3',k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19904,c_19929])).

tff(c_20984,plain,(
    ~ r2_relset_1('#skF_3','#skF_3',k6_partfun1('#skF_3'),k6_partfun1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20982,c_17800])).

tff(c_20987,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20490,c_20984])).

tff(c_20988,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_18162])).

tff(c_21012,plain,(
    ! [A_924] : ~ r2_hidden(A_924,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20988,c_17414])).

tff(c_22657,plain,(
    ! [B_1254] :
      ( r2_relset_1('#skF_3','#skF_3',B_1254,k6_partfun1('#skF_3'))
      | ~ m1_subset_1(B_1254,k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_21723,c_21012])).

tff(c_22660,plain,(
    r2_relset_1('#skF_3','#skF_3',k5_relat_1(k2_funct_1('#skF_4'),'#skF_4'),k6_partfun1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_22319,c_22657])).

tff(c_22702,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22311,c_22660])).

tff(c_22703,plain,(
    ! [A_3] : ~ v1_xboole_0(A_3) ),
    inference(splitRight,[status(thm)],[c_17413])).

tff(c_17363,plain,(
    ! [B_916,A_917] :
      ( v1_xboole_0(B_916)
      | ~ m1_subset_1(B_916,k1_zfmisc_1(A_917))
      | ~ v1_xboole_0(A_917) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_17380,plain,(
    ! [A_3] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(A_3) ) ),
    inference(resolution,[status(thm)],[c_6,c_17363])).

tff(c_17381,plain,(
    ! [A_3] : ~ v1_xboole_0(A_3) ),
    inference(splitLeft,[status(thm)],[c_17380])).

tff(c_17397,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17381,c_2])).

tff(c_17398,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_17380])).

tff(c_22708,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22703,c_17398])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:04:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.20/6.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.20/6.86  
% 14.20/6.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.20/6.87  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v2_funct_2 > v1_partfun1 > r2_hidden > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k2_funct_2 > k11_relat_1 > #nlpp > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 14.20/6.87  
% 14.20/6.87  %Foreground sorts:
% 14.20/6.87  
% 14.20/6.87  
% 14.20/6.87  %Background operators:
% 14.20/6.87  
% 14.20/6.87  
% 14.20/6.87  %Foreground operators:
% 14.20/6.87  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 14.20/6.87  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 14.20/6.87  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 14.20/6.87  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 14.20/6.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.20/6.87  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 14.20/6.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.20/6.87  tff('#skF_1', type, '#skF_1': $i > $i).
% 14.20/6.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.20/6.87  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 14.20/6.87  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 14.20/6.87  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 14.20/6.87  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 14.20/6.87  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 14.20/6.87  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 14.20/6.87  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 14.20/6.87  tff('#skF_3', type, '#skF_3': $i).
% 14.20/6.87  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 14.20/6.87  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 14.20/6.87  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 14.20/6.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 14.20/6.87  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 14.20/6.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.20/6.87  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.20/6.87  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.20/6.87  tff('#skF_4', type, '#skF_4': $i).
% 14.20/6.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.20/6.87  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 14.20/6.87  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 14.20/6.87  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.20/6.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.20/6.87  
% 14.20/6.89  tff(f_197, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, k2_funct_2(A, B)), k6_partfun1(A)) & r2_relset_1(A, A, k1_partfun1(A, A, A, A, k2_funct_2(A, B), B), k6_partfun1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_funct_2)).
% 14.20/6.89  tff(f_168, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 14.20/6.89  tff(f_144, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 14.20/6.89  tff(f_158, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 14.20/6.89  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 14.20/6.89  tff(f_148, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 14.20/6.89  tff(f_86, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A))) => ((![D]: (r2_hidden(D, A) => (k11_relat_1(B, D) = k11_relat_1(C, D)))) => r2_relset_1(A, A, B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relset_1)).
% 14.20/6.89  tff(f_128, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 14.20/6.89  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 14.20/6.89  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 14.20/6.89  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 14.20/6.89  tff(f_62, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 14.20/6.89  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 14.20/6.89  tff(f_184, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 14.20/6.89  tff(f_32, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 14.20/6.89  tff(f_52, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 14.20/6.89  tff(f_39, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 14.20/6.89  tff(f_30, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_subset_1)).
% 14.20/6.89  tff(c_78, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_197])).
% 14.20/6.89  tff(c_76, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 14.20/6.89  tff(c_74, plain, (v3_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_197])).
% 14.20/6.89  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_197])).
% 14.20/6.89  tff(c_17778, plain, (![A_988, B_989]: (k2_funct_2(A_988, B_989)=k2_funct_1(B_989) | ~m1_subset_1(B_989, k1_zfmisc_1(k2_zfmisc_1(A_988, A_988))) | ~v3_funct_2(B_989, A_988, A_988) | ~v1_funct_2(B_989, A_988, A_988) | ~v1_funct_1(B_989))), inference(cnfTransformation, [status(thm)], [f_168])).
% 14.20/6.89  tff(c_17784, plain, (k2_funct_2('#skF_3', '#skF_4')=k2_funct_1('#skF_4') | ~v3_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_17778])).
% 14.20/6.89  tff(c_17796, plain, (k2_funct_2('#skF_3', '#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_17784])).
% 14.20/6.89  tff(c_17730, plain, (![A_981, B_982]: (v1_funct_1(k2_funct_2(A_981, B_982)) | ~m1_subset_1(B_982, k1_zfmisc_1(k2_zfmisc_1(A_981, A_981))) | ~v3_funct_2(B_982, A_981, A_981) | ~v1_funct_2(B_982, A_981, A_981) | ~v1_funct_1(B_982))), inference(cnfTransformation, [status(thm)], [f_144])).
% 14.20/6.89  tff(c_17736, plain, (v1_funct_1(k2_funct_2('#skF_3', '#skF_4')) | ~v3_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_17730])).
% 14.20/6.89  tff(c_17748, plain, (v1_funct_1(k2_funct_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_17736])).
% 14.20/6.89  tff(c_17799, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_17796, c_17748])).
% 14.20/6.89  tff(c_17945, plain, (![A_1022, B_1023]: (m1_subset_1(k2_funct_2(A_1022, B_1023), k1_zfmisc_1(k2_zfmisc_1(A_1022, A_1022))) | ~m1_subset_1(B_1023, k1_zfmisc_1(k2_zfmisc_1(A_1022, A_1022))) | ~v3_funct_2(B_1023, A_1022, A_1022) | ~v1_funct_2(B_1023, A_1022, A_1022) | ~v1_funct_1(B_1023))), inference(cnfTransformation, [status(thm)], [f_144])).
% 14.20/6.89  tff(c_18009, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v3_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_17796, c_17945])).
% 14.20/6.89  tff(c_18033, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_72, c_18009])).
% 14.20/6.89  tff(c_18120, plain, (![F_1029, A_1025, C_1027, E_1028, B_1024, D_1026]: (k1_partfun1(A_1025, B_1024, C_1027, D_1026, E_1028, F_1029)=k5_relat_1(E_1028, F_1029) | ~m1_subset_1(F_1029, k1_zfmisc_1(k2_zfmisc_1(C_1027, D_1026))) | ~v1_funct_1(F_1029) | ~m1_subset_1(E_1028, k1_zfmisc_1(k2_zfmisc_1(A_1025, B_1024))) | ~v1_funct_1(E_1028))), inference(cnfTransformation, [status(thm)], [f_158])).
% 14.20/6.89  tff(c_18128, plain, (![A_1025, B_1024, E_1028]: (k1_partfun1(A_1025, B_1024, '#skF_3', '#skF_3', E_1028, '#skF_4')=k5_relat_1(E_1028, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_1028, k1_zfmisc_1(k2_zfmisc_1(A_1025, B_1024))) | ~v1_funct_1(E_1028))), inference(resolution, [status(thm)], [c_72, c_18120])).
% 14.20/6.89  tff(c_21194, plain, (![A_1174, B_1175, E_1176]: (k1_partfun1(A_1174, B_1175, '#skF_3', '#skF_3', E_1176, '#skF_4')=k5_relat_1(E_1176, '#skF_4') | ~m1_subset_1(E_1176, k1_zfmisc_1(k2_zfmisc_1(A_1174, B_1175))) | ~v1_funct_1(E_1176))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_18128])).
% 14.20/6.89  tff(c_21201, plain, (k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', k2_funct_1('#skF_4'), '#skF_4')=k5_relat_1(k2_funct_1('#skF_4'), '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_18033, c_21194])).
% 14.20/6.89  tff(c_21218, plain, (k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', k2_funct_1('#skF_4'), '#skF_4')=k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_17799, c_21201])).
% 14.20/6.89  tff(c_533, plain, (![A_141, B_142]: (k2_funct_2(A_141, B_142)=k2_funct_1(B_142) | ~m1_subset_1(B_142, k1_zfmisc_1(k2_zfmisc_1(A_141, A_141))) | ~v3_funct_2(B_142, A_141, A_141) | ~v1_funct_2(B_142, A_141, A_141) | ~v1_funct_1(B_142))), inference(cnfTransformation, [status(thm)], [f_168])).
% 14.20/6.89  tff(c_539, plain, (k2_funct_2('#skF_3', '#skF_4')=k2_funct_1('#skF_4') | ~v3_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_533])).
% 14.20/6.89  tff(c_551, plain, (k2_funct_2('#skF_3', '#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_539])).
% 14.20/6.89  tff(c_635, plain, (![A_159, B_160]: (m1_subset_1(k2_funct_2(A_159, B_160), k1_zfmisc_1(k2_zfmisc_1(A_159, A_159))) | ~m1_subset_1(B_160, k1_zfmisc_1(k2_zfmisc_1(A_159, A_159))) | ~v3_funct_2(B_160, A_159, A_159) | ~v1_funct_2(B_160, A_159, A_159) | ~v1_funct_1(B_160))), inference(cnfTransformation, [status(thm)], [f_144])).
% 14.20/6.89  tff(c_694, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v3_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_551, c_635])).
% 14.20/6.89  tff(c_716, plain, (m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_72, c_694])).
% 14.20/6.89  tff(c_20, plain, (![A_17, B_18, C_19]: (k1_relset_1(A_17, B_18, C_19)=k1_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 14.20/6.89  tff(c_785, plain, (k1_relset_1('#skF_3', '#skF_3', k2_funct_1('#skF_4'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_716, c_20])).
% 14.20/6.89  tff(c_60, plain, (![A_44]: (m1_subset_1(k6_partfun1(A_44), k1_zfmisc_1(k2_zfmisc_1(A_44, A_44))))), inference(cnfTransformation, [status(thm)], [f_148])).
% 14.20/6.89  tff(c_24, plain, (![C_28, A_23, B_24]: (k11_relat_1(C_28, '#skF_2'(A_23, B_24, C_28))!=k11_relat_1(B_24, '#skF_2'(A_23, B_24, C_28)) | r2_relset_1(A_23, A_23, B_24, C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))) | ~m1_subset_1(B_24, k1_zfmisc_1(k2_zfmisc_1(A_23, A_23))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 14.20/6.89  tff(c_7592, plain, (![A_472, B_473]: (r2_relset_1(A_472, A_472, B_473, B_473) | ~m1_subset_1(B_473, k1_zfmisc_1(k2_zfmisc_1(A_472, A_472))) | ~m1_subset_1(B_473, k1_zfmisc_1(k2_zfmisc_1(A_472, A_472))))), inference(reflexivity, [status(thm), theory('equality')], [c_24])).
% 14.20/6.89  tff(c_7605, plain, (![A_44]: (r2_relset_1(A_44, A_44, k6_partfun1(A_44), k6_partfun1(A_44)) | ~m1_subset_1(k6_partfun1(A_44), k1_zfmisc_1(k2_zfmisc_1(A_44, A_44))))), inference(resolution, [status(thm)], [c_60, c_7592])).
% 14.20/6.89  tff(c_7627, plain, (![A_44]: (r2_relset_1(A_44, A_44, k6_partfun1(A_44), k6_partfun1(A_44)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_7605])).
% 14.20/6.89  tff(c_491, plain, (![A_135, B_136]: (v1_funct_1(k2_funct_2(A_135, B_136)) | ~m1_subset_1(B_136, k1_zfmisc_1(k2_zfmisc_1(A_135, A_135))) | ~v3_funct_2(B_136, A_135, A_135) | ~v1_funct_2(B_136, A_135, A_135) | ~v1_funct_1(B_136))), inference(cnfTransformation, [status(thm)], [f_144])).
% 14.20/6.89  tff(c_497, plain, (v1_funct_1(k2_funct_2('#skF_3', '#skF_4')) | ~v3_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_491])).
% 14.20/6.89  tff(c_509, plain, (v1_funct_1(k2_funct_2('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_497])).
% 14.20/6.89  tff(c_554, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_551, c_509])).
% 14.20/6.89  tff(c_50, plain, (![A_42, B_43]: (m1_subset_1(k2_funct_2(A_42, B_43), k1_zfmisc_1(k2_zfmisc_1(A_42, A_42))) | ~m1_subset_1(B_43, k1_zfmisc_1(k2_zfmisc_1(A_42, A_42))) | ~v3_funct_2(B_43, A_42, A_42) | ~v1_funct_2(B_43, A_42, A_42) | ~v1_funct_1(B_43))), inference(cnfTransformation, [status(thm)], [f_144])).
% 14.20/6.89  tff(c_859, plain, (![C_170, D_169, B_167, F_172, E_171, A_168]: (k1_partfun1(A_168, B_167, C_170, D_169, E_171, F_172)=k5_relat_1(E_171, F_172) | ~m1_subset_1(F_172, k1_zfmisc_1(k2_zfmisc_1(C_170, D_169))) | ~v1_funct_1(F_172) | ~m1_subset_1(E_171, k1_zfmisc_1(k2_zfmisc_1(A_168, B_167))) | ~v1_funct_1(E_171))), inference(cnfTransformation, [status(thm)], [f_158])).
% 14.20/6.89  tff(c_6465, plain, (![B_440, B_439, A_441, A_442, E_438]: (k1_partfun1(A_442, B_439, A_441, A_441, E_438, k2_funct_2(A_441, B_440))=k5_relat_1(E_438, k2_funct_2(A_441, B_440)) | ~v1_funct_1(k2_funct_2(A_441, B_440)) | ~m1_subset_1(E_438, k1_zfmisc_1(k2_zfmisc_1(A_442, B_439))) | ~v1_funct_1(E_438) | ~m1_subset_1(B_440, k1_zfmisc_1(k2_zfmisc_1(A_441, A_441))) | ~v3_funct_2(B_440, A_441, A_441) | ~v1_funct_2(B_440, A_441, A_441) | ~v1_funct_1(B_440))), inference(resolution, [status(thm)], [c_50, c_859])).
% 14.20/6.89  tff(c_6498, plain, (![A_441, B_440]: (k1_partfun1('#skF_3', '#skF_3', A_441, A_441, '#skF_4', k2_funct_2(A_441, B_440))=k5_relat_1('#skF_4', k2_funct_2(A_441, B_440)) | ~v1_funct_1(k2_funct_2(A_441, B_440)) | ~v1_funct_1('#skF_4') | ~m1_subset_1(B_440, k1_zfmisc_1(k2_zfmisc_1(A_441, A_441))) | ~v3_funct_2(B_440, A_441, A_441) | ~v1_funct_2(B_440, A_441, A_441) | ~v1_funct_1(B_440))), inference(resolution, [status(thm)], [c_72, c_6465])).
% 14.20/6.89  tff(c_6945, plain, (![A_453, B_454]: (k1_partfun1('#skF_3', '#skF_3', A_453, A_453, '#skF_4', k2_funct_2(A_453, B_454))=k5_relat_1('#skF_4', k2_funct_2(A_453, B_454)) | ~v1_funct_1(k2_funct_2(A_453, B_454)) | ~m1_subset_1(B_454, k1_zfmisc_1(k2_zfmisc_1(A_453, A_453))) | ~v3_funct_2(B_454, A_453, A_453) | ~v1_funct_2(B_454, A_453, A_453) | ~v1_funct_1(B_454))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_6498])).
% 14.20/6.89  tff(c_6981, plain, (k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_4', k2_funct_2('#skF_3', '#skF_4'))=k5_relat_1('#skF_4', k2_funct_2('#skF_3', '#skF_4')) | ~v1_funct_1(k2_funct_2('#skF_3', '#skF_4')) | ~v3_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_6945])).
% 14.20/6.89  tff(c_7027, plain, (k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_4', k2_funct_1('#skF_4'))=k5_relat_1('#skF_4', k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_554, c_551, c_551, c_551, c_6981])).
% 14.20/6.89  tff(c_70, plain, (~r2_relset_1('#skF_3', '#skF_3', k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', k2_funct_2('#skF_3', '#skF_4'), '#skF_4'), k6_partfun1('#skF_3')) | ~r2_relset_1('#skF_3', '#skF_3', k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_4', k2_funct_2('#skF_3', '#skF_4')), k6_partfun1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_197])).
% 14.20/6.89  tff(c_86, plain, (~r2_relset_1('#skF_3', '#skF_3', k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_4', k2_funct_2('#skF_3', '#skF_4')), k6_partfun1('#skF_3'))), inference(splitLeft, [status(thm)], [c_70])).
% 14.20/6.89  tff(c_555, plain, (~r2_relset_1('#skF_3', '#skF_3', k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_4', k2_funct_1('#skF_4')), k6_partfun1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_551, c_86])).
% 14.20/6.89  tff(c_7030, plain, (~r2_relset_1('#skF_3', '#skF_3', k5_relat_1('#skF_4', k2_funct_1('#skF_4')), k6_partfun1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7027, c_555])).
% 14.20/6.89  tff(c_46, plain, (![F_41, D_39, A_36, E_40, C_38, B_37]: (m1_subset_1(k1_partfun1(A_36, B_37, C_38, D_39, E_40, F_41), k1_zfmisc_1(k2_zfmisc_1(A_36, D_39))) | ~m1_subset_1(F_41, k1_zfmisc_1(k2_zfmisc_1(C_38, D_39))) | ~v1_funct_1(F_41) | ~m1_subset_1(E_40, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_1(E_40))), inference(cnfTransformation, [status(thm)], [f_128])).
% 14.20/6.89  tff(c_7042, plain, (m1_subset_1(k5_relat_1('#skF_4', k2_funct_1('#skF_4')), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7027, c_46])).
% 14.20/6.89  tff(c_7054, plain, (m1_subset_1(k5_relat_1('#skF_4', k2_funct_1('#skF_4')), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_72, c_554, c_716, c_7042])).
% 14.20/6.89  tff(c_600, plain, (![A_155, B_156, C_157]: (r2_hidden('#skF_2'(A_155, B_156, C_157), A_155) | r2_relset_1(A_155, A_155, B_156, C_157) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_155, A_155))) | ~m1_subset_1(B_156, k1_zfmisc_1(k2_zfmisc_1(A_155, A_155))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 14.20/6.89  tff(c_1586, plain, (![A_214, B_215]: (r2_hidden('#skF_2'(A_214, B_215, k6_partfun1(A_214)), A_214) | r2_relset_1(A_214, A_214, B_215, k6_partfun1(A_214)) | ~m1_subset_1(B_215, k1_zfmisc_1(k2_zfmisc_1(A_214, A_214))))), inference(resolution, [status(thm)], [c_60, c_600])).
% 14.20/6.89  tff(c_88, plain, (![C_62, A_63, B_64]: (v1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 14.20/6.89  tff(c_104, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_88])).
% 14.20/6.89  tff(c_272, plain, (![C_103, A_104, B_105]: (v2_funct_1(C_103) | ~v3_funct_2(C_103, A_104, B_105) | ~v1_funct_1(C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 14.20/6.89  tff(c_278, plain, (v2_funct_1('#skF_4') | ~v3_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_272])).
% 14.20/6.89  tff(c_290, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_278])).
% 14.20/6.89  tff(c_562, plain, (![A_147, B_148]: (v1_funct_2(k2_funct_2(A_147, B_148), A_147, A_147) | ~m1_subset_1(B_148, k1_zfmisc_1(k2_zfmisc_1(A_147, A_147))) | ~v3_funct_2(B_148, A_147, A_147) | ~v1_funct_2(B_148, A_147, A_147) | ~v1_funct_1(B_148))), inference(cnfTransformation, [status(thm)], [f_144])).
% 14.20/6.89  tff(c_566, plain, (v1_funct_2(k2_funct_2('#skF_3', '#skF_4'), '#skF_3', '#skF_3') | ~v3_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_562])).
% 14.20/6.89  tff(c_576, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_551, c_566])).
% 14.20/6.89  tff(c_44, plain, (![B_34, A_33, C_35]: (k1_xboole_0=B_34 | k1_relset_1(A_33, B_34, C_35)=A_33 | ~v1_funct_2(C_35, A_33, B_34) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 14.20/6.89  tff(c_737, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_3', '#skF_3', k2_funct_1('#skF_4'))='#skF_3' | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_716, c_44])).
% 14.20/6.89  tff(c_778, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_3', '#skF_3', k2_funct_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_576, c_737])).
% 14.20/6.89  tff(c_829, plain, (k1_relset_1('#skF_3', '#skF_3', k2_funct_1('#skF_4'))='#skF_3'), inference(splitLeft, [status(thm)], [c_778])).
% 14.20/6.89  tff(c_839, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_829, c_785])).
% 14.20/6.89  tff(c_16, plain, (![A_13]: (k1_relat_1(k2_funct_1(A_13))=k2_relat_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_62])).
% 14.20/6.89  tff(c_843, plain, (k2_relat_1('#skF_4')='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_839, c_16])).
% 14.20/6.89  tff(c_850, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_78, c_290, c_843])).
% 14.20/6.89  tff(c_185, plain, (![A_89, B_90, C_91]: (k2_relset_1(A_89, B_90, C_91)=k2_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 14.20/6.89  tff(c_201, plain, (k2_relset_1('#skF_3', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_185])).
% 14.20/6.89  tff(c_854, plain, (k2_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_850, c_201])).
% 14.20/6.89  tff(c_974, plain, (![A_173, C_174, B_175]: (k6_partfun1(A_173)=k5_relat_1(C_174, k2_funct_1(C_174)) | k1_xboole_0=B_175 | ~v2_funct_1(C_174) | k2_relset_1(A_173, B_175, C_174)!=B_175 | ~m1_subset_1(C_174, k1_zfmisc_1(k2_zfmisc_1(A_173, B_175))) | ~v1_funct_2(C_174, A_173, B_175) | ~v1_funct_1(C_174))), inference(cnfTransformation, [status(thm)], [f_184])).
% 14.20/6.89  tff(c_984, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_3') | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_3', '#skF_3', '#skF_4')!='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_974])).
% 14.20/6.89  tff(c_1002, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_854, c_290, c_984])).
% 14.20/6.89  tff(c_1007, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1002])).
% 14.20/6.89  tff(c_6, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.20/6.89  tff(c_134, plain, (![C_71, B_72, A_73]: (~v1_xboole_0(C_71) | ~m1_subset_1(B_72, k1_zfmisc_1(C_71)) | ~r2_hidden(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_52])).
% 14.20/6.89  tff(c_146, plain, (![A_3, A_73]: (~v1_xboole_0(A_3) | ~r2_hidden(A_73, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_134])).
% 14.20/6.89  tff(c_147, plain, (![A_73]: (~r2_hidden(A_73, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_146])).
% 14.20/6.89  tff(c_1031, plain, (![A_73]: (~r2_hidden(A_73, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1007, c_147])).
% 14.20/6.89  tff(c_1607, plain, (![B_215]: (r2_relset_1('#skF_3', '#skF_3', B_215, k6_partfun1('#skF_3')) | ~m1_subset_1(B_215, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))))), inference(resolution, [status(thm)], [c_1586, c_1031])).
% 14.20/6.89  tff(c_7125, plain, (r2_relset_1('#skF_3', '#skF_3', k5_relat_1('#skF_4', k2_funct_1('#skF_4')), k6_partfun1('#skF_3'))), inference(resolution, [status(thm)], [c_7054, c_1607])).
% 14.20/6.89  tff(c_7274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7030, c_7125])).
% 14.20/6.89  tff(c_7275, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_3')), inference(splitRight, [status(thm)], [c_1002])).
% 14.20/6.89  tff(c_13722, plain, (![B_750, A_751, B_749, E_748, A_752]: (k1_partfun1(A_752, B_749, A_751, A_751, E_748, k2_funct_2(A_751, B_750))=k5_relat_1(E_748, k2_funct_2(A_751, B_750)) | ~v1_funct_1(k2_funct_2(A_751, B_750)) | ~m1_subset_1(E_748, k1_zfmisc_1(k2_zfmisc_1(A_752, B_749))) | ~v1_funct_1(E_748) | ~m1_subset_1(B_750, k1_zfmisc_1(k2_zfmisc_1(A_751, A_751))) | ~v3_funct_2(B_750, A_751, A_751) | ~v1_funct_2(B_750, A_751, A_751) | ~v1_funct_1(B_750))), inference(resolution, [status(thm)], [c_50, c_859])).
% 14.20/6.89  tff(c_13758, plain, (![A_751, B_750]: (k1_partfun1('#skF_3', '#skF_3', A_751, A_751, '#skF_4', k2_funct_2(A_751, B_750))=k5_relat_1('#skF_4', k2_funct_2(A_751, B_750)) | ~v1_funct_1(k2_funct_2(A_751, B_750)) | ~v1_funct_1('#skF_4') | ~m1_subset_1(B_750, k1_zfmisc_1(k2_zfmisc_1(A_751, A_751))) | ~v3_funct_2(B_750, A_751, A_751) | ~v1_funct_2(B_750, A_751, A_751) | ~v1_funct_1(B_750))), inference(resolution, [status(thm)], [c_72, c_13722])).
% 14.20/6.89  tff(c_14342, plain, (![A_766, B_767]: (k1_partfun1('#skF_3', '#skF_3', A_766, A_766, '#skF_4', k2_funct_2(A_766, B_767))=k5_relat_1('#skF_4', k2_funct_2(A_766, B_767)) | ~v1_funct_1(k2_funct_2(A_766, B_767)) | ~m1_subset_1(B_767, k1_zfmisc_1(k2_zfmisc_1(A_766, A_766))) | ~v3_funct_2(B_767, A_766, A_766) | ~v1_funct_2(B_767, A_766, A_766) | ~v1_funct_1(B_767))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_13758])).
% 14.20/6.89  tff(c_14381, plain, (k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_4', k2_funct_2('#skF_3', '#skF_4'))=k5_relat_1('#skF_4', k2_funct_2('#skF_3', '#skF_4')) | ~v1_funct_1(k2_funct_2('#skF_3', '#skF_4')) | ~v3_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_14342])).
% 14.20/6.89  tff(c_14438, plain, (k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', '#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_554, c_551, c_7275, c_551, c_551, c_14381])).
% 14.20/6.89  tff(c_14443, plain, (~r2_relset_1('#skF_3', '#skF_3', k6_partfun1('#skF_3'), k6_partfun1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14438, c_555])).
% 14.20/6.89  tff(c_14448, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7627, c_14443])).
% 14.20/6.89  tff(c_14450, plain, (k1_relset_1('#skF_3', '#skF_3', k2_funct_1('#skF_4'))!='#skF_3'), inference(splitRight, [status(thm)], [c_778])).
% 14.20/6.89  tff(c_14693, plain, (k1_relat_1(k2_funct_1('#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_785, c_14450])).
% 14.20/6.89  tff(c_14449, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_778])).
% 14.20/6.89  tff(c_42, plain, (![B_34, C_35]: (k1_relset_1(k1_xboole_0, B_34, C_35)=k1_xboole_0 | ~v1_funct_2(C_35, k1_xboole_0, B_34) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_34))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 14.20/6.89  tff(c_705, plain, (![B_160]: (k1_relset_1(k1_xboole_0, k1_xboole_0, k2_funct_2(k1_xboole_0, B_160))=k1_xboole_0 | ~v1_funct_2(k2_funct_2(k1_xboole_0, B_160), k1_xboole_0, k1_xboole_0) | ~m1_subset_1(B_160, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, k1_xboole_0))) | ~v3_funct_2(B_160, k1_xboole_0, k1_xboole_0) | ~v1_funct_2(B_160, k1_xboole_0, k1_xboole_0) | ~v1_funct_1(B_160))), inference(resolution, [status(thm)], [c_635, c_42])).
% 14.20/6.89  tff(c_17252, plain, (![B_908]: (k1_relset_1('#skF_3', '#skF_3', k2_funct_2('#skF_3', B_908))='#skF_3' | ~v1_funct_2(k2_funct_2('#skF_3', B_908), '#skF_3', '#skF_3') | ~m1_subset_1(B_908, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v3_funct_2(B_908, '#skF_3', '#skF_3') | ~v1_funct_2(B_908, '#skF_3', '#skF_3') | ~v1_funct_1(B_908))), inference(demodulation, [status(thm), theory('equality')], [c_14449, c_14449, c_14449, c_14449, c_14449, c_14449, c_14449, c_14449, c_14449, c_14449, c_14449, c_14449, c_14449, c_705])).
% 14.20/6.89  tff(c_17295, plain, (k1_relset_1('#skF_3', '#skF_3', k2_funct_2('#skF_3', '#skF_4'))='#skF_3' | ~v1_funct_2(k2_funct_2('#skF_3', '#skF_4'), '#skF_3', '#skF_3') | ~v3_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_17252])).
% 14.20/6.89  tff(c_17330, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_576, c_551, c_785, c_551, c_17295])).
% 14.20/6.89  tff(c_17332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14693, c_17330])).
% 14.20/6.89  tff(c_17333, plain, (![A_3]: (~v1_xboole_0(A_3))), inference(splitRight, [status(thm)], [c_146])).
% 14.20/6.89  tff(c_108, plain, (![B_66, A_67]: (v1_xboole_0(B_66) | ~m1_subset_1(B_66, k1_zfmisc_1(A_67)) | ~v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.20/6.89  tff(c_125, plain, (![A_3]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(A_3))), inference(resolution, [status(thm)], [c_6, c_108])).
% 14.20/6.89  tff(c_126, plain, (![A_3]: (~v1_xboole_0(A_3))), inference(splitLeft, [status(thm)], [c_125])).
% 14.20/6.89  tff(c_2, plain, (![A_1]: (v1_xboole_0('#skF_1'(A_1)))), inference(cnfTransformation, [status(thm)], [f_30])).
% 14.20/6.89  tff(c_129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126, c_2])).
% 14.20/6.89  tff(c_130, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_125])).
% 14.20/6.89  tff(c_17338, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17333, c_130])).
% 14.20/6.89  tff(c_17339, plain, (~r2_relset_1('#skF_3', '#skF_3', k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', k2_funct_2('#skF_3', '#skF_4'), '#skF_4'), k6_partfun1('#skF_3'))), inference(splitRight, [status(thm)], [c_70])).
% 14.20/6.89  tff(c_17800, plain, (~r2_relset_1('#skF_3', '#skF_3', k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', k2_funct_1('#skF_4'), '#skF_4'), k6_partfun1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_17796, c_17339])).
% 14.20/6.89  tff(c_22311, plain, (~r2_relset_1('#skF_3', '#skF_3', k5_relat_1(k2_funct_1('#skF_4'), '#skF_4'), k6_partfun1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_21218, c_17800])).
% 14.20/6.89  tff(c_22315, plain, (m1_subset_1(k5_relat_1(k2_funct_1('#skF_4'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_21218, c_46])).
% 14.20/6.89  tff(c_22319, plain, (m1_subset_1(k5_relat_1(k2_funct_1('#skF_4'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_17799, c_18033, c_78, c_72, c_22315])).
% 14.20/6.89  tff(c_17867, plain, (![A_1006, B_1007, C_1008]: (r2_hidden('#skF_2'(A_1006, B_1007, C_1008), A_1006) | r2_relset_1(A_1006, A_1006, B_1007, C_1008) | ~m1_subset_1(C_1008, k1_zfmisc_1(k2_zfmisc_1(A_1006, A_1006))) | ~m1_subset_1(B_1007, k1_zfmisc_1(k2_zfmisc_1(A_1006, A_1006))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 14.20/6.89  tff(c_21723, plain, (![A_1206, B_1207]: (r2_hidden('#skF_2'(A_1206, B_1207, k6_partfun1(A_1206)), A_1206) | r2_relset_1(A_1206, A_1206, B_1207, k6_partfun1(A_1206)) | ~m1_subset_1(B_1207, k1_zfmisc_1(k2_zfmisc_1(A_1206, A_1206))))), inference(resolution, [status(thm)], [c_60, c_17867])).
% 14.20/6.89  tff(c_20450, plain, (![A_1137, B_1138]: (r2_relset_1(A_1137, A_1137, B_1138, B_1138) | ~m1_subset_1(B_1138, k1_zfmisc_1(k2_zfmisc_1(A_1137, A_1137))) | ~m1_subset_1(B_1138, k1_zfmisc_1(k2_zfmisc_1(A_1137, A_1137))))), inference(reflexivity, [status(thm), theory('equality')], [c_24])).
% 14.20/6.89  tff(c_20465, plain, (![A_44]: (r2_relset_1(A_44, A_44, k6_partfun1(A_44), k6_partfun1(A_44)) | ~m1_subset_1(k6_partfun1(A_44), k1_zfmisc_1(k2_zfmisc_1(A_44, A_44))))), inference(resolution, [status(thm)], [c_60, c_20450])).
% 14.20/6.89  tff(c_20490, plain, (![A_44]: (r2_relset_1(A_44, A_44, k6_partfun1(A_44), k6_partfun1(A_44)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_20465])).
% 14.20/6.89  tff(c_18488, plain, (![A_1051, B_1052, E_1053]: (k1_partfun1(A_1051, B_1052, '#skF_3', '#skF_3', E_1053, '#skF_4')=k5_relat_1(E_1053, '#skF_4') | ~m1_subset_1(E_1053, k1_zfmisc_1(k2_zfmisc_1(A_1051, B_1052))) | ~v1_funct_1(E_1053))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_18128])).
% 14.20/6.89  tff(c_18498, plain, (k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', k2_funct_1('#skF_4'), '#skF_4')=k5_relat_1(k2_funct_1('#skF_4'), '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_18033, c_18488])).
% 14.20/6.89  tff(c_18516, plain, (k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', k2_funct_1('#skF_4'), '#skF_4')=k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_17799, c_18498])).
% 14.20/6.90  tff(c_19650, plain, (~r2_relset_1('#skF_3', '#skF_3', k5_relat_1(k2_funct_1('#skF_4'), '#skF_4'), k6_partfun1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_18516, c_17800])).
% 14.20/6.90  tff(c_19654, plain, (m1_subset_1(k5_relat_1(k2_funct_1('#skF_4'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1(k2_funct_1('#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))) | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_18516, c_46])).
% 14.20/6.90  tff(c_19658, plain, (m1_subset_1(k5_relat_1(k2_funct_1('#skF_4'), '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_17799, c_18033, c_78, c_72, c_19654])).
% 14.20/6.90  tff(c_18908, plain, (![A_1070, B_1071]: (r2_hidden('#skF_2'(A_1070, B_1071, k6_partfun1(A_1070)), A_1070) | r2_relset_1(A_1070, A_1070, B_1071, k6_partfun1(A_1070)) | ~m1_subset_1(B_1071, k1_zfmisc_1(k2_zfmisc_1(A_1070, A_1070))))), inference(resolution, [status(thm)], [c_60, c_17867])).
% 14.20/6.90  tff(c_17342, plain, (![C_910, A_911, B_912]: (v1_relat_1(C_910) | ~m1_subset_1(C_910, k1_zfmisc_1(k2_zfmisc_1(A_911, B_912))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 14.20/6.90  tff(c_17358, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_17342])).
% 14.20/6.90  tff(c_17566, plain, (![C_958, A_959, B_960]: (v2_funct_1(C_958) | ~v3_funct_2(C_958, A_959, B_960) | ~v1_funct_1(C_958) | ~m1_subset_1(C_958, k1_zfmisc_1(k2_zfmisc_1(A_959, B_960))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 14.20/6.90  tff(c_17572, plain, (v2_funct_1('#skF_4') | ~v3_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_17566])).
% 14.20/6.90  tff(c_17584, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_17572])).
% 14.20/6.90  tff(c_18114, plain, (k1_relset_1('#skF_3', '#skF_3', k2_funct_1('#skF_4'))=k1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_18033, c_20])).
% 14.20/6.90  tff(c_17849, plain, (![A_1003, B_1004]: (v1_funct_2(k2_funct_2(A_1003, B_1004), A_1003, A_1003) | ~m1_subset_1(B_1004, k1_zfmisc_1(k2_zfmisc_1(A_1003, A_1003))) | ~v3_funct_2(B_1004, A_1003, A_1003) | ~v1_funct_2(B_1004, A_1003, A_1003) | ~v1_funct_1(B_1004))), inference(cnfTransformation, [status(thm)], [f_144])).
% 14.20/6.90  tff(c_17853, plain, (v1_funct_2(k2_funct_2('#skF_3', '#skF_4'), '#skF_3', '#skF_3') | ~v3_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_17849])).
% 14.20/6.90  tff(c_17863, plain, (v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_17796, c_17853])).
% 14.20/6.90  tff(c_18056, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_3', '#skF_3', k2_funct_1('#skF_4'))='#skF_3' | ~v1_funct_2(k2_funct_1('#skF_4'), '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_18033, c_44])).
% 14.20/6.90  tff(c_18104, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_3', '#skF_3', k2_funct_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_17863, c_18056])).
% 14.20/6.90  tff(c_18162, plain, (k1_xboole_0='#skF_3' | k1_relat_1(k2_funct_1('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18114, c_18104])).
% 14.20/6.90  tff(c_18163, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_3'), inference(splitLeft, [status(thm)], [c_18162])).
% 14.20/6.90  tff(c_18168, plain, (k2_relat_1('#skF_4')='#skF_3' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_18163, c_16])).
% 14.20/6.90  tff(c_18175, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_17358, c_78, c_17584, c_18168])).
% 14.20/6.90  tff(c_17475, plain, (![A_943, B_944, C_945]: (k2_relset_1(A_943, B_944, C_945)=k2_relat_1(C_945) | ~m1_subset_1(C_945, k1_zfmisc_1(k2_zfmisc_1(A_943, B_944))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 14.20/6.90  tff(c_17491, plain, (k2_relset_1('#skF_3', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_17475])).
% 14.20/6.90  tff(c_18179, plain, (![B_1030, C_1031, A_1032]: (k6_partfun1(B_1030)=k5_relat_1(k2_funct_1(C_1031), C_1031) | k1_xboole_0=B_1030 | ~v2_funct_1(C_1031) | k2_relset_1(A_1032, B_1030, C_1031)!=B_1030 | ~m1_subset_1(C_1031, k1_zfmisc_1(k2_zfmisc_1(A_1032, B_1030))) | ~v1_funct_2(C_1031, A_1032, B_1030) | ~v1_funct_1(C_1031))), inference(cnfTransformation, [status(thm)], [f_184])).
% 14.20/6.90  tff(c_18187, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_3') | k1_xboole_0='#skF_3' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_3', '#skF_3', '#skF_4')!='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_18179])).
% 14.20/6.90  tff(c_18202, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_3') | k1_xboole_0='#skF_3' | k2_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_17491, c_17584, c_18187])).
% 14.20/6.90  tff(c_18218, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_18175, c_18202])).
% 14.20/6.90  tff(c_18219, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_18218])).
% 14.20/6.90  tff(c_17401, plain, (![C_922, B_923, A_924]: (~v1_xboole_0(C_922) | ~m1_subset_1(B_923, k1_zfmisc_1(C_922)) | ~r2_hidden(A_924, B_923))), inference(cnfTransformation, [status(thm)], [f_52])).
% 14.20/6.90  tff(c_17413, plain, (![A_3, A_924]: (~v1_xboole_0(A_3) | ~r2_hidden(A_924, k1_xboole_0))), inference(resolution, [status(thm)], [c_6, c_17401])).
% 14.20/6.90  tff(c_17414, plain, (![A_924]: (~r2_hidden(A_924, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_17413])).
% 14.20/6.90  tff(c_18243, plain, (![A_924]: (~r2_hidden(A_924, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_18219, c_17414])).
% 14.20/6.90  tff(c_19858, plain, (![B_1120]: (r2_relset_1('#skF_3', '#skF_3', B_1120, k6_partfun1('#skF_3')) | ~m1_subset_1(B_1120, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))))), inference(resolution, [status(thm)], [c_18908, c_18243])).
% 14.20/6.90  tff(c_19861, plain, (r2_relset_1('#skF_3', '#skF_3', k5_relat_1(k2_funct_1('#skF_4'), '#skF_4'), k6_partfun1('#skF_3'))), inference(resolution, [status(thm)], [c_19658, c_19858])).
% 14.20/6.90  tff(c_19903, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19650, c_19861])).
% 14.20/6.90  tff(c_19904, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_3')), inference(splitRight, [status(thm)], [c_18218])).
% 14.20/6.90  tff(c_19906, plain, (![A_1121, B_1122, E_1123]: (k1_partfun1(A_1121, B_1122, '#skF_3', '#skF_3', E_1123, '#skF_4')=k5_relat_1(E_1123, '#skF_4') | ~m1_subset_1(E_1123, k1_zfmisc_1(k2_zfmisc_1(A_1121, B_1122))) | ~v1_funct_1(E_1123))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_18128])).
% 14.20/6.90  tff(c_19909, plain, (k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', k2_funct_1('#skF_4'), '#skF_4')=k5_relat_1(k2_funct_1('#skF_4'), '#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_18033, c_19906])).
% 14.20/6.90  tff(c_19929, plain, (k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', k2_funct_1('#skF_4'), '#skF_4')=k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_17799, c_19909])).
% 14.20/6.90  tff(c_20982, plain, (k1_partfun1('#skF_3', '#skF_3', '#skF_3', '#skF_3', k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_19904, c_19929])).
% 14.20/6.90  tff(c_20984, plain, (~r2_relset_1('#skF_3', '#skF_3', k6_partfun1('#skF_3'), k6_partfun1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_20982, c_17800])).
% 14.20/6.90  tff(c_20987, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20490, c_20984])).
% 14.20/6.90  tff(c_20988, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_18162])).
% 14.20/6.90  tff(c_21012, plain, (![A_924]: (~r2_hidden(A_924, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_20988, c_17414])).
% 14.20/6.90  tff(c_22657, plain, (![B_1254]: (r2_relset_1('#skF_3', '#skF_3', B_1254, k6_partfun1('#skF_3')) | ~m1_subset_1(B_1254, k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3'))))), inference(resolution, [status(thm)], [c_21723, c_21012])).
% 14.20/6.90  tff(c_22660, plain, (r2_relset_1('#skF_3', '#skF_3', k5_relat_1(k2_funct_1('#skF_4'), '#skF_4'), k6_partfun1('#skF_3'))), inference(resolution, [status(thm)], [c_22319, c_22657])).
% 14.20/6.90  tff(c_22702, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22311, c_22660])).
% 14.20/6.90  tff(c_22703, plain, (![A_3]: (~v1_xboole_0(A_3))), inference(splitRight, [status(thm)], [c_17413])).
% 14.20/6.90  tff(c_17363, plain, (![B_916, A_917]: (v1_xboole_0(B_916) | ~m1_subset_1(B_916, k1_zfmisc_1(A_917)) | ~v1_xboole_0(A_917))), inference(cnfTransformation, [status(thm)], [f_39])).
% 14.20/6.90  tff(c_17380, plain, (![A_3]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(A_3))), inference(resolution, [status(thm)], [c_6, c_17363])).
% 14.20/6.90  tff(c_17381, plain, (![A_3]: (~v1_xboole_0(A_3))), inference(splitLeft, [status(thm)], [c_17380])).
% 14.20/6.90  tff(c_17397, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17381, c_2])).
% 14.20/6.90  tff(c_17398, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_17380])).
% 14.20/6.90  tff(c_22708, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22703, c_17398])).
% 14.20/6.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.20/6.90  
% 14.20/6.90  Inference rules
% 14.20/6.90  ----------------------
% 14.20/6.90  #Ref     : 6
% 14.20/6.90  #Sup     : 4691
% 14.20/6.90  #Fact    : 0
% 14.20/6.90  #Define  : 0
% 14.20/6.90  #Split   : 87
% 14.20/6.90  #Chain   : 0
% 14.20/6.90  #Close   : 0
% 14.20/6.90  
% 14.20/6.90  Ordering : KBO
% 14.20/6.90  
% 14.20/6.90  Simplification rules
% 14.20/6.90  ----------------------
% 14.20/6.90  #Subsume      : 618
% 14.20/6.90  #Demod        : 6316
% 14.20/6.90  #Tautology    : 962
% 14.20/6.90  #SimpNegUnit  : 232
% 14.20/6.90  #BackRed      : 273
% 14.20/6.90  
% 14.20/6.90  #Partial instantiations: 0
% 14.20/6.90  #Strategies tried      : 1
% 14.20/6.90  
% 14.20/6.90  Timing (in seconds)
% 14.20/6.90  ----------------------
% 14.49/6.90  Preprocessing        : 0.37
% 14.49/6.90  Parsing              : 0.19
% 14.49/6.90  CNF conversion       : 0.03
% 14.49/6.90  Main loop            : 5.69
% 14.49/6.90  Inferencing          : 1.51
% 14.49/6.90  Reduction            : 2.69
% 14.49/6.90  Demodulation         : 2.11
% 14.49/6.90  BG Simplification    : 0.10
% 14.49/6.90  Subsumption          : 1.08
% 14.49/6.90  Abstraction          : 0.15
% 14.49/6.90  MUC search           : 0.00
% 14.49/6.90  Cooper               : 0.00
% 14.49/6.90  Total                : 6.12
% 14.49/6.90  Index Insertion      : 0.00
% 14.49/6.90  Index Deletion       : 0.00
% 14.49/6.90  Index Matching       : 0.00
% 14.49/6.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
