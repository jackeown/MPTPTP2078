%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:23:29 EST 2020

% Result     : Theorem 7.41s
% Output     : CNFRefutation 7.73s
% Verified   : 
% Statistics : Number of formulae       :  200 (76894 expanded)
%              Number of leaves         :   49 (27264 expanded)
%              Depth                    :   33
%              Number of atoms          :  439 (229856 expanded)
%              Number of equality atoms :   95 (48692 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k4_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tops_2,type,(
    k2_tops_2: ( $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(r2_funct_2,type,(
    r2_funct_2: ( $i * $i * $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_196,negated_conjecture,(
    ~ ! [A] :
        ( l1_struct_0(A)
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & l1_struct_0(B) )
           => ! [C] :
                ( ( v1_funct_1(C)
                  & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                  & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
               => ( ( k2_relset_1(u1_struct_0(A),u1_struct_0(B),C) = k2_struct_0(B)
                    & v2_funct_1(C) )
                 => r2_funct_2(u1_struct_0(A),u1_struct_0(B),k2_tops_2(u1_struct_0(B),u1_struct_0(A),k2_tops_2(u1_struct_0(A),u1_struct_0(B),C)),C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

tff(f_154,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_162,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_120,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_112,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_134,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_funct_2(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(k2_funct_1(A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A))
        & v2_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_76,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v2_funct_1(A)
            & r1_tarski(B,k1_relat_1(A)) )
         => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_150,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_174,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => k2_tops_2(A,B,C) = k2_funct_1(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

tff(c_74,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_78,plain,(
    ! [A_45] :
      ( u1_struct_0(A_45) = k2_struct_0(A_45)
      | ~ l1_struct_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_86,plain,(
    u1_struct_0('#skF_1') = k2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_78])).

tff(c_70,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_85,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_78])).

tff(c_64,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_145,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_85,c_64])).

tff(c_153,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_157,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_145,c_153])).

tff(c_68,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_60,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_1960,plain,(
    ! [A_139,B_140,C_141] :
      ( k2_relset_1(A_139,B_140,C_141) = k2_relat_1(C_141)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_139,B_140))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1964,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_145,c_1960])).

tff(c_62,plain,(
    k2_relset_1(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_140,plain,(
    k2_relset_1(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_85,c_62])).

tff(c_1965,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1964,c_140])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_115,plain,(
    ! [A_48] :
      ( ~ v1_xboole_0(u1_struct_0(A_48))
      | ~ l1_struct_0(A_48)
      | v2_struct_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_121,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_115])).

tff(c_125,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_2'))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_121])).

tff(c_126,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_125])).

tff(c_1974,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1965,c_126])).

tff(c_167,plain,(
    ! [C_61,A_62,B_63] :
      ( v4_relat_1(C_61,A_62)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_171,plain,(
    v4_relat_1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_145,c_167])).

tff(c_1946,plain,(
    ! [B_137,A_138] :
      ( k1_relat_1(B_137) = A_138
      | ~ v1_partfun1(B_137,A_138)
      | ~ v4_relat_1(B_137,A_138)
      | ~ v1_relat_1(B_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1952,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_171,c_1946])).

tff(c_1958,plain,
    ( k2_struct_0('#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_1952])).

tff(c_1959,plain,(
    ~ v1_partfun1('#skF_3',k2_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1958])).

tff(c_66,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_91,plain,(
    v1_funct_2('#skF_3',u1_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_66])).

tff(c_92,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_91])).

tff(c_1975,plain,(
    v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1965,c_92])).

tff(c_1973,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1965,c_145])).

tff(c_36,plain,(
    ! [C_24,A_21,B_22] :
      ( v1_partfun1(C_24,A_21)
      | ~ v1_funct_2(C_24,A_21,B_22)
      | ~ v1_funct_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | v1_xboole_0(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1994,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | ~ v1_funct_2('#skF_3',k2_struct_0('#skF_1'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1973,c_36])).

tff(c_2009,plain,
    ( v1_partfun1('#skF_3',k2_struct_0('#skF_1'))
    | v1_xboole_0(k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1975,c_1994])).

tff(c_2011,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1974,c_1959,c_2009])).

tff(c_2012,plain,(
    k2_struct_0('#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1958])).

tff(c_2016,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2012,c_145])).

tff(c_34,plain,(
    ! [A_18,B_19,C_20] :
      ( k2_relset_1(A_18,B_19,C_20) = k2_relat_1(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_2061,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2016,c_34])).

tff(c_2017,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3') = k2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2012,c_140])).

tff(c_2072,plain,(
    k2_struct_0('#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2061,c_2017])).

tff(c_2019,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2012,c_92])).

tff(c_2080,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2072,c_2019])).

tff(c_2079,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2072,c_2016])).

tff(c_2803,plain,(
    ! [A_171,B_172,C_173,D_174] :
      ( r2_funct_2(A_171,B_172,C_173,C_173)
      | ~ m1_subset_1(D_174,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172)))
      | ~ v1_funct_2(D_174,A_171,B_172)
      | ~ v1_funct_1(D_174)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(A_171,B_172)))
      | ~ v1_funct_2(C_173,A_171,B_172)
      | ~ v1_funct_1(C_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_2807,plain,(
    ! [C_173] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_173,C_173)
      | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_173,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_173) ) ),
    inference(resolution,[status(thm)],[c_2079,c_2803])).

tff(c_2864,plain,(
    ! [C_177] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_177,C_177)
      | ~ m1_subset_1(C_177,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_177,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2080,c_2807])).

tff(c_2869,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2079,c_2864])).

tff(c_2873,plain,(
    r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2080,c_2869])).

tff(c_26,plain,(
    ! [A_11] :
      ( k2_funct_1(k2_funct_1(A_11)) = A_11
      | ~ v2_funct_1(A_11)
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_20,plain,(
    ! [A_7] :
      ( v1_funct_1(k2_funct_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_198,plain,(
    ! [A_65] :
      ( k4_relat_1(A_65) = k2_funct_1(A_65)
      | ~ v2_funct_1(A_65)
      | ~ v1_funct_1(A_65)
      | ~ v1_relat_1(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_204,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_198])).

tff(c_208,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_68,c_204])).

tff(c_8,plain,(
    ! [A_3] :
      ( v1_relat_1(k4_relat_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_218,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_8])).

tff(c_226,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_218])).

tff(c_14,plain,(
    ! [A_5] :
      ( k1_relat_1(k4_relat_1(A_5)) = k2_relat_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_215,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_14])).

tff(c_224,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_215])).

tff(c_12,plain,(
    ! [A_5] :
      ( k2_relat_1(k4_relat_1(A_5)) = k1_relat_1(A_5)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_212,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_12])).

tff(c_222,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_212])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_4] :
      ( k9_relat_1(A_4,k1_relat_1(A_4)) = k2_relat_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2098,plain,(
    ! [A_148,B_149] :
      ( k9_relat_1(k2_funct_1(A_148),k9_relat_1(A_148,B_149)) = B_149
      | ~ r1_tarski(B_149,k1_relat_1(A_148))
      | ~ v2_funct_1(A_148)
      | ~ v1_funct_1(A_148)
      | ~ v1_relat_1(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2119,plain,(
    ! [A_4] :
      ( k9_relat_1(k2_funct_1(A_4),k2_relat_1(A_4)) = k1_relat_1(A_4)
      | ~ r1_tarski(k1_relat_1(A_4),k1_relat_1(A_4))
      | ~ v2_funct_1(A_4)
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_2098])).

tff(c_2175,plain,(
    ! [A_151] :
      ( k9_relat_1(k2_funct_1(A_151),k2_relat_1(A_151)) = k1_relat_1(A_151)
      | ~ v2_funct_1(A_151)
      | ~ v1_funct_1(A_151)
      | ~ v1_relat_1(A_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2119])).

tff(c_2193,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_2175])).

tff(c_2209,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_224,c_2193])).

tff(c_2237,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2209])).

tff(c_2240,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_2237])).

tff(c_2244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_68,c_60,c_2240])).

tff(c_2246,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2209])).

tff(c_2077,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2072,c_2061])).

tff(c_2388,plain,(
    ! [C_158,B_159,A_160] :
      ( v1_funct_2(k2_funct_1(C_158),B_159,A_160)
      | k2_relset_1(A_160,B_159,C_158) != B_159
      | ~ v2_funct_1(C_158)
      | ~ m1_subset_1(C_158,k1_zfmisc_1(k2_zfmisc_1(A_160,B_159)))
      | ~ v1_funct_2(C_158,A_160,B_159)
      | ~ v1_funct_1(C_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_2391,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2079,c_2388])).

tff(c_2394,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2080,c_60,c_2077,c_2391])).

tff(c_2627,plain,(
    ! [C_166,B_167,A_168] :
      ( m1_subset_1(k2_funct_1(C_166),k1_zfmisc_1(k2_zfmisc_1(B_167,A_168)))
      | k2_relset_1(A_168,B_167,C_166) != B_167
      | ~ v2_funct_1(C_166)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_168,B_167)))
      | ~ v1_funct_2(C_166,A_168,B_167)
      | ~ v1_funct_1(C_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_4604,plain,(
    ! [B_220,A_221,C_222] :
      ( k2_relset_1(B_220,A_221,k2_funct_1(C_222)) = k2_relat_1(k2_funct_1(C_222))
      | k2_relset_1(A_221,B_220,C_222) != B_220
      | ~ v2_funct_1(C_222)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(A_221,B_220)))
      | ~ v1_funct_2(C_222,A_221,B_220)
      | ~ v1_funct_1(C_222) ) ),
    inference(resolution,[status(thm)],[c_2627,c_34])).

tff(c_4610,plain,
    ( k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_relat_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2079,c_4604])).

tff(c_4614,plain,(
    k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2080,c_60,c_2077,c_222,c_4610])).

tff(c_18,plain,(
    ! [A_7] :
      ( v2_funct_1(k2_funct_1(A_7))
      | ~ v2_funct_1(A_7)
      | ~ v1_funct_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2245,plain,
    ( ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2209])).

tff(c_2247,plain,(
    ~ v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2245])).

tff(c_2250,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_2247])).

tff(c_2254,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_68,c_60,c_2250])).

tff(c_2256,plain,(
    v2_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2245])).

tff(c_46,plain,(
    ! [C_33,B_32,A_31] :
      ( m1_subset_1(k2_funct_1(C_33),k1_zfmisc_1(k2_zfmisc_1(B_32,A_31)))
      | k2_relset_1(A_31,B_32,C_33) != B_32
      | ~ v2_funct_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ v1_funct_2(C_33,A_31,B_32)
      | ~ v1_funct_1(C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_16,plain,(
    ! [A_6] :
      ( k4_relat_1(A_6) = k2_funct_1(A_6)
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2259,plain,
    ( k4_relat_1(k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2256,c_16])).

tff(c_2262,plain,(
    k4_relat_1(k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_2246,c_2259])).

tff(c_127,plain,(
    ! [A_49] :
      ( k9_relat_1(A_49,k1_relat_1(A_49)) = k2_relat_1(A_49)
      | ~ v1_relat_1(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2150,plain,(
    ! [A_150] :
      ( k9_relat_1(k4_relat_1(A_150),k2_relat_1(A_150)) = k2_relat_1(k4_relat_1(A_150))
      | ~ v1_relat_1(k4_relat_1(A_150))
      | ~ v1_relat_1(A_150) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_127])).

tff(c_2162,plain,
    ( k9_relat_1(k4_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = k2_relat_1(k4_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k4_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_2150])).

tff(c_2172,plain,
    ( k9_relat_1(k4_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = k2_relat_1(k4_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k4_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_2162])).

tff(c_2210,plain,(
    ~ v1_relat_1(k4_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2172])).

tff(c_2213,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_2210])).

tff(c_2217,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_2213])).

tff(c_2219,plain,(
    v1_relat_1(k4_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2172])).

tff(c_2264,plain,(
    v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2262,c_2219])).

tff(c_2274,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2262,c_14])).

tff(c_2285,plain,(
    k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_222,c_2274])).

tff(c_2255,plain,(
    k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2245])).

tff(c_24,plain,(
    ! [A_8,B_10] :
      ( k9_relat_1(k2_funct_1(A_8),k9_relat_1(A_8,B_10)) = B_10
      | ~ r1_tarski(B_10,k1_relat_1(A_8))
      | ~ v2_funct_1(A_8)
      | ~ v1_funct_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2345,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))),k2_relat_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2255,c_24])).

tff(c_2352,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))),k2_relat_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2264,c_6,c_2285,c_2345])).

tff(c_2463,plain,(
    ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2352])).

tff(c_2466,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2463])).

tff(c_2472,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_68,c_60,c_68,c_2466])).

tff(c_2474,plain,(
    v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2352])).

tff(c_2271,plain,
    ( k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2262,c_12])).

tff(c_2283,plain,(
    k2_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_224,c_2271])).

tff(c_2218,plain,(
    k9_relat_1(k4_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = k2_relat_1(k4_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2172])).

tff(c_2231,plain,
    ( k9_relat_1(k2_funct_1(k4_relat_1(k2_funct_1('#skF_3'))),k2_relat_1(k4_relat_1(k2_funct_1('#skF_3')))) = k1_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(k4_relat_1(k2_funct_1('#skF_3'))))
    | ~ v2_funct_1(k4_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k4_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k4_relat_1(k2_funct_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2218,c_24])).

tff(c_2235,plain,
    ( k9_relat_1(k2_funct_1(k4_relat_1(k2_funct_1('#skF_3'))),k2_relat_1(k4_relat_1(k2_funct_1('#skF_3')))) = k1_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(k4_relat_1(k2_funct_1('#skF_3'))))
    | ~ v2_funct_1(k4_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k4_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2219,c_2231])).

tff(c_2493,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))),k2_relat_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2474,c_2262,c_2262,c_6,c_2285,c_2262,c_2283,c_2262,c_2262,c_2235])).

tff(c_2494,plain,(
    ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_2493])).

tff(c_2497,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2494])).

tff(c_2503,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_68,c_60,c_60,c_2497])).

tff(c_2505,plain,(
    v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_2493])).

tff(c_2508,plain,
    ( k4_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_2505,c_16])).

tff(c_2514,plain,(
    k4_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2264,c_2474,c_2508])).

tff(c_2542,plain,
    ( k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k4_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2514])).

tff(c_2560,plain,(
    k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_68,c_60,c_208,c_2542])).

tff(c_6503,plain,(
    ! [A_252,B_253,A_254] :
      ( m1_subset_1(A_252,k1_zfmisc_1(k2_zfmisc_1(B_253,A_254)))
      | k2_relset_1(A_254,B_253,k2_funct_1(A_252)) != B_253
      | ~ v2_funct_1(k2_funct_1(A_252))
      | ~ m1_subset_1(k2_funct_1(A_252),k1_zfmisc_1(k2_zfmisc_1(A_254,B_253)))
      | ~ v1_funct_2(k2_funct_1(A_252),A_254,B_253)
      | ~ v1_funct_1(k2_funct_1(A_252))
      | ~ v2_funct_1(A_252)
      | ~ v1_funct_1(A_252)
      | ~ v1_relat_1(A_252) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_2627])).

tff(c_6512,plain,(
    ! [B_253,A_254] :
      ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(B_253,A_254)))
      | k2_relset_1(A_254,B_253,k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) != B_253
      | ~ v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
      | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(A_254,B_253)))
      | ~ v1_funct_2(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))),A_254,B_253)
      | ~ v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))
      | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
      | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2560,c_6503])).

tff(c_6519,plain,(
    ! [B_255,A_256] :
      ( m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')),k1_zfmisc_1(k2_zfmisc_1(B_255,A_256)))
      | k2_relset_1(A_256,B_255,k2_funct_1('#skF_3')) != B_255
      | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(A_256,B_255)))
      | ~ v1_funct_2(k2_funct_1('#skF_3'),A_256,B_255) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2264,c_2474,c_2505,c_2246,c_2560,c_2560,c_2256,c_2560,c_2560,c_6512])).

tff(c_2811,plain,(
    ! [C_173] :
      ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),C_173,C_173)
      | ~ m1_subset_1(C_173,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
      | ~ v1_funct_2(C_173,k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
      | ~ v1_funct_1(C_173) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2080,c_2807])).

tff(c_6546,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6519,c_2811])).

tff(c_6602,plain,
    ( r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),k2_funct_1(k2_funct_1('#skF_3')))
    | ~ v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2394,c_4614,c_2474,c_6546])).

tff(c_6642,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(splitLeft,[status(thm)],[c_6602])).

tff(c_6645,plain,
    ( k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))))
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_6642])).

tff(c_6649,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2080,c_2079,c_60,c_2077,c_6645])).

tff(c_6651,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3')))) ),
    inference(splitRight,[status(thm)],[c_6602])).

tff(c_56,plain,(
    ! [A_36,B_37,C_38] :
      ( k2_tops_2(A_36,B_37,C_38) = k2_funct_1(C_38)
      | ~ v2_funct_1(C_38)
      | k2_relset_1(A_36,B_37,C_38) != B_37
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_funct_2(C_38,A_36,B_37)
      | ~ v1_funct_1(C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_6684,plain,
    ( k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_2(k2_funct_1('#skF_3'),k2_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6651,c_56])).

tff(c_6742,plain,(
    k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')) = k2_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2246,c_2394,c_4614,c_2256,c_6684])).

tff(c_2475,plain,(
    ! [A_163,B_164,C_165] :
      ( k2_tops_2(A_163,B_164,C_165) = k2_funct_1(C_165)
      | ~ v2_funct_1(C_165)
      | k2_relset_1(A_163,B_164,C_165) != B_164
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_163,B_164)))
      | ~ v1_funct_2(C_165,A_163,B_164)
      | ~ v1_funct_1(C_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_2478,plain,
    ( k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2079,c_2475])).

tff(c_2481,plain,(
    k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2080,c_2077,c_60,c_2478])).

tff(c_58,plain,(
    ~ r2_funct_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),k2_tops_2(u1_struct_0('#skF_2'),u1_struct_0('#skF_1'),k2_tops_2(u1_struct_0('#skF_1'),u1_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_196])).

tff(c_166,plain,(
    ~ r2_funct_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k2_struct_0('#skF_1'),k2_tops_2(k2_struct_0('#skF_1'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_86,c_86,c_85,c_85,c_85,c_58])).

tff(c_2015,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),k2_tops_2(k2_struct_0('#skF_2'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_struct_0('#skF_2'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2012,c_2012,c_2012,c_166])).

tff(c_2078,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_tops_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2072,c_2072,c_2072,c_2015])).

tff(c_2487,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_tops_2(k2_relat_1('#skF_3'),k1_relat_1('#skF_3'),k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2481,c_2078])).

tff(c_6804,plain,(
    ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),k2_funct_1(k2_funct_1('#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6742,c_2487])).

tff(c_6811,plain,
    ( ~ r2_funct_2(k1_relat_1('#skF_3'),k2_relat_1('#skF_3'),'#skF_3','#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_6804])).

tff(c_6814,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_68,c_60,c_2873,c_6811])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:57:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.41/2.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.41/2.60  
% 7.41/2.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.41/2.60  %$ r2_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_struct_0 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > l1_struct_0 > k2_tops_2 > k2_relset_1 > k9_relat_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k4_relat_1 > k2_struct_0 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 7.41/2.60  
% 7.41/2.60  %Foreground sorts:
% 7.41/2.60  
% 7.41/2.60  
% 7.41/2.60  %Background operators:
% 7.41/2.60  
% 7.41/2.60  
% 7.41/2.60  %Foreground operators:
% 7.41/2.60  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.41/2.60  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.41/2.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.41/2.60  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 7.41/2.60  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.41/2.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.41/2.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.41/2.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.41/2.60  tff(k2_tops_2, type, k2_tops_2: ($i * $i * $i) > $i).
% 7.41/2.60  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.41/2.60  tff('#skF_2', type, '#skF_2': $i).
% 7.41/2.60  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.41/2.60  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.41/2.60  tff('#skF_3', type, '#skF_3': $i).
% 7.41/2.60  tff('#skF_1', type, '#skF_1': $i).
% 7.41/2.60  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.41/2.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.41/2.60  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 7.41/2.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.41/2.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.41/2.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.41/2.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.41/2.60  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.41/2.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.41/2.60  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 7.41/2.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.41/2.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.41/2.60  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 7.41/2.60  tff(r2_funct_2, type, r2_funct_2: ($i * $i * $i * $i) > $o).
% 7.41/2.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.41/2.60  
% 7.73/2.63  tff(f_196, negated_conjecture, ~(![A]: (l1_struct_0(A) => (![B]: ((~v2_struct_0(B) & l1_struct_0(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (((k2_relset_1(u1_struct_0(A), u1_struct_0(B), C) = k2_struct_0(B)) & v2_funct_1(C)) => r2_funct_2(u1_struct_0(A), u1_struct_0(B), k2_tops_2(u1_struct_0(B), u1_struct_0(A), k2_tops_2(u1_struct_0(A), u1_struct_0(B), C)), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tops_2)).
% 7.73/2.63  tff(f_154, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 7.73/2.63  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.73/2.63  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.73/2.63  tff(f_162, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 7.73/2.63  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.73/2.63  tff(f_120, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 7.73/2.63  tff(f_112, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 7.73/2.63  tff(f_134, axiom, (![A, B, C, D]: ((((((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(D)) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_funct_2(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_funct_2)).
% 7.73/2.63  tff(f_84, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(k2_funct_1(A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_1)).
% 7.73/2.63  tff(f_65, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => ((v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))) & v2_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_funct_1)).
% 7.73/2.63  tff(f_53, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 7.73/2.63  tff(f_35, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 7.73/2.63  tff(f_45, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 7.73/2.63  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.73/2.63  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 7.73/2.63  tff(f_76, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t177_funct_1)).
% 7.73/2.63  tff(f_150, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 7.73/2.63  tff(f_174, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => (k2_tops_2(A, B, C) = k2_funct_1(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tops_2)).
% 7.73/2.63  tff(c_74, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_196])).
% 7.73/2.63  tff(c_78, plain, (![A_45]: (u1_struct_0(A_45)=k2_struct_0(A_45) | ~l1_struct_0(A_45))), inference(cnfTransformation, [status(thm)], [f_154])).
% 7.73/2.63  tff(c_86, plain, (u1_struct_0('#skF_1')=k2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_74, c_78])).
% 7.73/2.63  tff(c_70, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_196])).
% 7.73/2.63  tff(c_85, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_70, c_78])).
% 7.73/2.63  tff(c_64, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_196])).
% 7.73/2.63  tff(c_145, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_85, c_64])).
% 7.73/2.63  tff(c_153, plain, (![C_52, A_53, B_54]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.73/2.63  tff(c_157, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_145, c_153])).
% 7.73/2.63  tff(c_68, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_196])).
% 7.73/2.63  tff(c_60, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_196])).
% 7.73/2.63  tff(c_1960, plain, (![A_139, B_140, C_141]: (k2_relset_1(A_139, B_140, C_141)=k2_relat_1(C_141) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_139, B_140))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.73/2.63  tff(c_1964, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_145, c_1960])).
% 7.73/2.63  tff(c_62, plain, (k2_relset_1(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_196])).
% 7.73/2.63  tff(c_140, plain, (k2_relset_1(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_85, c_62])).
% 7.73/2.63  tff(c_1965, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1964, c_140])).
% 7.73/2.63  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_196])).
% 7.73/2.63  tff(c_115, plain, (![A_48]: (~v1_xboole_0(u1_struct_0(A_48)) | ~l1_struct_0(A_48) | v2_struct_0(A_48))), inference(cnfTransformation, [status(thm)], [f_162])).
% 7.73/2.63  tff(c_121, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_85, c_115])).
% 7.73/2.63  tff(c_125, plain, (~v1_xboole_0(k2_struct_0('#skF_2')) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_121])).
% 7.73/2.63  tff(c_126, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_72, c_125])).
% 7.73/2.63  tff(c_1974, plain, (~v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1965, c_126])).
% 7.73/2.63  tff(c_167, plain, (![C_61, A_62, B_63]: (v4_relat_1(C_61, A_62) | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.73/2.63  tff(c_171, plain, (v4_relat_1('#skF_3', k2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_145, c_167])).
% 7.73/2.63  tff(c_1946, plain, (![B_137, A_138]: (k1_relat_1(B_137)=A_138 | ~v1_partfun1(B_137, A_138) | ~v4_relat_1(B_137, A_138) | ~v1_relat_1(B_137))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.73/2.63  tff(c_1952, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_171, c_1946])).
% 7.73/2.63  tff(c_1958, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3') | ~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_1952])).
% 7.73/2.63  tff(c_1959, plain, (~v1_partfun1('#skF_3', k2_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_1958])).
% 7.73/2.63  tff(c_66, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_196])).
% 7.73/2.63  tff(c_91, plain, (v1_funct_2('#skF_3', u1_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_66])).
% 7.73/2.63  tff(c_92, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_91])).
% 7.73/2.63  tff(c_1975, plain, (v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1965, c_92])).
% 7.73/2.63  tff(c_1973, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_1'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_1965, c_145])).
% 7.73/2.63  tff(c_36, plain, (![C_24, A_21, B_22]: (v1_partfun1(C_24, A_21) | ~v1_funct_2(C_24, A_21, B_22) | ~v1_funct_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | v1_xboole_0(B_22))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.73/2.63  tff(c_1994, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | ~v1_funct_2('#skF_3', k2_struct_0('#skF_1'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | v1_xboole_0(k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1973, c_36])).
% 7.73/2.63  tff(c_2009, plain, (v1_partfun1('#skF_3', k2_struct_0('#skF_1')) | v1_xboole_0(k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1975, c_1994])).
% 7.73/2.63  tff(c_2011, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1974, c_1959, c_2009])).
% 7.73/2.63  tff(c_2012, plain, (k2_struct_0('#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_1958])).
% 7.73/2.63  tff(c_2016, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_2012, c_145])).
% 7.73/2.63  tff(c_34, plain, (![A_18, B_19, C_20]: (k2_relset_1(A_18, B_19, C_20)=k2_relat_1(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.73/2.63  tff(c_2061, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2016, c_34])).
% 7.73/2.63  tff(c_2017, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')=k2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2012, c_140])).
% 7.73/2.63  tff(c_2072, plain, (k2_struct_0('#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2061, c_2017])).
% 7.73/2.63  tff(c_2019, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2012, c_92])).
% 7.73/2.63  tff(c_2080, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2072, c_2019])).
% 7.73/2.63  tff(c_2079, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_2072, c_2016])).
% 7.73/2.63  tff(c_2803, plain, (![A_171, B_172, C_173, D_174]: (r2_funct_2(A_171, B_172, C_173, C_173) | ~m1_subset_1(D_174, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))) | ~v1_funct_2(D_174, A_171, B_172) | ~v1_funct_1(D_174) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(A_171, B_172))) | ~v1_funct_2(C_173, A_171, B_172) | ~v1_funct_1(C_173))), inference(cnfTransformation, [status(thm)], [f_134])).
% 7.73/2.63  tff(c_2807, plain, (![C_173]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_173, C_173) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_173, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_173))), inference(resolution, [status(thm)], [c_2079, c_2803])).
% 7.73/2.63  tff(c_2864, plain, (![C_177]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_177, C_177) | ~m1_subset_1(C_177, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_177, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_177))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2080, c_2807])).
% 7.73/2.63  tff(c_2869, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2079, c_2864])).
% 7.73/2.63  tff(c_2873, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2080, c_2869])).
% 7.73/2.63  tff(c_26, plain, (![A_11]: (k2_funct_1(k2_funct_1(A_11))=A_11 | ~v2_funct_1(A_11) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.73/2.63  tff(c_20, plain, (![A_7]: (v1_funct_1(k2_funct_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.73/2.63  tff(c_198, plain, (![A_65]: (k4_relat_1(A_65)=k2_funct_1(A_65) | ~v2_funct_1(A_65) | ~v1_funct_1(A_65) | ~v1_relat_1(A_65))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.73/2.63  tff(c_204, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_198])).
% 7.73/2.63  tff(c_208, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_157, c_68, c_204])).
% 7.73/2.63  tff(c_8, plain, (![A_3]: (v1_relat_1(k4_relat_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.73/2.63  tff(c_218, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_208, c_8])).
% 7.73/2.63  tff(c_226, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_218])).
% 7.73/2.63  tff(c_14, plain, (![A_5]: (k1_relat_1(k4_relat_1(A_5))=k2_relat_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.73/2.63  tff(c_215, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_208, c_14])).
% 7.73/2.63  tff(c_224, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_157, c_215])).
% 7.73/2.63  tff(c_12, plain, (![A_5]: (k2_relat_1(k4_relat_1(A_5))=k1_relat_1(A_5) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.73/2.63  tff(c_212, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_208, c_12])).
% 7.73/2.63  tff(c_222, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_157, c_212])).
% 7.73/2.63  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.73/2.63  tff(c_10, plain, (![A_4]: (k9_relat_1(A_4, k1_relat_1(A_4))=k2_relat_1(A_4) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.73/2.63  tff(c_2098, plain, (![A_148, B_149]: (k9_relat_1(k2_funct_1(A_148), k9_relat_1(A_148, B_149))=B_149 | ~r1_tarski(B_149, k1_relat_1(A_148)) | ~v2_funct_1(A_148) | ~v1_funct_1(A_148) | ~v1_relat_1(A_148))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.73/2.63  tff(c_2119, plain, (![A_4]: (k9_relat_1(k2_funct_1(A_4), k2_relat_1(A_4))=k1_relat_1(A_4) | ~r1_tarski(k1_relat_1(A_4), k1_relat_1(A_4)) | ~v2_funct_1(A_4) | ~v1_funct_1(A_4) | ~v1_relat_1(A_4) | ~v1_relat_1(A_4))), inference(superposition, [status(thm), theory('equality')], [c_10, c_2098])).
% 7.73/2.63  tff(c_2175, plain, (![A_151]: (k9_relat_1(k2_funct_1(A_151), k2_relat_1(A_151))=k1_relat_1(A_151) | ~v2_funct_1(A_151) | ~v1_funct_1(A_151) | ~v1_relat_1(A_151))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2119])).
% 7.73/2.63  tff(c_2193, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_222, c_2175])).
% 7.73/2.63  tff(c_2209, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_226, c_224, c_2193])).
% 7.73/2.63  tff(c_2237, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2209])).
% 7.73/2.63  tff(c_2240, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_2237])).
% 7.73/2.63  tff(c_2244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_157, c_68, c_60, c_2240])).
% 7.73/2.63  tff(c_2246, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2209])).
% 7.73/2.63  tff(c_2077, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2072, c_2061])).
% 7.73/2.63  tff(c_2388, plain, (![C_158, B_159, A_160]: (v1_funct_2(k2_funct_1(C_158), B_159, A_160) | k2_relset_1(A_160, B_159, C_158)!=B_159 | ~v2_funct_1(C_158) | ~m1_subset_1(C_158, k1_zfmisc_1(k2_zfmisc_1(A_160, B_159))) | ~v1_funct_2(C_158, A_160, B_159) | ~v1_funct_1(C_158))), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.73/2.63  tff(c_2391, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2079, c_2388])).
% 7.73/2.63  tff(c_2394, plain, (v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2080, c_60, c_2077, c_2391])).
% 7.73/2.63  tff(c_2627, plain, (![C_166, B_167, A_168]: (m1_subset_1(k2_funct_1(C_166), k1_zfmisc_1(k2_zfmisc_1(B_167, A_168))) | k2_relset_1(A_168, B_167, C_166)!=B_167 | ~v2_funct_1(C_166) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_168, B_167))) | ~v1_funct_2(C_166, A_168, B_167) | ~v1_funct_1(C_166))), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.73/2.63  tff(c_4604, plain, (![B_220, A_221, C_222]: (k2_relset_1(B_220, A_221, k2_funct_1(C_222))=k2_relat_1(k2_funct_1(C_222)) | k2_relset_1(A_221, B_220, C_222)!=B_220 | ~v2_funct_1(C_222) | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1(A_221, B_220))) | ~v1_funct_2(C_222, A_221, B_220) | ~v1_funct_1(C_222))), inference(resolution, [status(thm)], [c_2627, c_34])).
% 7.73/2.63  tff(c_4610, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_relat_1(k2_funct_1('#skF_3')) | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2079, c_4604])).
% 7.73/2.63  tff(c_4614, plain, (k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2080, c_60, c_2077, c_222, c_4610])).
% 7.73/2.63  tff(c_18, plain, (![A_7]: (v2_funct_1(k2_funct_1(A_7)) | ~v2_funct_1(A_7) | ~v1_funct_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.73/2.63  tff(c_2245, plain, (~v2_funct_1(k2_funct_1('#skF_3')) | k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_2209])).
% 7.73/2.63  tff(c_2247, plain, (~v2_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2245])).
% 7.73/2.63  tff(c_2250, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_2247])).
% 7.73/2.63  tff(c_2254, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_157, c_68, c_60, c_2250])).
% 7.73/2.63  tff(c_2256, plain, (v2_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_2245])).
% 7.73/2.63  tff(c_46, plain, (![C_33, B_32, A_31]: (m1_subset_1(k2_funct_1(C_33), k1_zfmisc_1(k2_zfmisc_1(B_32, A_31))) | k2_relset_1(A_31, B_32, C_33)!=B_32 | ~v2_funct_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~v1_funct_2(C_33, A_31, B_32) | ~v1_funct_1(C_33))), inference(cnfTransformation, [status(thm)], [f_150])).
% 7.73/2.63  tff(c_16, plain, (![A_6]: (k4_relat_1(A_6)=k2_funct_1(A_6) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.73/2.63  tff(c_2259, plain, (k4_relat_1(k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2256, c_16])).
% 7.73/2.63  tff(c_2262, plain, (k4_relat_1(k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_226, c_2246, c_2259])).
% 7.73/2.63  tff(c_127, plain, (![A_49]: (k9_relat_1(A_49, k1_relat_1(A_49))=k2_relat_1(A_49) | ~v1_relat_1(A_49))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.73/2.63  tff(c_2150, plain, (![A_150]: (k9_relat_1(k4_relat_1(A_150), k2_relat_1(A_150))=k2_relat_1(k4_relat_1(A_150)) | ~v1_relat_1(k4_relat_1(A_150)) | ~v1_relat_1(A_150))), inference(superposition, [status(thm), theory('equality')], [c_14, c_127])).
% 7.73/2.63  tff(c_2162, plain, (k9_relat_1(k4_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))=k2_relat_1(k4_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k4_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_222, c_2150])).
% 7.73/2.63  tff(c_2172, plain, (k9_relat_1(k4_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))=k2_relat_1(k4_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k4_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_226, c_2162])).
% 7.73/2.63  tff(c_2210, plain, (~v1_relat_1(k4_relat_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_2172])).
% 7.73/2.63  tff(c_2213, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_8, c_2210])).
% 7.73/2.63  tff(c_2217, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_226, c_2213])).
% 7.73/2.63  tff(c_2219, plain, (v1_relat_1(k4_relat_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_2172])).
% 7.73/2.63  tff(c_2264, plain, (v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2262, c_2219])).
% 7.73/2.63  tff(c_2274, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2262, c_14])).
% 7.73/2.63  tff(c_2285, plain, (k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_226, c_222, c_2274])).
% 7.73/2.63  tff(c_2255, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_2245])).
% 7.73/2.63  tff(c_24, plain, (![A_8, B_10]: (k9_relat_1(k2_funct_1(A_8), k9_relat_1(A_8, B_10))=B_10 | ~r1_tarski(B_10, k1_relat_1(A_8)) | ~v2_funct_1(A_8) | ~v1_funct_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.73/2.63  tff(c_2345, plain, (k9_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))), k2_relat_1('#skF_3'))=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2255, c_24])).
% 7.73/2.63  tff(c_2352, plain, (k9_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))), k2_relat_1('#skF_3'))=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2264, c_6, c_2285, c_2345])).
% 7.73/2.63  tff(c_2463, plain, (~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_2352])).
% 7.73/2.63  tff(c_2466, plain, (~v1_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26, c_2463])).
% 7.73/2.63  tff(c_2472, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_157, c_68, c_60, c_68, c_2466])).
% 7.73/2.63  tff(c_2474, plain, (v1_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_2352])).
% 7.73/2.63  tff(c_2271, plain, (k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2262, c_12])).
% 7.73/2.63  tff(c_2283, plain, (k2_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_226, c_224, c_2271])).
% 7.73/2.63  tff(c_2218, plain, (k9_relat_1(k4_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))=k2_relat_1(k4_relat_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_2172])).
% 7.73/2.63  tff(c_2231, plain, (k9_relat_1(k2_funct_1(k4_relat_1(k2_funct_1('#skF_3'))), k2_relat_1(k4_relat_1(k2_funct_1('#skF_3'))))=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(k4_relat_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k4_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k4_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k4_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_2218, c_24])).
% 7.73/2.63  tff(c_2235, plain, (k9_relat_1(k2_funct_1(k4_relat_1(k2_funct_1('#skF_3'))), k2_relat_1(k4_relat_1(k2_funct_1('#skF_3'))))=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(k4_relat_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k4_relat_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k4_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2219, c_2231])).
% 7.73/2.63  tff(c_2493, plain, (k9_relat_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))), k2_relat_1('#skF_3'))=k1_relat_1('#skF_3') | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2474, c_2262, c_2262, c_6, c_2285, c_2262, c_2283, c_2262, c_2262, c_2235])).
% 7.73/2.63  tff(c_2494, plain, (~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_2493])).
% 7.73/2.63  tff(c_2497, plain, (~v2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26, c_2494])).
% 7.73/2.63  tff(c_2503, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_157, c_68, c_60, c_60, c_2497])).
% 7.73/2.63  tff(c_2505, plain, (v2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_2493])).
% 7.73/2.63  tff(c_2508, plain, (k4_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_2505, c_16])).
% 7.73/2.63  tff(c_2514, plain, (k4_relat_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2264, c_2474, c_2508])).
% 7.73/2.63  tff(c_2542, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k4_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26, c_2514])).
% 7.73/2.63  tff(c_2560, plain, (k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_157, c_68, c_60, c_208, c_2542])).
% 7.73/2.63  tff(c_6503, plain, (![A_252, B_253, A_254]: (m1_subset_1(A_252, k1_zfmisc_1(k2_zfmisc_1(B_253, A_254))) | k2_relset_1(A_254, B_253, k2_funct_1(A_252))!=B_253 | ~v2_funct_1(k2_funct_1(A_252)) | ~m1_subset_1(k2_funct_1(A_252), k1_zfmisc_1(k2_zfmisc_1(A_254, B_253))) | ~v1_funct_2(k2_funct_1(A_252), A_254, B_253) | ~v1_funct_1(k2_funct_1(A_252)) | ~v2_funct_1(A_252) | ~v1_funct_1(A_252) | ~v1_relat_1(A_252))), inference(superposition, [status(thm), theory('equality')], [c_26, c_2627])).
% 7.73/2.63  tff(c_6512, plain, (![B_253, A_254]: (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(B_253, A_254))) | k2_relset_1(A_254, B_253, k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))))!=B_253 | ~v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(A_254, B_253))) | ~v1_funct_2(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))), A_254, B_253) | ~v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1('#skF_3')))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_2560, c_6503])).
% 7.73/2.63  tff(c_6519, plain, (![B_255, A_256]: (m1_subset_1(k2_funct_1(k2_funct_1('#skF_3')), k1_zfmisc_1(k2_zfmisc_1(B_255, A_256))) | k2_relset_1(A_256, B_255, k2_funct_1('#skF_3'))!=B_255 | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(A_256, B_255))) | ~v1_funct_2(k2_funct_1('#skF_3'), A_256, B_255))), inference(demodulation, [status(thm), theory('equality')], [c_2264, c_2474, c_2505, c_2246, c_2560, c_2560, c_2256, c_2560, c_2560, c_6512])).
% 7.73/2.63  tff(c_2811, plain, (![C_173]: (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), C_173, C_173) | ~m1_subset_1(C_173, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2(C_173, k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(C_173))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2080, c_2807])).
% 7.73/2.63  tff(c_6546, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_3'))) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3')))) | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_6519, c_2811])).
% 7.73/2.63  tff(c_6602, plain, (r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), k2_funct_1(k2_funct_1('#skF_3'))) | ~v1_funct_2(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_2394, c_4614, c_2474, c_6546])).
% 7.73/2.63  tff(c_6642, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(splitLeft, [status(thm)], [c_6602])).
% 7.73/2.63  tff(c_6645, plain, (k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3')))) | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_6642])).
% 7.73/2.63  tff(c_6649, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_2080, c_2079, c_60, c_2077, c_6645])).
% 7.73/2.63  tff(c_6651, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'))))), inference(splitRight, [status(thm)], [c_6602])).
% 7.73/2.63  tff(c_56, plain, (![A_36, B_37, C_38]: (k2_tops_2(A_36, B_37, C_38)=k2_funct_1(C_38) | ~v2_funct_1(C_38) | k2_relset_1(A_36, B_37, C_38)!=B_37 | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_2(C_38, A_36, B_37) | ~v1_funct_1(C_38))), inference(cnfTransformation, [status(thm)], [f_174])).
% 7.73/2.63  tff(c_6684, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1(k2_funct_1('#skF_3')) | k2_relset_1(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_2(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_6651, c_56])).
% 7.73/2.63  tff(c_6742, plain, (k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3'))=k2_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2246, c_2394, c_4614, c_2256, c_6684])).
% 7.73/2.63  tff(c_2475, plain, (![A_163, B_164, C_165]: (k2_tops_2(A_163, B_164, C_165)=k2_funct_1(C_165) | ~v2_funct_1(C_165) | k2_relset_1(A_163, B_164, C_165)!=B_164 | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_163, B_164))) | ~v1_funct_2(C_165, A_163, B_164) | ~v1_funct_1(C_165))), inference(cnfTransformation, [status(thm)], [f_174])).
% 7.73/2.63  tff(c_2478, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3') | ~v2_funct_1('#skF_3') | k2_relset_1(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2079, c_2475])).
% 7.73/2.63  tff(c_2481, plain, (k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2080, c_2077, c_60, c_2478])).
% 7.73/2.63  tff(c_58, plain, (~r2_funct_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), k2_tops_2(u1_struct_0('#skF_2'), u1_struct_0('#skF_1'), k2_tops_2(u1_struct_0('#skF_1'), u1_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_196])).
% 7.73/2.63  tff(c_166, plain, (~r2_funct_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k2_struct_0('#skF_1'), k2_tops_2(k2_struct_0('#skF_1'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_86, c_86, c_85, c_85, c_85, c_58])).
% 7.73/2.63  tff(c_2015, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), k2_tops_2(k2_struct_0('#skF_2'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_struct_0('#skF_2'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2012, c_2012, c_2012, c_166])).
% 7.73/2.63  tff(c_2078, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_tops_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2072, c_2072, c_2072, c_2015])).
% 7.73/2.63  tff(c_2487, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_tops_2(k2_relat_1('#skF_3'), k1_relat_1('#skF_3'), k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2481, c_2078])).
% 7.73/2.63  tff(c_6804, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), k2_funct_1(k2_funct_1('#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_6742, c_2487])).
% 7.73/2.63  tff(c_6811, plain, (~r2_funct_2(k1_relat_1('#skF_3'), k2_relat_1('#skF_3'), '#skF_3', '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_26, c_6804])).
% 7.73/2.63  tff(c_6814, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_157, c_68, c_60, c_2873, c_6811])).
% 7.73/2.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.73/2.63  
% 7.73/2.63  Inference rules
% 7.73/2.63  ----------------------
% 7.73/2.63  #Ref     : 0
% 7.73/2.63  #Sup     : 1551
% 7.73/2.63  #Fact    : 0
% 7.73/2.63  #Define  : 0
% 7.73/2.63  #Split   : 18
% 7.73/2.63  #Chain   : 0
% 7.73/2.63  #Close   : 0
% 7.73/2.63  
% 7.73/2.63  Ordering : KBO
% 7.73/2.63  
% 7.73/2.63  Simplification rules
% 7.73/2.63  ----------------------
% 7.73/2.63  #Subsume      : 166
% 7.73/2.63  #Demod        : 5238
% 7.73/2.63  #Tautology    : 799
% 7.73/2.63  #SimpNegUnit  : 13
% 7.73/2.63  #BackRed      : 57
% 7.73/2.63  
% 7.73/2.63  #Partial instantiations: 0
% 7.73/2.63  #Strategies tried      : 1
% 7.73/2.63  
% 7.73/2.63  Timing (in seconds)
% 7.73/2.63  ----------------------
% 7.73/2.63  Preprocessing        : 0.37
% 7.73/2.63  Parsing              : 0.20
% 7.73/2.63  CNF conversion       : 0.03
% 7.73/2.63  Main loop            : 1.46
% 7.73/2.63  Inferencing          : 0.47
% 7.73/2.63  Reduction            : 0.56
% 7.73/2.63  Demodulation         : 0.44
% 7.73/2.63  BG Simplification    : 0.06
% 7.73/2.63  Subsumption          : 0.28
% 7.73/2.63  Abstraction          : 0.07
% 7.73/2.63  MUC search           : 0.00
% 7.73/2.63  Cooper               : 0.00
% 7.73/2.63  Total                : 1.89
% 7.73/2.63  Index Insertion      : 0.00
% 7.73/2.63  Index Deletion       : 0.00
% 7.73/2.63  Index Matching       : 0.00
% 7.73/2.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
