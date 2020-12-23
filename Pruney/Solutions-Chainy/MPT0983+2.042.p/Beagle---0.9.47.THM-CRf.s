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
% DateTime   : Thu Dec  3 10:12:06 EST 2020

% Result     : Theorem 6.41s
% Output     : CNFRefutation 6.41s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 279 expanded)
%              Number of leaves         :   49 ( 117 expanded)
%              Depth                    :   10
%              Number of atoms          :  248 ( 681 expanded)
%              Number of equality atoms :   37 (  84 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_175,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
             => ( v2_funct_1(C)
                & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_116,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_114,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_94,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_155,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_54,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_133,axiom,(
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

tff(f_102,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_60,plain,
    ( ~ v2_funct_2('#skF_5','#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_135,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_298,plain,(
    ! [C_91,A_92,B_93] :
      ( v1_xboole_0(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93)))
      | ~ v1_xboole_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_313,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_298])).

tff(c_316,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_313])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_72,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_68,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_66,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_52,plain,(
    ! [A_42] : k6_relat_1(A_42) = k6_partfun1(A_42) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_24,plain,(
    ! [A_13] : v2_funct_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_76,plain,(
    ! [A_13] : v2_funct_1(k6_partfun1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_24])).

tff(c_1046,plain,(
    ! [D_177,B_178,A_176,E_180,F_175,C_179] :
      ( m1_subset_1(k1_partfun1(A_176,B_178,C_179,D_177,E_180,F_175),k1_zfmisc_1(k2_zfmisc_1(A_176,D_177)))
      | ~ m1_subset_1(F_175,k1_zfmisc_1(k2_zfmisc_1(C_179,D_177)))
      | ~ v1_funct_1(F_175)
      | ~ m1_subset_1(E_180,k1_zfmisc_1(k2_zfmisc_1(A_176,B_178)))
      | ~ v1_funct_1(E_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_42,plain,(
    ! [A_33] : m1_subset_1(k6_relat_1(A_33),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33))) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_75,plain,(
    ! [A_33] : m1_subset_1(k6_partfun1(A_33),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_42])).

tff(c_62,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_757,plain,(
    ! [D_144,C_145,A_146,B_147] :
      ( D_144 = C_145
      | ~ r2_relset_1(A_146,B_147,C_145,D_144)
      | ~ m1_subset_1(D_144,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147)))
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_765,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_62,c_757])).

tff(c_780,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_765])).

tff(c_813,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_780])).

tff(c_1052,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1046,c_813])).

tff(c_1078,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_68,c_64,c_1052])).

tff(c_1079,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_780])).

tff(c_2234,plain,(
    ! [B_237,E_235,C_239,D_236,A_238] :
      ( k1_xboole_0 = C_239
      | v2_funct_1(D_236)
      | ~ v2_funct_1(k1_partfun1(A_238,B_237,B_237,C_239,D_236,E_235))
      | ~ m1_subset_1(E_235,k1_zfmisc_1(k2_zfmisc_1(B_237,C_239)))
      | ~ v1_funct_2(E_235,B_237,C_239)
      | ~ v1_funct_1(E_235)
      | ~ m1_subset_1(D_236,k1_zfmisc_1(k2_zfmisc_1(A_238,B_237)))
      | ~ v1_funct_2(D_236,A_238,B_237)
      | ~ v1_funct_1(D_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_2236,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1079,c_2234])).

tff(c_2238,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_68,c_66,c_64,c_76,c_2236])).

tff(c_2239,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_2238])).

tff(c_8,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_198,plain,(
    ! [C_77,B_78,A_79] :
      ( v5_relat_1(C_77,B_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_79,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_215,plain,(
    ! [B_78] : v5_relat_1(k1_xboole_0,B_78) ),
    inference(resolution,[status(thm)],[c_8,c_198])).

tff(c_106,plain,(
    ! [A_61] : k6_relat_1(A_61) = k6_partfun1(A_61) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_20,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_112,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_20])).

tff(c_22,plain,(
    ! [A_13] : v1_relat_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_77,plain,(
    ! [A_13] : v1_relat_1(k6_partfun1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_22])).

tff(c_129,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_77])).

tff(c_18,plain,(
    ! [A_12] : k2_relat_1(k6_relat_1(A_12)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_78,plain,(
    ! [A_12] : k2_relat_1(k6_partfun1(A_12)) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_18])).

tff(c_124,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_78])).

tff(c_216,plain,(
    ! [B_80,A_81] :
      ( r1_tarski(k2_relat_1(B_80),A_81)
      | ~ v5_relat_1(B_80,A_81)
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_226,plain,(
    ! [A_81] :
      ( r1_tarski(k1_xboole_0,A_81)
      | ~ v5_relat_1(k1_xboole_0,A_81)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_216])).

tff(c_233,plain,(
    ! [A_81] :
      ( r1_tarski(k1_xboole_0,A_81)
      | ~ v5_relat_1(k1_xboole_0,A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_226])).

tff(c_431,plain,(
    ! [A_110] : r1_tarski(k1_xboole_0,A_110) ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_233])).

tff(c_315,plain,(
    ! [A_92] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(A_92) ) ),
    inference(resolution,[status(thm)],[c_8,c_298])).

tff(c_318,plain,(
    ! [A_92] : ~ v1_xboole_0(A_92) ),
    inference(splitLeft,[status(thm)],[c_315])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_151,plain,(
    ! [B_65,A_66] :
      ( ~ r1_tarski(B_65,A_66)
      | ~ r2_hidden(A_66,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_155,plain,(
    ! [A_1] :
      ( ~ r1_tarski(A_1,'#skF_1'(A_1))
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_151])).

tff(c_333,plain,(
    ! [A_1] : ~ r1_tarski(A_1,'#skF_1'(A_1)) ),
    inference(negUnitSimplification,[status(thm)],[c_318,c_155])).

tff(c_436,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_431,c_333])).

tff(c_437,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_315])).

tff(c_2258,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2239,c_437])).

tff(c_2271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_316,c_2258])).

tff(c_2272,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_313])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2277,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2272,c_6])).

tff(c_131,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_76])).

tff(c_2288,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2277,c_131])).

tff(c_2295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_2288])).

tff(c_2296,plain,(
    ~ v2_funct_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_2324,plain,(
    ! [C_247,A_248,B_249] :
      ( v1_relat_1(C_247)
      | ~ m1_subset_1(C_247,k1_zfmisc_1(k2_zfmisc_1(A_248,B_249))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2341,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_2324])).

tff(c_2659,plain,(
    ! [A_289,B_290,D_291] :
      ( r2_relset_1(A_289,B_290,D_291,D_291)
      | ~ m1_subset_1(D_291,k1_zfmisc_1(k2_zfmisc_1(A_289,B_290))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2669,plain,(
    ! [A_33] : r2_relset_1(A_33,A_33,k6_partfun1(A_33),k6_partfun1(A_33)) ),
    inference(resolution,[status(thm)],[c_75,c_2659])).

tff(c_2753,plain,(
    ! [A_300,B_301,C_302] :
      ( k2_relset_1(A_300,B_301,C_302) = k2_relat_1(C_302)
      | ~ m1_subset_1(C_302,k1_zfmisc_1(k2_zfmisc_1(A_300,B_301))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2770,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_2753])).

tff(c_48,plain,(
    ! [F_41,D_39,A_36,E_40,C_38,B_37] :
      ( m1_subset_1(k1_partfun1(A_36,B_37,C_38,D_39,E_40,F_41),k1_zfmisc_1(k2_zfmisc_1(A_36,D_39)))
      | ~ m1_subset_1(F_41,k1_zfmisc_1(k2_zfmisc_1(C_38,D_39)))
      | ~ v1_funct_1(F_41)
      | ~ m1_subset_1(E_40,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_funct_1(E_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_2892,plain,(
    ! [D_312,C_313,A_314,B_315] :
      ( D_312 = C_313
      | ~ r2_relset_1(A_314,B_315,C_313,D_312)
      | ~ m1_subset_1(D_312,k1_zfmisc_1(k2_zfmisc_1(A_314,B_315)))
      | ~ m1_subset_1(C_313,k1_zfmisc_1(k2_zfmisc_1(A_314,B_315))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2902,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_62,c_2892])).

tff(c_2921,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_2902])).

tff(c_3013,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2921])).

tff(c_3979,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_3013])).

tff(c_3983,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_68,c_64,c_3979])).

tff(c_3984,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2921])).

tff(c_7074,plain,(
    ! [A_444,B_445,C_446,D_447] :
      ( k2_relset_1(A_444,B_445,C_446) = B_445
      | ~ r2_relset_1(B_445,B_445,k1_partfun1(B_445,A_444,A_444,B_445,D_447,C_446),k6_partfun1(B_445))
      | ~ m1_subset_1(D_447,k1_zfmisc_1(k2_zfmisc_1(B_445,A_444)))
      | ~ v1_funct_2(D_447,B_445,A_444)
      | ~ v1_funct_1(D_447)
      | ~ m1_subset_1(C_446,k1_zfmisc_1(k2_zfmisc_1(A_444,B_445)))
      | ~ v1_funct_2(C_446,A_444,B_445)
      | ~ v1_funct_1(C_446) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_7095,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3984,c_7074])).

tff(c_7103,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_74,c_72,c_70,c_2669,c_2770,c_7095])).

tff(c_2344,plain,(
    ! [C_250,B_251,A_252] :
      ( v5_relat_1(C_250,B_251)
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(A_252,B_251))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2358,plain,(
    ! [A_33] : v5_relat_1(k6_partfun1(A_33),A_33) ),
    inference(resolution,[status(thm)],[c_75,c_2344])).

tff(c_2403,plain,(
    ! [B_263,A_264] :
      ( r1_tarski(k2_relat_1(B_263),A_264)
      | ~ v5_relat_1(B_263,A_264)
      | ~ v1_relat_1(B_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2416,plain,(
    ! [A_12,A_264] :
      ( r1_tarski(A_12,A_264)
      | ~ v5_relat_1(k6_partfun1(A_12),A_264)
      | ~ v1_relat_1(k6_partfun1(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_2403])).

tff(c_2439,plain,(
    ! [A_267,A_268] :
      ( r1_tarski(A_267,A_268)
      | ~ v5_relat_1(k6_partfun1(A_267),A_268) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_2416])).

tff(c_2453,plain,(
    ! [A_269] : r1_tarski(A_269,A_269) ),
    inference(resolution,[status(thm)],[c_2358,c_2439])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( v5_relat_1(B_11,A_10)
      | ~ r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2458,plain,(
    ! [B_11] :
      ( v5_relat_1(B_11,k2_relat_1(B_11))
      | ~ v1_relat_1(B_11) ) ),
    inference(resolution,[status(thm)],[c_2453,c_12])).

tff(c_2505,plain,(
    ! [B_280] :
      ( v2_funct_2(B_280,k2_relat_1(B_280))
      | ~ v5_relat_1(B_280,k2_relat_1(B_280))
      | ~ v1_relat_1(B_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2523,plain,(
    ! [B_11] :
      ( v2_funct_2(B_11,k2_relat_1(B_11))
      | ~ v1_relat_1(B_11) ) ),
    inference(resolution,[status(thm)],[c_2458,c_2505])).

tff(c_7111,plain,
    ( v2_funct_2('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7103,c_2523])).

tff(c_7127,plain,(
    v2_funct_2('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2341,c_7111])).

tff(c_7129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2296,c_7127])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:35:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.41/2.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.41/2.43  
% 6.41/2.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.41/2.43  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 6.41/2.43  
% 6.41/2.43  %Foreground sorts:
% 6.41/2.43  
% 6.41/2.43  
% 6.41/2.43  %Background operators:
% 6.41/2.43  
% 6.41/2.43  
% 6.41/2.43  %Foreground operators:
% 6.41/2.43  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.41/2.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.41/2.43  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.41/2.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.41/2.43  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.41/2.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.41/2.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.41/2.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.41/2.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.41/2.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.41/2.43  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.41/2.43  tff('#skF_5', type, '#skF_5': $i).
% 6.41/2.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.41/2.43  tff('#skF_2', type, '#skF_2': $i).
% 6.41/2.43  tff('#skF_3', type, '#skF_3': $i).
% 6.41/2.43  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.41/2.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.41/2.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.41/2.43  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.41/2.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.41/2.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.41/2.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.41/2.43  tff('#skF_4', type, '#skF_4': $i).
% 6.41/2.43  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.41/2.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.41/2.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.41/2.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.41/2.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.41/2.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.41/2.43  
% 6.41/2.45  tff(f_175, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 6.41/2.45  tff(f_80, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 6.41/2.45  tff(f_116, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.41/2.45  tff(f_58, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 6.41/2.45  tff(f_114, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.41/2.45  tff(f_94, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 6.41/2.45  tff(f_92, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.41/2.45  tff(f_155, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 6.41/2.45  tff(f_37, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 6.41/2.45  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.41/2.45  tff(f_54, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 6.41/2.45  tff(f_53, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 6.41/2.45  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 6.41/2.45  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.41/2.45  tff(f_63, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.41/2.45  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 6.41/2.45  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.41/2.45  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.41/2.45  tff(f_133, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 6.41/2.45  tff(f_102, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 6.41/2.45  tff(c_60, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_175])).
% 6.41/2.45  tff(c_135, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_60])).
% 6.41/2.45  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 6.41/2.45  tff(c_298, plain, (![C_91, A_92, B_93]: (v1_xboole_0(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))) | ~v1_xboole_0(A_92))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.41/2.45  tff(c_313, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_70, c_298])).
% 6.41/2.45  tff(c_316, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_313])).
% 6.41/2.45  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_175])).
% 6.41/2.45  tff(c_72, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_175])).
% 6.41/2.45  tff(c_68, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_175])).
% 6.41/2.45  tff(c_66, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_175])).
% 6.41/2.45  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 6.41/2.45  tff(c_52, plain, (![A_42]: (k6_relat_1(A_42)=k6_partfun1(A_42))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.41/2.45  tff(c_24, plain, (![A_13]: (v2_funct_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.41/2.45  tff(c_76, plain, (![A_13]: (v2_funct_1(k6_partfun1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_24])).
% 6.41/2.45  tff(c_1046, plain, (![D_177, B_178, A_176, E_180, F_175, C_179]: (m1_subset_1(k1_partfun1(A_176, B_178, C_179, D_177, E_180, F_175), k1_zfmisc_1(k2_zfmisc_1(A_176, D_177))) | ~m1_subset_1(F_175, k1_zfmisc_1(k2_zfmisc_1(C_179, D_177))) | ~v1_funct_1(F_175) | ~m1_subset_1(E_180, k1_zfmisc_1(k2_zfmisc_1(A_176, B_178))) | ~v1_funct_1(E_180))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.41/2.45  tff(c_42, plain, (![A_33]: (m1_subset_1(k6_relat_1(A_33), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.41/2.45  tff(c_75, plain, (![A_33]: (m1_subset_1(k6_partfun1(A_33), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_42])).
% 6.41/2.45  tff(c_62, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_175])).
% 6.41/2.45  tff(c_757, plain, (![D_144, C_145, A_146, B_147]: (D_144=C_145 | ~r2_relset_1(A_146, B_147, C_145, D_144) | ~m1_subset_1(D_144, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.41/2.45  tff(c_765, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_62, c_757])).
% 6.41/2.45  tff(c_780, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_765])).
% 6.41/2.45  tff(c_813, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_780])).
% 6.41/2.45  tff(c_1052, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_1046, c_813])).
% 6.41/2.45  tff(c_1078, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_68, c_64, c_1052])).
% 6.41/2.45  tff(c_1079, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_780])).
% 6.41/2.45  tff(c_2234, plain, (![B_237, E_235, C_239, D_236, A_238]: (k1_xboole_0=C_239 | v2_funct_1(D_236) | ~v2_funct_1(k1_partfun1(A_238, B_237, B_237, C_239, D_236, E_235)) | ~m1_subset_1(E_235, k1_zfmisc_1(k2_zfmisc_1(B_237, C_239))) | ~v1_funct_2(E_235, B_237, C_239) | ~v1_funct_1(E_235) | ~m1_subset_1(D_236, k1_zfmisc_1(k2_zfmisc_1(A_238, B_237))) | ~v1_funct_2(D_236, A_238, B_237) | ~v1_funct_1(D_236))), inference(cnfTransformation, [status(thm)], [f_155])).
% 6.41/2.45  tff(c_2236, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1079, c_2234])).
% 6.41/2.45  tff(c_2238, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_68, c_66, c_64, c_76, c_2236])).
% 6.41/2.45  tff(c_2239, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_135, c_2238])).
% 6.41/2.45  tff(c_8, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.41/2.45  tff(c_198, plain, (![C_77, B_78, A_79]: (v5_relat_1(C_77, B_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_79, B_78))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.41/2.45  tff(c_215, plain, (![B_78]: (v5_relat_1(k1_xboole_0, B_78))), inference(resolution, [status(thm)], [c_8, c_198])).
% 6.41/2.45  tff(c_106, plain, (![A_61]: (k6_relat_1(A_61)=k6_partfun1(A_61))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.41/2.45  tff(c_20, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.41/2.45  tff(c_112, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_106, c_20])).
% 6.41/2.45  tff(c_22, plain, (![A_13]: (v1_relat_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.41/2.45  tff(c_77, plain, (![A_13]: (v1_relat_1(k6_partfun1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_22])).
% 6.41/2.45  tff(c_129, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_112, c_77])).
% 6.41/2.45  tff(c_18, plain, (![A_12]: (k2_relat_1(k6_relat_1(A_12))=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.41/2.45  tff(c_78, plain, (![A_12]: (k2_relat_1(k6_partfun1(A_12))=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_18])).
% 6.41/2.45  tff(c_124, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_112, c_78])).
% 6.41/2.45  tff(c_216, plain, (![B_80, A_81]: (r1_tarski(k2_relat_1(B_80), A_81) | ~v5_relat_1(B_80, A_81) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.41/2.45  tff(c_226, plain, (![A_81]: (r1_tarski(k1_xboole_0, A_81) | ~v5_relat_1(k1_xboole_0, A_81) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_124, c_216])).
% 6.41/2.45  tff(c_233, plain, (![A_81]: (r1_tarski(k1_xboole_0, A_81) | ~v5_relat_1(k1_xboole_0, A_81))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_226])).
% 6.41/2.45  tff(c_431, plain, (![A_110]: (r1_tarski(k1_xboole_0, A_110))), inference(demodulation, [status(thm), theory('equality')], [c_215, c_233])).
% 6.41/2.45  tff(c_315, plain, (![A_92]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(A_92))), inference(resolution, [status(thm)], [c_8, c_298])).
% 6.41/2.45  tff(c_318, plain, (![A_92]: (~v1_xboole_0(A_92))), inference(splitLeft, [status(thm)], [c_315])).
% 6.41/2.45  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.41/2.45  tff(c_151, plain, (![B_65, A_66]: (~r1_tarski(B_65, A_66) | ~r2_hidden(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.41/2.45  tff(c_155, plain, (![A_1]: (~r1_tarski(A_1, '#skF_1'(A_1)) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_151])).
% 6.41/2.45  tff(c_333, plain, (![A_1]: (~r1_tarski(A_1, '#skF_1'(A_1)))), inference(negUnitSimplification, [status(thm)], [c_318, c_155])).
% 6.41/2.45  tff(c_436, plain, $false, inference(resolution, [status(thm)], [c_431, c_333])).
% 6.41/2.45  tff(c_437, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_315])).
% 6.41/2.45  tff(c_2258, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2239, c_437])).
% 6.41/2.45  tff(c_2271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_316, c_2258])).
% 6.41/2.45  tff(c_2272, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_313])).
% 6.41/2.45  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.41/2.45  tff(c_2277, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_2272, c_6])).
% 6.41/2.45  tff(c_131, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_112, c_76])).
% 6.41/2.45  tff(c_2288, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2277, c_131])).
% 6.41/2.45  tff(c_2295, plain, $false, inference(negUnitSimplification, [status(thm)], [c_135, c_2288])).
% 6.41/2.45  tff(c_2296, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_60])).
% 6.41/2.45  tff(c_2324, plain, (![C_247, A_248, B_249]: (v1_relat_1(C_247) | ~m1_subset_1(C_247, k1_zfmisc_1(k2_zfmisc_1(A_248, B_249))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.41/2.45  tff(c_2341, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_2324])).
% 6.41/2.45  tff(c_2659, plain, (![A_289, B_290, D_291]: (r2_relset_1(A_289, B_290, D_291, D_291) | ~m1_subset_1(D_291, k1_zfmisc_1(k2_zfmisc_1(A_289, B_290))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.41/2.45  tff(c_2669, plain, (![A_33]: (r2_relset_1(A_33, A_33, k6_partfun1(A_33), k6_partfun1(A_33)))), inference(resolution, [status(thm)], [c_75, c_2659])).
% 6.41/2.45  tff(c_2753, plain, (![A_300, B_301, C_302]: (k2_relset_1(A_300, B_301, C_302)=k2_relat_1(C_302) | ~m1_subset_1(C_302, k1_zfmisc_1(k2_zfmisc_1(A_300, B_301))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.41/2.45  tff(c_2770, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_2753])).
% 6.41/2.45  tff(c_48, plain, (![F_41, D_39, A_36, E_40, C_38, B_37]: (m1_subset_1(k1_partfun1(A_36, B_37, C_38, D_39, E_40, F_41), k1_zfmisc_1(k2_zfmisc_1(A_36, D_39))) | ~m1_subset_1(F_41, k1_zfmisc_1(k2_zfmisc_1(C_38, D_39))) | ~v1_funct_1(F_41) | ~m1_subset_1(E_40, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_1(E_40))), inference(cnfTransformation, [status(thm)], [f_114])).
% 6.41/2.45  tff(c_2892, plain, (![D_312, C_313, A_314, B_315]: (D_312=C_313 | ~r2_relset_1(A_314, B_315, C_313, D_312) | ~m1_subset_1(D_312, k1_zfmisc_1(k2_zfmisc_1(A_314, B_315))) | ~m1_subset_1(C_313, k1_zfmisc_1(k2_zfmisc_1(A_314, B_315))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.41/2.45  tff(c_2902, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_62, c_2892])).
% 6.41/2.45  tff(c_2921, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_2902])).
% 6.41/2.45  tff(c_3013, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_2921])).
% 6.41/2.45  tff(c_3979, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_3013])).
% 6.41/2.45  tff(c_3983, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_68, c_64, c_3979])).
% 6.41/2.45  tff(c_3984, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_2921])).
% 6.41/2.45  tff(c_7074, plain, (![A_444, B_445, C_446, D_447]: (k2_relset_1(A_444, B_445, C_446)=B_445 | ~r2_relset_1(B_445, B_445, k1_partfun1(B_445, A_444, A_444, B_445, D_447, C_446), k6_partfun1(B_445)) | ~m1_subset_1(D_447, k1_zfmisc_1(k2_zfmisc_1(B_445, A_444))) | ~v1_funct_2(D_447, B_445, A_444) | ~v1_funct_1(D_447) | ~m1_subset_1(C_446, k1_zfmisc_1(k2_zfmisc_1(A_444, B_445))) | ~v1_funct_2(C_446, A_444, B_445) | ~v1_funct_1(C_446))), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.41/2.45  tff(c_7095, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3984, c_7074])).
% 6.41/2.45  tff(c_7103, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_74, c_72, c_70, c_2669, c_2770, c_7095])).
% 6.41/2.45  tff(c_2344, plain, (![C_250, B_251, A_252]: (v5_relat_1(C_250, B_251) | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(A_252, B_251))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.41/2.45  tff(c_2358, plain, (![A_33]: (v5_relat_1(k6_partfun1(A_33), A_33))), inference(resolution, [status(thm)], [c_75, c_2344])).
% 6.41/2.45  tff(c_2403, plain, (![B_263, A_264]: (r1_tarski(k2_relat_1(B_263), A_264) | ~v5_relat_1(B_263, A_264) | ~v1_relat_1(B_263))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.41/2.45  tff(c_2416, plain, (![A_12, A_264]: (r1_tarski(A_12, A_264) | ~v5_relat_1(k6_partfun1(A_12), A_264) | ~v1_relat_1(k6_partfun1(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_78, c_2403])).
% 6.41/2.45  tff(c_2439, plain, (![A_267, A_268]: (r1_tarski(A_267, A_268) | ~v5_relat_1(k6_partfun1(A_267), A_268))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_2416])).
% 6.41/2.45  tff(c_2453, plain, (![A_269]: (r1_tarski(A_269, A_269))), inference(resolution, [status(thm)], [c_2358, c_2439])).
% 6.41/2.45  tff(c_12, plain, (![B_11, A_10]: (v5_relat_1(B_11, A_10) | ~r1_tarski(k2_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.41/2.45  tff(c_2458, plain, (![B_11]: (v5_relat_1(B_11, k2_relat_1(B_11)) | ~v1_relat_1(B_11))), inference(resolution, [status(thm)], [c_2453, c_12])).
% 6.41/2.45  tff(c_2505, plain, (![B_280]: (v2_funct_2(B_280, k2_relat_1(B_280)) | ~v5_relat_1(B_280, k2_relat_1(B_280)) | ~v1_relat_1(B_280))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.41/2.45  tff(c_2523, plain, (![B_11]: (v2_funct_2(B_11, k2_relat_1(B_11)) | ~v1_relat_1(B_11))), inference(resolution, [status(thm)], [c_2458, c_2505])).
% 6.41/2.45  tff(c_7111, plain, (v2_funct_2('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7103, c_2523])).
% 6.41/2.45  tff(c_7127, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2341, c_7111])).
% 6.41/2.45  tff(c_7129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2296, c_7127])).
% 6.41/2.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.41/2.45  
% 6.41/2.45  Inference rules
% 6.41/2.45  ----------------------
% 6.41/2.45  #Ref     : 0
% 6.41/2.45  #Sup     : 1836
% 6.41/2.45  #Fact    : 0
% 6.41/2.45  #Define  : 0
% 6.41/2.45  #Split   : 21
% 6.41/2.45  #Chain   : 0
% 6.41/2.45  #Close   : 0
% 6.41/2.45  
% 6.41/2.45  Ordering : KBO
% 6.41/2.45  
% 6.41/2.45  Simplification rules
% 6.41/2.45  ----------------------
% 6.41/2.46  #Subsume      : 525
% 6.41/2.46  #Demod        : 1239
% 6.41/2.46  #Tautology    : 548
% 6.41/2.46  #SimpNegUnit  : 9
% 6.41/2.46  #BackRed      : 46
% 6.41/2.46  
% 6.41/2.46  #Partial instantiations: 0
% 6.41/2.46  #Strategies tried      : 1
% 6.41/2.46  
% 6.41/2.46  Timing (in seconds)
% 6.41/2.46  ----------------------
% 6.77/2.46  Preprocessing        : 0.37
% 6.77/2.46  Parsing              : 0.21
% 6.77/2.46  CNF conversion       : 0.02
% 6.77/2.46  Main loop            : 1.21
% 6.77/2.46  Inferencing          : 0.39
% 6.77/2.46  Reduction            : 0.44
% 6.77/2.46  Demodulation         : 0.33
% 6.77/2.46  BG Simplification    : 0.05
% 6.77/2.46  Subsumption          : 0.26
% 6.77/2.46  Abstraction          : 0.05
% 6.77/2.46  MUC search           : 0.00
% 6.77/2.46  Cooper               : 0.00
% 6.77/2.46  Total                : 1.64
% 6.77/2.46  Index Insertion      : 0.00
% 6.77/2.46  Index Deletion       : 0.00
% 6.77/2.46  Index Matching       : 0.00
% 6.77/2.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
